#!/usr/bin/env python3
"""
Stella Soup Visualization Server
=================================
Bridges the C soup engine (soup_2d_viz) to the browser.

Architecture:
  soup_2d_viz (C, full speed) → stdout → this server → SSE → browser

Usage:
  python3 viz_server.py                    # default: n_sub=8, port=8765
  python3 viz_server.py --n-sub 12         # more sites
  python3 viz_server.py --port 9000        # different port
  python3 viz_server.py --snap-interval 200  # faster snapshots

The server:
  1. Compiles soup_2d_viz.c if needed
  2. Spawns the C process
  3. Reads binary frames from its stdout
  4. Serves the HTML viewer on http://localhost:8765
  5. Streams frames to the browser via Server-Sent Events (SSE)
  6. Forwards control commands (pause, speed) from browser to C process
"""

import argparse
import base64
import http.server
import json
import os
import struct
import subprocess
import sys
import threading
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
C_SOURCE = SCRIPT_DIR / "soup_tile_viz.c"
C_BINARY = SCRIPT_DIR / "soup_tile_viz"
HTML_FILE = SCRIPT_DIR / "viz_soup_live.html"

FRAME_MAGIC = 0x53565A31
MESH_MAGIC = 0x4D455348
TILE_MAGIC = 0x54494C45

# Shared state
latest_frame = None
mesh_data = None
tile_data = None
frame_lock = threading.Lock()
frame_event = threading.Event()
c_process = None


def compile_engine():
    """Compile the C visualization engine if needed."""
    if C_BINARY.exists() and C_BINARY.stat().st_mtime > C_SOURCE.stat().st_mtime:
        print(f"  Engine binary up to date: {C_BINARY}")
        return True

    print(f"  Compiling {C_SOURCE.name}...")
    result = subprocess.run(
        ["cc", "-O3", "-o", str(C_BINARY), str(C_SOURCE), "-lm", "-lpthread"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        print(f"  Compilation failed:\n{result.stderr}")
        return False
    print(f"  Compiled successfully: {C_BINARY}")
    return True


def read_exact(stream, n):
    """Read exactly n bytes from stream, handling short reads."""
    buf = b''
    while len(buf) < n:
        chunk = stream.read(n - len(buf))
        if not chunk:
            return buf  # EOF
        buf += chunk
    return buf


def read_frames(proc):
    """Read binary frames from the C process stdout."""
    global latest_frame, mesh_data

    stdout = proc.stdout

    while proc.poll() is None:
        # Read 4-byte magic
        header = read_exact(stdout, 4)
        if len(header) < 4:
            break

        magic = struct.unpack('<I', header)[0]

        if magic == MESH_MAGIC:
            # Mesh frame: 4 bytes n_sites, then positions + neighbors
            ns_bytes = read_exact(stdout, 4)
            if len(ns_bytes) < 4:
                break
            n_sites = struct.unpack('<I', ns_bytes)[0]

            # Read positions (3 floats per vertex)
            pos_bytes = read_exact(stdout, n_sites * 12)
            if len(pos_bytes) < n_sites * 12:
                break

            # Read and discard neighbor data (not sent to browser)
            for i in range(n_sites):
                nn_byte = read_exact(stdout, 1)
                if len(nn_byte) < 1:
                    break
                nn = nn_byte[0]
                if nn > 0:
                    nb_bytes = read_exact(stdout, nn * 2)
                    if len(nb_bytes) < nn * 2:
                        break

            # Send positions as base64 packed floats for efficiency
            with frame_lock:
                mesh_data = {
                    "type": "mesh",
                    "n_sites": n_sites,
                    "positions_b64": base64.b64encode(pos_bytes).decode('ascii'),
                }

            print(f"  Mesh received: {n_sites} sites")

        elif magic == TILE_MAGIC:
            # Tile frame: n_tiles_per, prog_size, then tile site lists
            tile_header = read_exact(stdout, 8)
            if len(tile_header) < 8:
                break
            n_tiles_per, prog_size = struct.unpack('<II', tile_header)

            # Read and discard tile site lists (not sent to browser)
            ok = True
            for _ in range(2):  # T+ tiles then T- tiles
                for i in range(n_tiles_per):
                    sz_bytes = read_exact(stdout, 2)
                    if len(sz_bytes) < 2: ok = False; break
                    sz = struct.unpack('<H', sz_bytes)[0]
                    sites_bytes = read_exact(stdout, sz * 2)
                    if len(sites_bytes) < sz * 2: ok = False; break
                if not ok: break
            if not ok: break

            with frame_lock:
                global tile_data
                tile_data = {
                    "type": "tiles",
                    "n_tiles_per": n_tiles_per,
                    "prog_size": prog_size,
                    "n_tiles_total": 2 * n_tiles_per,
                }

            print(f"  Tiles received: {n_tiles_per} per tetra, "
                  f"{2*n_tiles_per} total")

        elif magic == FRAME_MAGIC:
            # Data frame: epoch, n_sites, entropy, repl_count, unique_count,
            #              tp_data, tm_data
            rest = read_exact(stdout, 20)  # 5 * 4 bytes
            if len(rest) < 20:
                break

            epoch, n_sites, entropy_bits, repl_count, unique_count = \
                struct.unpack('<IIf II', rest)

            tp_data = read_exact(stdout, n_sites)
            tm_data = read_exact(stdout, n_sites)
            if len(tp_data) < n_sites or len(tm_data) < n_sites:
                break

            frame = {
                "type": "frame",
                "epoch": epoch,
                "n_sites": n_sites,
                "entropy": round(entropy_bits, 4),
                "repl_count": repl_count,
                "repl_sample": 200,
                "unique_count": unique_count,
                "unique_sample": 200,
                # Send trit data as base64 for efficiency
                "tp": base64.b64encode(tp_data).decode('ascii'),
                "tm": base64.b64encode(tm_data).decode('ascii'),
            }

            with frame_lock:
                latest_frame = frame

            frame_event.set()

            if epoch % 10000 == 0:
                print(f"  Epoch {epoch:>10,}  H={entropy_bits:.4f}  "
                      f"Repl={repl_count}/200  Unique={unique_count}/200")
        else:
            print(f"  Unknown magic: 0x{magic:08x}, resynchronizing...")
            # Try to resync by reading one byte at a time
            buf = header[1:]
            while proc.poll() is None:
                b = read_exact(stdout, 1)
                if len(b) == 0:
                    break
                buf = buf[-3:] + b
                if len(buf) >= 4:
                    m = struct.unpack('<I', buf)[0]
                    if m == FRAME_MAGIC or m == MESH_MAGIC:
                        break

    print("  C process ended")


class ThreadingHTTPServer(http.server.HTTPServer):
    """HTTP server that handles each request in a new thread."""
    import socketserver
    # Mixin for threading
    allow_reuse_address = True
    daemon_threads = True

    def process_request(self, request, client_address):
        import threading as _t
        t = _t.Thread(target=self.process_request_thread,
                      args=(request, client_address), daemon=True)
        t.start()

    def process_request_thread(self, request, client_address):
        try:
            self.finish_request(request, client_address)
        except Exception:
            self.handle_error(request, client_address)
        finally:
            self.shutdown_request(request)


class VizHandler(http.server.BaseHTTPRequestHandler):
    """HTTP handler for the visualization server."""

    def log_message(self, format, *args):
        pass  # Suppress default logging

    def do_GET(self):
        if self.path == '/' or self.path == '/index.html':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()
            self.wfile.write(HTML_FILE.read_bytes())

        elif self.path == '/mesh':
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()
            with frame_lock:
                if mesh_data:
                    self.wfile.write(json.dumps(mesh_data).encode())
                else:
                    self.wfile.write(b'null')

        elif self.path == '/stream':
            # Server-Sent Events endpoint
            self.send_response(200)
            self.send_header('Content-Type', 'text/event-stream')
            self.send_header('Cache-Control', 'no-cache')
            self.send_header('Connection', 'keep-alive')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()

            try:
                # Send mesh and tiles first
                with frame_lock:
                    if mesh_data:
                        self.wfile.write(
                            f"event: mesh\ndata: {json.dumps(mesh_data)}\n\n".encode()
                        )
                        self.wfile.flush()
                    if tile_data:
                        self.wfile.write(
                            f"event: tiles\ndata: {json.dumps(tile_data)}\n\n".encode()
                        )
                        self.wfile.flush()

                # Stream frames
                last_epoch = -1
                while True:
                    frame_event.wait(timeout=1.0)
                    frame_event.clear()

                    with frame_lock:
                        frame = latest_frame

                    if frame and frame['epoch'] != last_epoch:
                        last_epoch = frame['epoch']
                        data = json.dumps(frame)
                        self.wfile.write(f"data: {data}\n\n".encode())
                        self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError):
                pass  # Client disconnected

        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        if self.path == '/control':
            length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(length).decode()
            try:
                cmd = json.loads(body)
                action = cmd.get('action', '')

                if c_process and c_process.stdin:
                    if action == 'pause':
                        c_process.stdin.write(b'p')
                        c_process.stdin.flush()
                    elif action == 'faster':
                        c_process.stdin.write(b'-')  # decrease interval = faster
                        c_process.stdin.flush()
                    elif action == 'slower':
                        c_process.stdin.write(b'+')  # increase interval = slower
                        c_process.stdin.flush()
                    elif action == 'quit':
                        c_process.stdin.write(b'q')
                        c_process.stdin.flush()

                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"ok":true}')
            except Exception as e:
                self.send_response(400)
                self.end_headers()
                self.wfile.write(str(e).encode())
        else:
            self.send_response(404)
            self.end_headers()


def main():
    global c_process

    parser = argparse.ArgumentParser(description='Stella Soup Visualization Server')
    parser.add_argument('--port', type=int, default=8765)
    parser.add_argument('--n-sub', type=int, default=100,
                        help='Subdivisions per tetra edge (default: 100, gives ~1666 tiles)')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--snap-interval', type=int, default=500,
                        help='Epochs between snapshots (default: 500)')
    parser.add_argument('--mutation-rate', type=float, default=0.001)
    parser.add_argument('--global-interact', action='store_true',
                        help='Use global (random) tile interactions instead of local')
    args = parser.parse_args()

    print("=" * 60)
    print("  Stella Soup — Interactive Visualization")
    print("=" * 60)

    # Compile
    if not compile_engine():
        sys.exit(1)

    # Start C engine
    cmd = [
        str(C_BINARY),
        '--n-sub', str(args.n_sub),
        '--seed', str(args.seed),
        '--snap-interval', str(args.snap_interval),
        '--mutation-rate', str(args.mutation_rate),
    ]
    if args.global_interact:
        cmd.append('--global')
    print(f"  Starting engine: {' '.join(cmd)}")

    c_process = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stdin=subprocess.PIPE,
        stderr=sys.stderr,
        bufsize=0,  # unbuffered
    )

    # Start frame reader thread
    reader_thread = threading.Thread(target=read_frames, args=(c_process,), daemon=True)
    reader_thread.start()

    # Wait for first frame
    print("  Waiting for first frame...")
    for _ in range(50):  # wait up to 5 seconds
        time.sleep(0.1)
        if latest_frame is not None:
            break

    # Start HTTP server (threaded so SSE doesn't block other requests)
    server = ThreadingHTTPServer(('0.0.0.0', args.port), VizHandler)
    print(f"\n  Open in browser: http://localhost:{args.port}")
    print(f"  Press Ctrl+C to stop\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Shutting down...")
        if c_process:
            c_process.terminate()
            c_process.wait(timeout=2)
        server.shutdown()


if __name__ == '__main__':
    main()
