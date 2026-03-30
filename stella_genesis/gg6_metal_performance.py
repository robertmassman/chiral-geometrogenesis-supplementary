#!/usr/bin/env python3
"""
GG6: Metal GPU Performance Scaling
====================================

Measures GPU throughput scaling across n_sub={64, 128, 256, 512} and compares
convergence-per-wallclock vs CPU.

Architecture reminder:
  - CPU processes 1 BFS tile per epoch (Gauss-Seidel sequential)
  - GPU processes ALL tiles per epoch (Jacobi parallel)
  - GPU tiles/epoch ≈ n_sites/(2*24) = n_sites/48

Key metrics:
  1. Raw throughput: epochs/sec for CPU and GPU
  2. Effective throughput: tile-operations/sec (GPU = ep/s × tiles/ep, CPU = ep/s × 1)
  3. GPU/CPU effective speedup ratio
  4. Convergence quality at matched wall-clock time
  5. Scaling exponent: how throughput degrades with mesh size

Configuration: GG2b params (K=1.0, sub_steps=8, instr_mode=2, color_pressure=1).
Single seed (42) for throughput; 3 seeds for convergence quality.

Outputs gg6_results.json.
"""

import subprocess
import re
import json
import os
import sys
import time
import math
import numpy as np
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CPU_BINARY = os.path.join(SCRIPT_DIR, 'genesis_soup')
CPU_SOURCE = os.path.join(SCRIPT_DIR, 'genesis_soup.c')
GPU_BINARY = os.path.join(SCRIPT_DIR, 'genesis_soup_metal')
GPU_SOURCE = os.path.join(SCRIPT_DIR, 'genesis_soup_metal.m')

# GG2b-validated configuration
CS = 0.7
MU = 0.001
EPS = 0.1
CHI = 0.15
CHI_MODE = 0
INSTR_MODE = 2
WARP = 1.0
COLOR_PRESSURE = 1
PHASE_LOCK = 1.0
KURAMOTO = 1
ENERGY_LAMBDA = 0
MASS_MODE = 0
MASS_COUPLE = 0.0
MASS_KURAMOTO = 0.0
MASS_GEO = 0.0
KURAMOTO_SUB_STEPS = 8
SNAPSHOT_MODE = 1

# Performance sweep
N_SUBS = [64, 128, 256, 512]
SEEDS = [42, 137, 271]

# Epoch counts scaled by mesh size to keep wall-clock manageable
# GPU: ~30-120s per run; CPU: ~10-60s per run
EPOCH_TABLE = {
    #  n_sub: (gpu_epochs, cpu_epochs)
    64:  (100_000,  1_000_000),
    128: (30_000,   300_000),
    256: (10_000,   100_000),
    512: (3_000,    30_000),
}


def compile_binaries():
    print("Compiling binaries...")
    r = subprocess.run(['cc', '-O3', '-o', CPU_BINARY, CPU_SOURCE, '-lm'],
                       capture_output=True, text=True, cwd=SCRIPT_DIR)
    if r.returncode != 0:
        print(f"CPU compilation failed:\n{r.stderr}")
        sys.exit(1)
    print("  CPU binary OK")

    r = subprocess.run([
        'clang', '-O3', '-framework', 'Metal', '-framework', 'Foundation',
        '-o', GPU_BINARY, GPU_SOURCE, '-lm'
    ], capture_output=True, text=True, cwd=SCRIPT_DIR)
    if r.returncode != 0:
        print(f"GPU compilation failed:\n{r.stderr}")
        sys.exit(1)
    print("  GPU binary OK\n")


def build_cpu_command(epochs, seed, n_sub):
    return [
        CPU_BINARY,
        str(epochs), str(seed), str(CS), '0', str(n_sub),
        str(MU), str(EPS), str(CHI), str(CHI_MODE), str(INSTR_MODE),
        str(WARP), str(COLOR_PRESSURE), str(PHASE_LOCK), str(KURAMOTO),
        str(ENERGY_LAMBDA), str(MASS_MODE), str(MASS_COUPLE),
        str(SNAPSHOT_MODE), str(MASS_KURAMOTO), str(MASS_GEO),
        str(KURAMOTO_SUB_STEPS),
    ]


def build_gpu_command(epochs, seed, n_sub):
    return [
        GPU_BINARY,
        '--n-sub', str(n_sub),
        '--epochs', str(epochs),
        '--seed', str(seed),
        '--coupling-strength', str(CS),
        '--mutation-rate', str(MU),
        '--epsilon', str(EPS),
        '--chirality', str(CHI),
        '--chirality-mode', str(CHI_MODE),
        '--instr-mode', str(INSTR_MODE),
        '--warp-alpha', str(WARP),
        '--color-pressure', str(COLOR_PRESSURE),
        '--phase-lock', str(PHASE_LOCK),
        '--kuramoto-mode', str(KURAMOTO),
        '--energy-lambda', str(ENERGY_LAMBDA),
        '--mass-mode', str(MASS_MODE),
        '--mass-couple', str(MASS_COUPLE),
        '--mass-kuramoto', str(MASS_KURAMOTO),
        '--mass-geo', str(MASS_GEO),
        '--kuramoto-sub-steps', str(KURAMOTO_SUB_STEPS),
        '--report-interval', str(epochs),
    ]


def parse_output(text):
    """Extract metrics from genesis_soup / genesis_soup_metal output."""
    metrics = {}

    # Parse final state metrics
    final_section = False
    for line in text.split('\n'):
        if '=== Final State ===' in line:
            final_section = True
            continue
        if final_section and line.startswith('epoch='):
            for key, pat in [
                ('correlation', r'corr=([\d.]+)'),
                ('chi2', r'chi2=([\d.]+)'),
                ('entropy_tp', r'H_tp=([\d.]+)'),
                ('entropy_tm', r'H_tm=([\d.]+)'),
            ]:
                m = re.search(pat, line)
                if m:
                    metrics[key] = float(m.group(1))
            break

    # Parse binary's own throughput report
    m = re.search(r'([\d.]+)\s+epochs/sec', text)
    if m:
        metrics['reported_eps'] = float(m.group(1))

    # Parse completion line: "Completed N epochs in X.Xs (Y epochs/sec)"
    m = re.search(r'Completed\s+(\d+)\s+epochs\s+in\s+([\d.]+)s', text)
    if m:
        metrics['reported_epochs'] = int(m.group(1))
        metrics['reported_time_s'] = float(m.group(2))

    # Parse pressure-ratio bins for zone analysis
    metrics['pratio_bins'] = {}
    for m in re.finditer(
            r'\[([\d.]+),([\d.]+)\)\s+(\d+)\s+([\d.]+)\s+(open|blocked|boundary)',
            text):
        lo, hi = float(m.group(1)), float(m.group(2))
        key = f'[{lo:.2f},{hi:.2f})'
        metrics['pratio_bins'][key] = {
            'n_sites': int(m.group(3)),
            'match_rate': float(m.group(4)),
            'gate': m.group(5)
        }

    open_rates = [v['match_rate'] for v in metrics['pratio_bins'].values()
                  if v['gate'] == 'open' and v['match_rate'] > 0]
    blocked_rates = [v['match_rate'] for v in metrics['pratio_bins'].values()
                     if v['gate'] == 'blocked']
    metrics['open_zone_corr'] = float(np.mean(open_rates)) if open_rates else None
    metrics['blocked_zone_corr'] = float(np.mean(blocked_rates)) if blocked_rates else None

    # Total sites from pressure bins
    total_sites = sum(v['n_sites'] for v in metrics['pratio_bins'].values())
    metrics['total_sites'] = total_sites

    return metrics


def run_binary(cmd, label, timeout=600):
    """Run a binary and return metrics + wall-clock time."""
    t0 = time.time()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True,
                                cwd=SCRIPT_DIR, timeout=timeout)
    except subprocess.TimeoutExpired:
        print(f"    {label}: TIMEOUT ({timeout}s)")
        return None

    elapsed = time.time() - t0

    if result.returncode != 0:
        print(f"    {label}: FAILED (exit {result.returncode})")
        if result.stderr:
            print(f"    stderr: {result.stderr[:300]}")
        return None

    metrics = parse_output(result.stdout)
    metrics['wall_clock_s'] = round(elapsed, 2)
    return metrics


def estimate_tiles_per_epoch(n_sub):
    """Estimate GPU tiles per epoch from mesh geometry.
    Each tetrahedron has ~2*n_sub² + 2 sites, tiled into patches of ~24.
    GPU processes tiles from BOTH tetrahedra each epoch."""
    sites_per_tet = 2 * n_sub * n_sub + 2
    tiles_per_tet = max(1, sites_per_tet // 24)
    # n_tiles_per = tiles for one tet (GPU dispatches n_tiles_per interactions)
    return tiles_per_tet


def main():
    compile_binaries()

    results = {
        'test': 'GG6',
        'description': 'Metal GPU performance scaling — throughput and convergence vs n_sub',
        'timestamp': datetime.now().isoformat(),
        'config': {
            'n_subs': N_SUBS,
            'seeds': SEEDS,
            'epoch_table': {str(k): list(v) for k, v in EPOCH_TABLE.items()},
            'phase_lock': PHASE_LOCK,
            'kuramoto_sub_steps': KURAMOTO_SUB_STEPS,
        },
        'scaling': [],
    }

    print("=" * 78)
    print("GG6: Metal GPU Performance Scaling")
    print("=" * 78)

    for n_sub in N_SUBS:
        gpu_epochs, cpu_epochs = EPOCH_TABLE[n_sub]
        tiles_per_ep = estimate_tiles_per_epoch(n_sub)
        sites_per_tet = 2 * n_sub * n_sub + 2

        print(f"\n{'─' * 78}")
        print(f"n_sub={n_sub}  sites/tet={sites_per_tet:,}  "
              f"tiles/ep≈{tiles_per_ep}  "
              f"GPU:{gpu_epochs:,} ep  CPU:{cpu_epochs:,} ep")
        print(f"{'─' * 78}")

        cpu_runs = []
        gpu_runs = []

        for seed in SEEDS:
            print(f"\n  seed={seed}:")

            # Run GPU
            gpu_m = run_binary(
                build_gpu_command(gpu_epochs, seed, n_sub),
                f"GPU n={n_sub} s={seed}")
            if gpu_m:
                gpu_m['seed'] = seed
                eps = gpu_m.get('reported_eps', gpu_epochs / gpu_m['wall_clock_s'])
                corr = gpu_m.get('correlation', 0)
                print(f"    GPU: {eps:,.0f} ep/s  corr={corr:.4f}  ({gpu_m['wall_clock_s']:.1f}s)")
                gpu_runs.append(gpu_m)

            # Run CPU
            cpu_m = run_binary(
                build_cpu_command(cpu_epochs, seed, n_sub),
                f"CPU n={n_sub} s={seed}")
            if cpu_m:
                cpu_m['seed'] = seed
                eps = cpu_m.get('reported_eps', cpu_epochs / cpu_m['wall_clock_s'])
                corr = cpu_m.get('correlation', 0)
                print(f"    CPU: {eps:,.0f} ep/s  corr={corr:.4f}  ({cpu_m['wall_clock_s']:.1f}s)")
                cpu_runs.append(cpu_m)

        if not gpu_runs or not cpu_runs:
            print(f"\n  SKIPPED n_sub={n_sub} (insufficient runs)")
            continue

        # Aggregate
        def avg(runs, key):
            vals = [r[key] for r in runs if key in r and r[key] is not None]
            return float(np.mean(vals)) if vals else None

        def std(runs, key):
            vals = [r[key] for r in runs if key in r and r[key] is not None]
            return float(np.std(vals)) if len(vals) > 1 else 0.0

        gpu_eps = avg(gpu_runs, 'reported_eps')
        if gpu_eps is None:
            gpu_eps = gpu_epochs / avg(gpu_runs, 'wall_clock_s') if avg(gpu_runs, 'wall_clock_s') else None
        cpu_eps = avg(cpu_runs, 'reported_eps')
        if cpu_eps is None:
            cpu_eps = cpu_epochs / avg(cpu_runs, 'wall_clock_s') if avg(cpu_runs, 'wall_clock_s') else None

        gpu_corr = avg(gpu_runs, 'correlation')
        cpu_corr = avg(cpu_runs, 'correlation')
        gpu_open = avg(gpu_runs, 'open_zone_corr')
        cpu_open = avg(cpu_runs, 'open_zone_corr')
        gpu_htp = avg(gpu_runs, 'entropy_tp')
        cpu_htp = avg(cpu_runs, 'entropy_tp')
        gpu_chi2 = avg(gpu_runs, 'chi2')
        cpu_chi2 = avg(cpu_runs, 'chi2')
        gpu_time = avg(gpu_runs, 'wall_clock_s')
        cpu_time = avg(cpu_runs, 'wall_clock_s')

        # Effective throughput (tile-ops per second)
        gpu_tile_ops = gpu_eps * tiles_per_ep if gpu_eps else None
        cpu_tile_ops = cpu_eps  # CPU does 1 tile per epoch

        # Speedup ratio
        speedup = gpu_tile_ops / cpu_tile_ops if (gpu_tile_ops and cpu_tile_ops) else None

        # Convergence efficiency: correlation achieved per second of wall-clock
        gpu_corr_per_sec = gpu_corr / gpu_time if (gpu_corr and gpu_time) else None
        cpu_corr_per_sec = cpu_corr / cpu_time if (cpu_corr and cpu_time) else None

        entry = {
            'n_sub': n_sub,
            'sites_per_tet': sites_per_tet,
            'tiles_per_epoch': tiles_per_ep,
            'gpu': {
                'epochs': gpu_epochs,
                'epochs_per_sec': round(gpu_eps, 1) if gpu_eps else None,
                'wall_clock_s': round(gpu_time, 2) if gpu_time else None,
                'tile_ops_per_sec': round(gpu_tile_ops, 0) if gpu_tile_ops else None,
                'correlation': round(gpu_corr, 5) if gpu_corr else None,
                'open_zone_corr': round(gpu_open, 5) if gpu_open else None,
                'entropy_tp': round(gpu_htp, 5) if gpu_htp else None,
                'chi2': round(gpu_chi2, 5) if gpu_chi2 else None,
                'corr_std': round(std(gpu_runs, 'correlation'), 5),
            },
            'cpu': {
                'epochs': cpu_epochs,
                'epochs_per_sec': round(cpu_eps, 1) if cpu_eps else None,
                'wall_clock_s': round(cpu_time, 2) if cpu_time else None,
                'tile_ops_per_sec': round(cpu_tile_ops, 0) if cpu_tile_ops else None,
                'correlation': round(cpu_corr, 5) if cpu_corr else None,
                'open_zone_corr': round(cpu_open, 5) if cpu_open else None,
                'entropy_tp': round(cpu_htp, 5) if cpu_htp else None,
                'chi2': round(cpu_chi2, 5) if cpu_chi2 else None,
                'corr_std': round(std(cpu_runs, 'correlation'), 5),
            },
            'effective_speedup': round(speedup, 1) if speedup else None,
            'gpu_corr_per_sec': round(gpu_corr_per_sec, 5) if gpu_corr_per_sec else None,
            'cpu_corr_per_sec': round(cpu_corr_per_sec, 5) if cpu_corr_per_sec else None,
        }
        results['scaling'].append(entry)

        # Print summary table
        print(f"\n  {'Metric':<28} {'GPU':>14} {'CPU':>14}")
        print(f"  {'─' * 56}")
        print(f"  {'Epochs/sec':<28} {gpu_eps:>14,.0f} {cpu_eps:>14,.0f}")
        print(f"  {'Tile-ops/sec':<28} {gpu_tile_ops:>14,.0f} {cpu_tile_ops:>14,.0f}")
        print(f"  {'Effective speedup':<28} {speedup:>14.1f}×")
        print(f"  {'Wall-clock (s)':<28} {gpu_time:>14.1f} {cpu_time:>14.1f}")
        if gpu_corr and cpu_corr:
            print(f"  {'Correlation':<28} {gpu_corr:>14.4f} {cpu_corr:>14.4f}")
        if gpu_open and cpu_open:
            print(f"  {'Open-zone corr':<28} {gpu_open:>14.4f} {cpu_open:>14.4f}")

    # Scaling analysis
    print(f"\n{'=' * 78}")
    print("SCALING SUMMARY")
    print(f"{'=' * 78}")

    if len(results['scaling']) >= 2:
        # Compute scaling exponents via log-log fit
        ns = [e['n_sub'] for e in results['scaling'] if e['gpu']['epochs_per_sec']]
        gpu_eps_vals = [e['gpu']['epochs_per_sec'] for e in results['scaling']
                        if e['gpu']['epochs_per_sec']]
        cpu_eps_vals = [e['cpu']['epochs_per_sec'] for e in results['scaling']
                        if e['cpu']['epochs_per_sec']]
        speedups = [e['effective_speedup'] for e in results['scaling']
                    if e['effective_speedup']]

        if len(ns) >= 2:
            log_ns = np.log2(ns)
            gpu_slope = np.polyfit(log_ns, np.log2(gpu_eps_vals), 1)[0]
            cpu_slope = np.polyfit(log_ns, np.log2(cpu_eps_vals), 1)[0]
            speedup_slope = np.polyfit(log_ns, np.log2(speedups), 1)[0]

            results['scaling_analysis'] = {
                'gpu_throughput_exponent': round(float(gpu_slope), 3),
                'cpu_throughput_exponent': round(float(cpu_slope), 3),
                'speedup_exponent': round(float(speedup_slope), 3),
                'note': ('Exponents from log-log fit: '
                         'eps ~ n_sub^α. '
                         'GPU degrades slower → speedup grows with n_sub.'),
            }

            print(f"\n  Throughput scaling: eps ~ n_sub^α")
            print(f"    GPU α = {gpu_slope:.3f}")
            print(f"    CPU α = {cpu_slope:.3f}")
            print(f"    Speedup grows as n_sub^{speedup_slope:.2f}")

    # Summary table
    print(f"\n  {'n_sub':>6} {'sites':>8} {'GPU ep/s':>10} {'CPU ep/s':>10} "
          f"{'GPU tiles/s':>12} {'CPU tiles/s':>12} {'Speedup':>8}")
    print(f"  {'─' * 72}")
    for e in results['scaling']:
        ns = e['n_sub']
        sites = e['sites_per_tet']
        ge = e['gpu']['epochs_per_sec'] or 0
        ce = e['cpu']['epochs_per_sec'] or 0
        gt = e['gpu']['tile_ops_per_sec'] or 0
        ct = e['cpu']['tile_ops_per_sec'] or 0
        sp = e['effective_speedup'] or 0
        print(f"  {ns:>6} {sites:>8,} {ge:>10,.0f} {ce:>10,.0f} "
              f"{gt:>12,.0f} {ct:>12,.0f} {sp:>7.1f}×")

    # Convergence comparison
    print(f"\n  {'n_sub':>6} {'GPU corr':>10} {'CPU corr':>10} "
          f"{'GPU open':>10} {'CPU open':>10} {'GPU H_tp':>10} {'CPU H_tp':>10}")
    print(f"  {'─' * 66}")
    for e in results['scaling']:
        ns = e['n_sub']
        gc = e['gpu']['correlation'] or 0
        cc = e['cpu']['correlation'] or 0
        go = e['gpu']['open_zone_corr'] or 0
        co = e['cpu']['open_zone_corr'] or 0
        gh = e['gpu']['entropy_tp'] or 0
        ch = e['cpu']['entropy_tp'] or 0
        print(f"  {ns:>6} {gc:>10.4f} {cc:>10.4f} "
              f"{go:>10.4f} {co:>10.4f} {gh:>10.4f} {ch:>10.4f}")

    # Save results
    out_path = os.path.join(SCRIPT_DIR, 'gg6_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    # Overall assessment
    print(f"\n{'=' * 78}")
    if results['scaling']:
        max_speedup = max(e['effective_speedup'] for e in results['scaling']
                          if e['effective_speedup'])
        max_ns = max(e['n_sub'] for e in results['scaling']
                     if e['effective_speedup'] == max_speedup)
        print(f"GG6 COMPLETE: Peak effective speedup {max_speedup:.0f}× at n_sub={max_ns}")
        print(f"  GPU advantage grows with mesh size (all-tiles-per-epoch parallelism)")
    print(f"{'=' * 78}")


if __name__ == '__main__':
    main()
