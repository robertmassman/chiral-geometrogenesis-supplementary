#!/usr/bin/env python3
"""
Phase Z1: Z₃ Emergence from Continuous Dynamics — Runner & Analyzer

Compiles phase_z1.c and runs all four experiments with parameter sweeps.
Parses output, generates summary tables, saves JSON results.

Usage:
    python3 run_phase_z1.py              # Run all modes
    python3 run_phase_z1.py 0            # Run only mode 0
    python3 run_phase_z1.py 0 1 2 3      # Run specific modes
"""

import subprocess
import sys
import os
import json
import re
from datetime import datetime

DIR = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(DIR, "phase_z1.c")
BIN = os.path.join(DIR, "phase_z1")
RESULTS_DIR = os.path.join(DIR, "phase_z1_results")


def compile_binary():
    """Compile phase_z1.c with optimization."""
    print("Compiling phase_z1.c ...")
    result = subprocess.run(
        ["cc", "-O3", "-o", BIN, SRC, "-lm"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("  ✓ Compiled successfully\n")


def run_experiment(args, timeout=300):
    """Run phase_z1 with given arguments, return stdout."""
    cmd = [BIN] + [str(a) for a in args]
    print(f"  Running: {' '.join(cmd)}")
    result = subprocess.run(
        cmd, capture_output=True, text=True, timeout=timeout
    )
    if result.returncode != 0:
        print(f"  ✗ Failed (exit {result.returncode})")
        if result.stderr:
            print(f"  stderr: {result.stderr[:500]}")
        return None
    return result.stdout


def parse_table(text, header_pattern):
    """Parse a text table following a header line matching pattern."""
    lines = text.split('\n')
    rows = []
    in_table = False
    for line in lines:
        if header_pattern in line:
            in_table = True
            continue
        if in_table:
            if line.startswith('---') or line.startswith('==='):
                if rows:  # End of table
                    break
                continue
            if '|' in line and line.strip():
                parts = [p.strip() for p in line.split('|')]
                rows.append(parts)
            elif line.strip() == '' and rows:
                break
    return rows


def parse_cluster_histogram(text):
    """Parse cluster histogram from output."""
    hist = {}
    for m in re.finditer(r'(\d+)\s+clusters?:\s+(\d+)/(\d+)\s+\((\d+)%\)', text):
        hist[int(m.group(1))] = {
            'count': int(m.group(2)),
            'total': int(m.group(3)),
            'pct': int(m.group(4))
        }
    # Also parse format: "   N    | count / total (pct%)"
    for m in re.finditer(r'^\s+(\d+)\s+\|\s+(\d+)\s*/\s*(\d+)\s+\((\d+)%\)', text, re.MULTILINE):
        hist[int(m.group(1))] = {
            'count': int(m.group(2)),
            'total': int(m.group(3)),
            'pct': int(m.group(4))
        }
    return hist


def parse_win_counts(text):
    """Parse Z_N win counts."""
    wins = {}
    for m in re.finditer(r'Z(\d+):\s+(\d+)/(\d+)\s+\((\d+)%\)', text):
        wins[int(m.group(1))] = {
            'count': int(m.group(2)),
            'total': int(m.group(3)),
            'pct': int(m.group(4))
        }
    return wins


# ── Mode 0: Phase Crystallization ────────────────────────────────────

def run_mode0():
    print("═══ MODE 0: Phase Crystallization on S¹ ═══\n")

    results = {'mode': 0, 'experiments': []}

    # Sweep M (number of oscillators) to see if cluster count depends on M
    for M in [12, 18, 24, 30, 42]:
        print(f"\n  M = {M}:")
        out = run_experiment([0, M, 300000, 42, 2.0], timeout=120)
        if out is None:
            continue

        # Parse the B/A sweep table
        sweep_data = []
        rows = parse_table(out, 'B/A')
        for row in rows:
            try:
                vals = [v for v in row if v]
                if len(vals) >= 7:
                    sweep_data.append({
                        'B_over_A': float(vals[0]),
                        'clusters': float(vals[1]),
                        'Z2': float(vals[2]),
                        'Z3': float(vals[3]),
                        'Z4': float(vals[4]),
                        'Z5': float(vals[5]),
                        'Z6': float(vals[6]),
                    })
            except (ValueError, IndexError):
                continue

        # Parse cluster histogram
        hist = parse_cluster_histogram(out)

        results['experiments'].append({
            'M': M,
            'sweep': sweep_data,
            'histogram': hist,
            'raw_output': out
        })

        # Print key finding
        if sweep_data:
            z3_peak = max(sweep_data, key=lambda d: d['Z3'])
            print(f"    Peak Z3 order = {z3_peak['Z3']:.3f} at B/A = {z3_peak['B_over_A']:.1f}")
            cl_at_peak = z3_peak['clusters']
            print(f"    Clusters at peak = {cl_at_peak:.1f}")

    return results


# ── Mode 1: Spontaneous Symmetry Breaking ────────────────────────────

def run_mode1():
    print("\n═══ MODE 1: Spontaneous Symmetry Breaking from U(1) ═══\n")

    results = {'mode': 1, 'experiments': []}

    # Part A: Equal couplings (built into the C code)
    print("  Part A: Equal couplings scan")
    out = run_experiment([1, 200, 500, 42, -1.0, -1.0, -1.0], timeout=120)
    if out:
        results['experiments'].append({
            'name': 'equal_couplings',
            'raw_output': out,
            'wins': parse_win_counts(out)
        })
        wins = parse_win_counts(out)
        if wins:
            winner = max(wins.items(), key=lambda x: x[1]['count'])
            print(f"    Winner from equal couplings: Z{winner[0]} ({winner[1]['pct']}%)")

    # Part B: g3-only (isolate cubic)
    print("\n  Part B: g3 only (cubic self-interaction)")
    out = run_experiment([1, 200, 500, 42, -2.0, 0.0, 0.0], timeout=120)
    if out:
        results['experiments'].append({
            'name': 'g3_only',
            'raw_output': out,
            'wins': parse_win_counts(out)
        })

    # Part C: g4-only (quartic self-interaction)
    print("\n  Part C: g4 only (quartic self-interaction)")
    out = run_experiment([1, 200, 500, 42, 0.0, -2.0, 0.0], timeout=120)
    if out:
        results['experiments'].append({
            'name': 'g4_only',
            'raw_output': out,
            'wins': parse_win_counts(out)
        })

    # Part D: Competition — g3 vs g4 at various strengths
    print("\n  Part D: g3 vs g4 competition")
    for g3 in [-0.5, -1.0, -2.0]:
        for g4 in [-0.5, -1.0, -2.0]:
            out = run_experiment([1, 200, 500, 42, g3, g4, 0.0], timeout=60)
            if out:
                wins = parse_win_counts(out)
                winner_n = max(wins.items(), key=lambda x: x[1]['count'])[0] if wins else '?'
                print(f"    g3={g3:.1f} g4={g4:.1f} → Z{winner_n}")
                results['experiments'].append({
                    'name': f'g3={g3}_g4={g4}',
                    'wins': wins
                })

    return results


# ── Mode 2: Fisher-Driven Dynamics ───────────────────────────────────

def run_mode2():
    print("\n═══ MODE 2: Fisher-Driven Dynamics ═══\n")

    results = {'mode': 2, 'experiments': []}

    # Sweep coupling (parsimony strength) and M
    for M in [6, 9, 12, 15, 18]:
        for coupling in [0.0, 0.05, 0.1, 0.2, 0.5]:
            print(f"  M={M}, coupling={coupling}")
            out = run_experiment([2, M, 80000, 42, coupling], timeout=120)
            if out:
                hist = parse_cluster_histogram(out)
                results['experiments'].append({
                    'M': M,
                    'coupling': coupling,
                    'histogram': hist,
                    'raw_output': out
                })
                if hist:
                    peak_cluster = max(hist.items(), key=lambda x: x[1]['count'])
                    print(f"    → {peak_cluster[0]} clusters ({peak_cluster[1]['pct']}%)")

    return results


# ── Mode 3: Stability Tournament ─────────────────────────────────────

def run_mode3():
    print("\n═══ MODE 3: Stability Tournament ═══\n")

    results = {'mode': 3, 'experiments': []}

    # Sweep noise amplitude
    for noise in [0.3, 0.5, 0.8, 1.0, 1.5]:
        print(f"  noise_amp = {noise}")
        out = run_experiment([3, 50, 42, noise, 3000], timeout=120)
        if out:
            wins = parse_win_counts(out)
            results['experiments'].append({
                'noise': noise,
                'raw_output': out,
                'attractor_wins': wins
            })
            if wins:
                winner = max(wins.items(), key=lambda x: x[1]['count'])
                print(f"    Attractor winner: Z{winner[0]} ({winner[1]['pct']}%)")

    return results


# ── Main ─────────────────────────────────────────────────────────────

def main():
    os.makedirs(RESULTS_DIR, exist_ok=True)

    compile_binary()

    modes = [int(a) for a in sys.argv[1:]] if len(sys.argv) > 1 else [0, 1, 2, 3]

    all_results = {
        'timestamp': datetime.now().isoformat(),
        'experiment': 'Phase Z1: Z₃ Emergence from Continuous Dynamics',
        'modes': {}
    }

    mode_runners = {
        0: run_mode0,
        1: run_mode1,
        2: run_mode2,
        3: run_mode3,
    }

    for mode in modes:
        if mode in mode_runners:
            result = mode_runners[mode]()
            all_results['modes'][mode] = result

    # Save results (strip raw output for JSON)
    results_clean = json.loads(json.dumps(all_results, default=str))
    for mode_key, mode_data in results_clean.get('modes', {}).items():
        if isinstance(mode_data, dict):
            for exp in mode_data.get('experiments', []):
                if 'raw_output' in exp:
                    # Keep first 2000 chars of raw output
                    exp['raw_output'] = exp['raw_output'][:2000] + '...' if len(exp.get('raw_output', '')) > 2000 else exp.get('raw_output', '')

    out_path = os.path.join(RESULTS_DIR, "phase_z1_results.json")
    with open(out_path, 'w') as f:
        json.dump(results_clean, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    # Print summary
    print("\n" + "=" * 70)
    print("SUMMARY: Z₃ Emergence from Continuous Dynamics")
    print("=" * 70)

    print("""
The four experiments probe Z₃ emergence through different lenses:

  Mode 0 (Phase Crystallization): Do M continuous oscillators with
    coherence+diversity pressure spontaneously form 3 clusters?

  Mode 1 (Symmetry Breaking): When all Z_N self-interactions compete
    equally, which ordering wins?

  Mode 2 (Fisher Dynamics): Does maximizing interference information
    drive oscillators into 3 clusters?

  Mode 3 (Stability Tournament): Which Z_N state is the most robust
    attractor from random initial conditions?

If Z₃ is genuinely special, it should appear as a preferred outcome
across multiple independent experiments with different mechanisms.
""")


if __name__ == "__main__":
    main()
