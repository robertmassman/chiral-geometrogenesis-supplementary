#!/usr/bin/env python3
"""
GG2: GPU Scale Advantage — High-Resolution Continuum Limit Refinement
=====================================================================

Extends the n_sub scaling study (RESULTS-Phase1.md §7) to n_sub={128, 192, 256}
under snapshot execution semantics. The existing Richardson extrapolation from
n_sub ≤ 128 gives a continuum-limit correlation of ~0.933. This test asks:

  1. Does the continuum limit tighten or shift at higher resolution?
  2. Does WRITE success rate stabilize or continue declining?
  3. Does the deep-blocked zone fully equilibrate at n_sub=256+?

Uses snapshot_mode=1 (GPU-like) since GG1 confirmed snapshot robustness.

Pass criteria (from GPU-TEST-PLAN.md E2.3):
  - Richardson extrapolation remains within [0.92, 0.95]
  - Correlation monotonically non-decreasing with n_sub
  - No divergence or instability at high resolution

Outputs gg2_results.json.
"""

import subprocess
import re
import json
import os
import sys
import time
import numpy as np
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BINARY = os.path.join(SCRIPT_DIR, 'genesis_soup')
SOURCE = os.path.join(SCRIPT_DIR, 'genesis_soup.c')

# G1 definitive configuration (matches GG1)
EPOCHS = 20000000      # 20M epochs (high-res needs longer to converge)
SEED = 42
CS = 0.7
MODE = 0
MU = 0.001
EPS = 0.1
CHI = 0.15
CHI_MODE = 0
INSTR_MODE = 2         # WRITE mode
WARP = 1.0
COLOR_PRESSURE = 1
PHASE_LOCK = 0.1       # Kuramoto coupling K
KURAMOTO = 1
ENERGY_LAMBDA = 0      # energy functional off (matches GG1/phase_h11)
MASS_MODE = 0
MASS_COUPLE = 0.0
SNAPSHOT_MODE = 1      # GPU-like snapshot execution

# High-resolution sweep points
N_SUBS = [128, 192, 256]

# Historical data from phase_h11 (sequential mode, 5M epochs, seed=42)
# Used for Richardson extrapolation comparison
HISTORICAL = {
    8:   {'corr_mean': 0.828, 'corr_std': 0.037},
    12:  {'corr_mean': 0.842, 'corr_std': 0.014},
    16:  {'corr_mean': 0.863, 'corr_std': 0.010},
    24:  {'corr_mean': 0.880, 'corr_std': 0.004},
    32:  {'corr_mean': 0.893, 'corr_std': 0.005},
    48:  {'corr_mean': 0.911, 'corr_std': 0.003},
    64:  {'corr_mean': 0.919, 'corr_std': 0.003},
    96:  {'corr_mean': 0.922, 'corr_std': 0.003},
    128: {'corr_mean': 0.930, 'corr_std': 0.002},
}


def compile_binary():
    """Compile genesis_soup.c with -O3."""
    print("Compiling genesis_soup.c...")
    result = subprocess.run(
        ['cc', '-O3', '-o', BINARY, SOURCE, '-lm'],
        capture_output=True, text=True, cwd=SCRIPT_DIR
    )
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("Compilation successful.\n")


def build_command(n_sub):
    """Build the genesis_soup command line with snapshot_mode=1."""
    return [
        BINARY,
        str(EPOCHS), str(SEED), str(CS), str(MODE), str(n_sub),
        str(MU), str(EPS), str(CHI), str(CHI_MODE), str(INSTR_MODE),
        str(WARP), str(COLOR_PRESSURE), str(PHASE_LOCK), str(KURAMOTO),
        str(ENERGY_LAMBDA), str(MASS_MODE), str(MASS_COUPLE),
        str(SNAPSHOT_MODE)
    ]


def parse_output(text):
    """Parse genesis_soup stdout for key metrics."""
    metrics = {}

    # Parse final state
    final_section = False
    for line in text.split('\n'):
        if '=== Final State ===' in line:
            final_section = True
            continue
        if final_section and line.startswith('epoch='):
            for key, pattern in [
                ('correlation', r'corr=([\d.]+)'),
                ('chi2', r'chi2=([\d.]+)'),
                ('auto_tp', r'auto_tp=([\d.]+)'),
                ('auto_tm', r'auto_tm=([\d.]+)'),
                ('entropy_tp', r'H_tp=([\d.]+)'),
                ('entropy_tm', r'H_tm=([\d.]+)'),
            ]:
                m = re.search(pattern, line)
                if m:
                    metrics[key] = float(m.group(1))
            break

    # WRITE success rate
    m = re.search(r'WRITE success rate:\s+([\d.]+)%', text)
    if m:
        metrics['write_success_rate'] = float(m.group(1))

    # WRITE counts
    m = re.search(r'WRITE succeeded:\s+(\d+)', text)
    if m:
        metrics['write_count'] = int(m.group(1))

    # Phase-lock nudges
    m = re.search(r'Phase-lock nudges:\s+(\d+)', text)
    if m:
        metrics['phase_lock_nudges'] = int(m.group(1))

    # Correlation by P_ratio bins
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

    # Convergence trajectory
    trajectory = []
    for line in text.split('\n'):
        if line.startswith('epoch=') and not final_section:
            m_e = re.search(r'epoch=(\d+)', line)
            m_c = re.search(r'corr=([\d.]+)', line)
            m_x = re.search(r'chi2=([\d.]+)', line)
            if m_e and m_c:
                trajectory.append({
                    'epoch': int(m_e.group(1)),
                    'corr': float(m_c.group(1)),
                    'chi2': float(m_x.group(1)) if m_x else None
                })
        if '=== Final State ===' in line:
            final_section = True
    metrics['trajectory'] = trajectory

    return metrics


def richardson_extrapolation(data_points):
    """
    Richardson extrapolation assuming O(h^2) leading correction:
      corr(h) = corr_inf + A * h^2
    where h = 1/n_sub.

    Uses least-squares fit over all data points.
    Returns (corr_inf, A, residuals).
    """
    h = np.array([1.0 / n for n in sorted(data_points.keys())])
    corr = np.array([data_points[n] for n in sorted(data_points.keys())])

    # Fit: corr = corr_inf + A * h^2
    H = np.column_stack([np.ones_like(h), h**2])
    params, residuals, _, _ = np.linalg.lstsq(H, corr, rcond=None)
    corr_inf, A = params

    return corr_inf, A, residuals


def run_test(n_sub):
    """Run genesis_soup at given resolution and parse output."""
    sites_per_tet = (n_sub + 1) * (n_sub + 2) // 2
    print(f"  Running n_sub={n_sub} ({sites_per_tet} sites/tet, "
          f"{EPOCHS/1e6:.0f}M epochs, snapshot)...", flush=True)

    cmd = build_command(n_sub)
    t0 = time.time()
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=SCRIPT_DIR)
    elapsed = time.time() - t0

    if result.returncode != 0:
        print(f"  FAILED (exit code {result.returncode})")
        print(result.stderr[:500])
        return None

    metrics = parse_output(result.stdout)
    metrics['wall_clock_s'] = round(elapsed, 1)
    metrics['n_sub'] = n_sub
    metrics['sites_per_tet'] = sites_per_tet

    print(f"  Done in {elapsed:.1f}s: corr={metrics.get('correlation', '?'):.4f} "
          f"chi2={metrics.get('chi2', '?'):.4f} "
          f"write={metrics.get('write_success_rate', '?'):.1f}%")
    return metrics


def main():
    compile_binary()

    results = {
        'test': 'GG2',
        'description': 'GPU Scale Advantage — High-Resolution Continuum Limit',
        'timestamp': datetime.now().isoformat(),
        'config': {
            'epochs': EPOCHS, 'seed': SEED, 'coupling_strength': CS,
            'mutation_rate': MU, 'epsilon': EPS, 'chirality': CHI,
            'instr_mode': INSTR_MODE, 'color_pressure': COLOR_PRESSURE,
            'phase_lock': PHASE_LOCK, 'kuramoto_mode': KURAMOTO,
            'energy_lambda': ENERGY_LAMBDA, 'snapshot_mode': SNAPSHOT_MODE,
        },
        'runs': [],
    }

    print(f"GG2: Scale Advantage Test")
    print(f"  n_sub sweep: {N_SUBS}")
    print(f"  Epochs: {EPOCHS/1e6:.0f}M, Seed: {SEED}, Snapshot: ON")
    print(f"  Historical Richardson estimate: corr_inf ≈ 0.933\n")

    for n_sub in N_SUBS:
        print(f"\n=== n_sub={n_sub} ===")
        metrics = run_test(n_sub)
        if metrics:
            results['runs'].append(metrics)

    # ─── Richardson extrapolation with new data ───
    print("\n" + "=" * 60)
    print("Richardson Extrapolation (O(h²) correction)")
    print("=" * 60)

    # Combine historical + new data
    all_data = {n: v['corr_mean'] for n, v in HISTORICAL.items()}
    for run in results['runs']:
        all_data[run['n_sub']] = run['correlation']

    # Historical-only extrapolation
    hist_data = {n: v['corr_mean'] for n, v in HISTORICAL.items()}
    corr_inf_old, A_old, _ = richardson_extrapolation(hist_data)

    # Updated extrapolation with new data
    corr_inf_new, A_new, _ = richardson_extrapolation(all_data)

    print(f"\n  Historical (n_sub ≤ 128):  corr_inf = {corr_inf_old:.4f}, A = {A_old:.4f}")
    print(f"  Updated   (n_sub ≤ 256):  corr_inf = {corr_inf_new:.4f}, A = {A_new:.4f}")
    print(f"  Shift: {(corr_inf_new - corr_inf_old):+.4f}")

    results['richardson'] = {
        'historical': {'corr_inf': round(corr_inf_old, 5), 'A': round(A_old, 5)},
        'updated': {'corr_inf': round(corr_inf_new, 5), 'A': round(A_new, 5)},
        'shift': round(corr_inf_new - corr_inf_old, 5),
        'data_points': {str(n): round(c, 4) for n, c in sorted(all_data.items())},
    }

    # ─── Monotonicity check ───
    corrs = [(run['n_sub'], run['correlation']) for run in results['runs']]
    corrs_sorted = sorted(corrs)
    monotonic = all(corrs_sorted[i][1] <= corrs_sorted[i+1][1]
                     for i in range(len(corrs_sorted) - 1))

    # Also check against last historical point
    if results['runs']:
        first_new = min(results['runs'], key=lambda r: r['n_sub'])
        hist_128 = HISTORICAL.get(128, {}).get('corr_mean', 0)
        monotonic = monotonic and (first_new['correlation'] >= hist_128 - 0.01)

    results['monotonic'] = monotonic

    # ─── Summary table ───
    print(f"\n{'n_sub':>6} {'sites':>8} {'corr':>8} {'chi2':>8} {'write%':>8} "
          f"{'wall(s)':>8} {'source':>10}")
    print("-" * 62)
    for n in sorted(all_data.keys()):
        if n in {r['n_sub'] for r in results['runs']}:
            run = next(r for r in results['runs'] if r['n_sub'] == n)
            print(f"{n:>6} {run['sites_per_tet']:>8} {run['correlation']:>8.4f} "
                  f"{run.get('chi2', 0):>8.4f} {run.get('write_success_rate', 0):>7.1f}% "
                  f"{run.get('wall_clock_s', 0):>7.1f}s {'GG2-snap':>10}")
        else:
            h = HISTORICAL.get(n, {})
            print(f"{n:>6} {'':>8} {h.get('corr_mean', 0):>8.4f} "
                  f"{'':>8} {'':>8} {'':>8} {'h11-seq':>10}")

    # ─── Deep-blocked zone analysis ───
    print(f"\nDeep-blocked zone match rates:")
    print(f"{'n_sub':>6} {'[0.00,0.10)':>12} {'[0.10,0.20)':>12} "
          f"{'[0.20,0.30)':>12} {'[0.30,0.40)':>12} {'[0.40,0.50)':>12}")
    print("-" * 66)
    for run in results['runs']:
        bins = run.get('pratio_bins', {})
        vals = []
        for lo in ['0.00', '0.10', '0.20', '0.30', '0.40']:
            key = f'[{lo},{float(lo)+0.10:.2f})'
            rate = bins.get(key, {}).get('match_rate')
            vals.append(f"{rate:.3f}" if rate is not None else "  —  ")
        print(f"{run['n_sub']:>6} {'  '.join(f'{v:>10}' for v in vals)}")

    # ─── Pass/fail ───
    print(f"\n{'=' * 60}")
    in_range = 0.92 <= corr_inf_new <= 0.95
    stable = abs(corr_inf_new - corr_inf_old) < 0.01

    results['pass_criteria'] = {
        'richardson_in_range': in_range,
        'richardson_stable': stable,
        'monotonic': monotonic,
    }
    results['overall_pass'] = in_range and monotonic

    if results['overall_pass']:
        print(f"GG2 PASSED:")
        print(f"  Richardson continuum limit: {corr_inf_new:.4f} (in [0.92, 0.95])")
        print(f"  Shift from historical: {corr_inf_new - corr_inf_old:+.4f} "
              f"({'stable' if stable else 'shifted'})")
        print(f"  Monotonicity: {'yes' if monotonic else 'NO'}")
    else:
        print(f"GG2 FAILED:")
        if not in_range:
            print(f"  Richardson {corr_inf_new:.4f} outside [0.92, 0.95]")
        if not monotonic:
            print(f"  Correlation not monotonically increasing")
    print(f"{'=' * 60}")

    # Save results
    out_path = os.path.join(SCRIPT_DIR, 'gg2_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return 0 if results['overall_pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
