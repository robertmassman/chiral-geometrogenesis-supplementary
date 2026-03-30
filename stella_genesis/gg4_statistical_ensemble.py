#!/usr/bin/env python3
"""
GG4: Statistical Ensemble — Single Attractor Test Under Genesis Dynamics
=========================================================================

G4 (StellaLang) showed a single deterministic attractor with entropy CV = 4.7e-5
across 20 runs. Genesis has richer dynamics (SENSE/WRITE feedback, Kuramoto
phase accumulation, energy functional) which could create multiple attractors
or seed-dependent outcomes.

Method: 20 independent runs at n_sub=64, seeds 1-20, 2M epochs, snapshot_mode=1.

Pass criteria (from GPU-TEST-PLAN.md E2.5):
  - Single attractor: unimodal distribution
  - Correlation CV < 0.01
  - No bimodality in correlation or entropy distributions

Outputs gg4_results.json.
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

# Configuration (matches GG1 at n_sub=64)
EPOCHS = 2000000       # 2M epochs
N_SUB = 64
CS = 0.7
MODE = 0
MU = 0.001
EPS = 0.1
CHI = 0.15
CHI_MODE = 0
INSTR_MODE = 2
WARP = 1.0
COLOR_PRESSURE = 1
PHASE_LOCK = 0.1
KURAMOTO = 1
ENERGY_LAMBDA = 0
MASS_MODE = 0
MASS_COUPLE = 0.0
SNAPSHOT_MODE = 1      # GPU-like snapshot

SEEDS = list(range(1, 21))  # 20 independent runs


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


def build_command(seed):
    """Build the genesis_soup command line."""
    return [
        BINARY,
        str(EPOCHS), str(seed), str(CS), str(MODE), str(N_SUB),
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

    # Phase-lock nudges
    m = re.search(r'Phase-lock nudges:\s+(\d+)', text)
    if m:
        metrics['phase_lock_nudges'] = int(m.group(1))

    # Deep-blocked zone match rate
    metrics['pratio_bins'] = {}
    for m_bin in re.finditer(
            r'\[([\d.]+),([\d.]+)\)\s+(\d+)\s+([\d.]+)\s+(open|blocked|boundary)',
            text):
        lo, hi = float(m_bin.group(1)), float(m_bin.group(2))
        key = f'[{lo:.2f},{hi:.2f})'
        metrics['pratio_bins'][key] = {
            'n_sites': int(m_bin.group(3)),
            'match_rate': float(m_bin.group(4)),
            'gate': m_bin.group(5)
        }

    return metrics


def compute_deep_blocked_rate(metrics):
    """Extract deep-blocked zone ([0.30,0.40)) match rate."""
    bins = metrics.get('pratio_bins', {})
    for key, val in bins.items():
        if key.startswith('[0.30'):
            return val['match_rate']
    blocked = [v['match_rate'] for v in bins.values() if v['gate'] == 'blocked']
    return sum(blocked) / len(blocked) if blocked else None


def dip_test_statistic(data):
    """
    Simple bimodality test: Hartigan's dip statistic approximation.
    Returns True if data appears unimodal (dip < threshold).
    Uses the sorted-data gap approach as a lightweight proxy.
    """
    if len(data) < 5:
        return True  # too few points to assess
    x = np.sort(data)
    n = len(x)
    # Compute the maximum gap between consecutive sorted values
    gaps = np.diff(x)
    data_range = x[-1] - x[0]
    if data_range == 0:
        return True  # all identical
    # Normalized max gap: large gap suggests bimodality
    max_gap_ratio = np.max(gaps) / data_range
    # For n uniform points, expected max gap ~ ln(n)/n ≈ 0.15 for n=20.
    # A true bimodal split creates a gap >> expected. Use 0.3 as threshold:
    # any single gap > 30% of the range indicates a split.
    return max_gap_ratio < 0.30


def main():
    compile_binary()

    results = {
        'test': 'GG4',
        'description': 'Statistical Ensemble — Single Attractor Test',
        'timestamp': datetime.now().isoformat(),
        'config': {
            'epochs': EPOCHS, 'n_sub': N_SUB, 'n_seeds': len(SEEDS),
            'coupling_strength': CS, 'mutation_rate': MU,
            'epsilon': EPS, 'chirality': CHI, 'instr_mode': INSTR_MODE,
            'color_pressure': COLOR_PRESSURE, 'phase_lock': PHASE_LOCK,
            'kuramoto_mode': KURAMOTO, 'energy_lambda': ENERGY_LAMBDA,
            'snapshot_mode': SNAPSHOT_MODE,
        },
        'runs': [],
    }

    print(f"GG4: Statistical Ensemble Test")
    print(f"  {len(SEEDS)} runs, seeds {SEEDS[0]}-{SEEDS[-1]}")
    print(f"  n_sub={N_SUB}, {EPOCHS/1e6:.0f}M epochs, snapshot=ON")
    print(f"  G4 reference (StellaLang): entropy CV = 4.7e-5\n")

    total_t0 = time.time()

    for i, seed in enumerate(SEEDS):
        print(f"  [{i+1:2d}/{len(SEEDS)}] seed={seed:3d} ...", end=' ', flush=True)

        cmd = build_command(seed)
        t0 = time.time()
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=SCRIPT_DIR)
        elapsed = time.time() - t0

        if result.returncode != 0:
            print(f"FAILED (exit {result.returncode})")
            continue

        metrics = parse_output(result.stdout)
        metrics['seed'] = seed
        metrics['wall_clock_s'] = round(elapsed, 1)
        metrics['deep_blocked_rate'] = compute_deep_blocked_rate(metrics)

        # Remove large pratio_bins from per-run storage to keep JSON manageable
        metrics.pop('pratio_bins', None)

        results['runs'].append(metrics)
        print(f"corr={metrics.get('correlation', '?'):.4f} "
              f"H_tp={metrics.get('entropy_tp', '?'):.4f} "
              f"chi2={metrics.get('chi2', '?'):.4f} "
              f"({elapsed:.1f}s)")

    total_elapsed = time.time() - total_t0
    results['total_wall_clock_s'] = round(total_elapsed, 1)

    # ─── Statistical analysis ───
    print(f"\n{'=' * 60}")
    print(f"Statistical Analysis ({len(results['runs'])} successful runs)")
    print(f"{'=' * 60}")

    if len(results['runs']) < 5:
        print("Too few successful runs for meaningful statistics.")
        results['overall_pass'] = False
        out_path = os.path.join(SCRIPT_DIR, 'gg4_results.json')
        with open(out_path, 'w') as f:
            json.dump(results, f, indent=2, default=str)
        return 1

    # Extract arrays
    corrs = np.array([r['correlation'] for r in results['runs']])
    h_tps = np.array([r.get('entropy_tp', 0) for r in results['runs']])
    h_tms = np.array([r.get('entropy_tm', 0) for r in results['runs']])
    chi2s = np.array([r.get('chi2', 0) for r in results['runs']])
    writes = np.array([r.get('write_success_rate', 0) for r in results['runs']])
    deep_rates = np.array([r.get('deep_blocked_rate', 0) for r in results['runs']
                           if r.get('deep_blocked_rate') is not None])

    def stats(arr, name):
        mean = np.mean(arr)
        std = np.std(arr)
        cv = std / mean if mean > 0 else float('inf')
        return {
            'mean': round(float(mean), 6),
            'std': round(float(std), 6),
            'cv': round(float(cv), 6),
            'min': round(float(np.min(arr)), 6),
            'max': round(float(np.max(arr)), 6),
            'range': round(float(np.max(arr) - np.min(arr)), 6),
        }

    stat_corr = stats(corrs, 'correlation')
    stat_h_tp = stats(h_tps, 'entropy_tp')
    stat_h_tm = stats(h_tms, 'entropy_tm')
    stat_chi2 = stats(chi2s, 'chi2')
    stat_write = stats(writes, 'write_success_rate')
    stat_deep = stats(deep_rates, 'deep_blocked_rate') if len(deep_rates) > 0 else None

    results['statistics'] = {
        'correlation': stat_corr,
        'entropy_tp': stat_h_tp,
        'entropy_tm': stat_h_tm,
        'chi2': stat_chi2,
        'write_success_rate': stat_write,
        'deep_blocked_rate': stat_deep,
    }

    # Print summary table
    print(f"\n{'Metric':<22} {'Mean':>10} {'Std':>10} {'CV':>10} "
          f"{'Min':>10} {'Max':>10}")
    print("-" * 72)
    for name, s in results['statistics'].items():
        if s is None:
            continue
        print(f"  {name:<20} {s['mean']:>10.4f} {s['std']:>10.6f} "
              f"{s['cv']:>10.6f} {s['min']:>10.4f} {s['max']:>10.4f}")

    # ─── Bimodality test ───
    corr_unimodal = dip_test_statistic(corrs)
    h_unimodal = dip_test_statistic(h_tps)
    chi2_unimodal = dip_test_statistic(chi2s)

    results['bimodality'] = {
        'correlation_unimodal': bool(corr_unimodal),
        'entropy_unimodal': bool(h_unimodal),
        'chi2_unimodal': bool(chi2_unimodal),
    }

    print(f"\nBimodality test (gap-based):")
    print(f"  Correlation: {'unimodal' if corr_unimodal else 'BIMODAL'}")
    print(f"  Entropy:     {'unimodal' if h_unimodal else 'BIMODAL'}")
    print(f"  |chi|^2:     {'unimodal' if chi2_unimodal else 'BIMODAL'}")

    # ─── Pass/fail ───
    corr_cv_pass = stat_corr['cv'] < 0.01
    unimodal_pass = corr_unimodal and h_unimodal
    overall_pass = corr_cv_pass and unimodal_pass

    results['pass_criteria'] = {
        'corr_cv_below_0.01': corr_cv_pass,
        'corr_cv_actual': stat_corr['cv'],
        'distributions_unimodal': unimodal_pass,
    }
    results['overall_pass'] = overall_pass

    # ─── Comparison with G4 (StellaLang) ───
    print(f"\nComparison with G4 (StellaLang on GPU):")
    print(f"  G4 entropy CV:     4.7e-5")
    print(f"  GG4 entropy CV:    {stat_h_tp['cv']:.2e}")
    print(f"  GG4 correlation CV: {stat_corr['cv']:.2e}")
    richer = stat_h_tp['cv'] > 4.7e-5
    print(f"  Genesis dynamics {'introduce more variability' if richer else 'are equally stable'}")

    print(f"\n{'=' * 60}")
    if overall_pass:
        print(f"GG4 PASSED: Single attractor confirmed.")
        print(f"  Correlation: {stat_corr['mean']:.4f} +/- {stat_corr['std']:.4f} "
              f"(CV = {stat_corr['cv']:.2e})")
        print(f"  All distributions unimodal.")
    else:
        print(f"GG4 FAILED:")
        if not corr_cv_pass:
            print(f"  Correlation CV = {stat_corr['cv']:.4f} >= 0.01")
        if not unimodal_pass:
            print(f"  Bimodal distribution detected")
    print(f"Total wall-clock: {total_elapsed:.0f}s ({total_elapsed/60:.1f}min)")
    print(f"{'=' * 60}")

    # Save results
    out_path = os.path.join(SCRIPT_DIR, 'gg4_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return 0 if overall_pass else 1


if __name__ == '__main__':
    sys.exit(main())
