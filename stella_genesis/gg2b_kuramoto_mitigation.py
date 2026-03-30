#!/usr/bin/env python3
"""
GG2b: Kuramoto Sub-Iteration Mitigation for High-Resolution Snapshot Mode
==========================================================================

GG2 failed because Jacobi-style Kuramoto updates propagate phase coherence
only 1 mesh hop per epoch. At high n_sub (>=192), the blocked zone spans
~40+ hops, so coherence can't diffuse across it.

This test sweeps two mitigation dimensions:
  1. kuramoto_sub_steps: multiple Kuramoto sweeps per epoch with phase
     re-snapshotting between sub-steps (allows multi-hop diffusion)
  2. phase_lock (K): coupling strength

Phase 1 (coarse): 5M epochs, seed=42, sweep sub_steps x K x n_sub
Phase 2 (confirmation): 20M epochs, 3 seeds, winning configuration

Pass criteria:
  - Richardson extrapolation in [0.92, 0.95]
  - Correlation monotonically non-decreasing with n_sub
  - Deep-blocked [0.30,0.40) match rate >= 0.90 at n_sub=256

Outputs gg2b_results.json.
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

# Base configuration (matches GG1/GG2)
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
KURAMOTO = 1
ENERGY_LAMBDA = 0
MASS_MODE = 0
MASS_COUPLE = 0.0
SNAPSHOT_MODE = 1
MASS_KURAMOTO = 0.0
MASS_GEO = 0.0

# Sweep parameters
N_SUBS = [128, 192, 256]
SUB_STEPS_SWEEP = [1, 4, 8, 16]
K_SWEEP = [0.1, 0.5, 1.0]

# Phase 1: coarse sweep
EPOCHS_COARSE = 5000000    # 5M
# Phase 2: confirmation
EPOCHS_CONFIRM = 20000000  # 20M
CONFIRM_SEEDS = [42, 137, 271]

# Historical data from phase_h11 (sequential mode, 5M epochs)
HISTORICAL = {
    8:   0.828, 12:  0.842, 16:  0.863, 24:  0.880,
    32:  0.893, 48:  0.911, 64:  0.919, 96:  0.922,
    128: 0.930,
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


def build_command(epochs, seed, n_sub, phase_lock, kuramoto_sub_steps):
    """Build genesis_soup command line."""
    return [
        BINARY,
        str(epochs), str(seed), str(CS), str(MODE), str(n_sub),
        str(MU), str(EPS), str(CHI), str(CHI_MODE), str(INSTR_MODE),
        str(WARP), str(COLOR_PRESSURE), str(phase_lock), str(KURAMOTO),
        str(ENERGY_LAMBDA), str(MASS_MODE), str(MASS_COUPLE),
        str(SNAPSHOT_MODE), str(MASS_KURAMOTO), str(MASS_GEO),
        str(kuramoto_sub_steps)
    ]


def parse_output(text):
    """Parse genesis_soup stdout for key metrics."""
    metrics = {}

    final_section = False
    for line in text.split('\n'):
        if '=== Final State ===' in line:
            final_section = True
            continue
        if final_section and line.startswith('epoch='):
            for key, pattern in [
                ('correlation', r'corr=([\d.]+)'),
                ('chi2', r'chi2=([\d.]+)'),
                ('entropy_tp', r'H_tp=([\d.]+)'),
                ('entropy_tm', r'H_tm=([\d.]+)'),
            ]:
                m = re.search(pattern, line)
                if m:
                    metrics[key] = float(m.group(1))
            break

    m = re.search(r'WRITE success rate:\s+([\d.]+)%', text)
    if m:
        metrics['write_success_rate'] = float(m.group(1))

    m = re.search(r'Phase-lock nudges:\s+(\d+)', text)
    if m:
        metrics['phase_lock_nudges'] = int(m.group(1))

    # Deep-blocked zone match rate
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

    # Get deep-blocked match rate shortcut
    deep_blocked = metrics['pratio_bins'].get('[0.30,0.40)', {})
    metrics['deep_blocked_match'] = deep_blocked.get('match_rate', None)

    return metrics


def richardson_extrapolation(data_points):
    """Richardson extrapolation: corr(h) = corr_inf + A * h^2, h = 1/n_sub."""
    h = np.array([1.0 / n for n in sorted(data_points.keys())])
    corr = np.array([data_points[n] for n in sorted(data_points.keys())])
    H = np.column_stack([np.ones_like(h), h**2])
    params, _, _, _ = np.linalg.lstsq(H, corr, rcond=None)
    return params[0], params[1]  # corr_inf, A


def run_single(epochs, seed, n_sub, phase_lock, sub_steps, label=""):
    """Run a single genesis_soup configuration."""
    cmd = build_command(epochs, seed, n_sub, phase_lock, sub_steps)
    t0 = time.time()
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=SCRIPT_DIR)
    elapsed = time.time() - t0

    if result.returncode != 0:
        print(f"  FAILED (exit {result.returncode})")
        return None

    metrics = parse_output(result.stdout)
    metrics['wall_clock_s'] = round(elapsed, 1)
    metrics['n_sub'] = n_sub
    metrics['phase_lock'] = phase_lock
    metrics['kuramoto_sub_steps'] = sub_steps
    metrics['seed'] = seed
    metrics['epochs'] = epochs

    corr = metrics.get('correlation', 0)
    db = metrics.get('deep_blocked_match', 0)
    print(f"  {label}n_sub={n_sub:>3} K={phase_lock:.1f} sub={sub_steps:>2}: "
          f"corr={corr:.4f} deep_blocked={db:.3f} "
          f"({elapsed:.1f}s)")
    return metrics


def main():
    compile_binary()

    results = {
        'test': 'GG2b',
        'description': 'Kuramoto sub-iteration mitigation for high-res snapshot',
        'timestamp': datetime.now().isoformat(),
        'phase1_coarse': [],
        'phase2_confirm': [],
    }

    # ═══════════════════════════════════════════════════════════════════
    # Phase 1: Coarse sweep (5M epochs, seed=42)
    # ═══════════════════════════════════════════════════════════════════
    print("=" * 70)
    print("PHASE 1: Coarse Sweep (5M epochs, seed=42)")
    print("=" * 70)

    for K in K_SWEEP:
        for sub in SUB_STEPS_SWEEP:
            for n_sub in N_SUBS:
                metrics = run_single(EPOCHS_COARSE, SEED, n_sub, K, sub)
                if metrics:
                    results['phase1_coarse'].append(metrics)

    # ─── Analyze Phase 1 ───
    print("\n" + "=" * 70)
    print("PHASE 1 RESULTS")
    print("=" * 70)

    # Build summary table
    print(f"\n{'K':>5} {'sub':>4} {'n128':>8} {'n192':>8} {'n256':>8} "
          f"{'mono':>5} {'db256':>7}")
    print("-" * 50)

    best_config = None
    best_score = -1

    for K in K_SWEEP:
        for sub in SUB_STEPS_SWEEP:
            runs = [r for r in results['phase1_coarse']
                    if r['phase_lock'] == K and r['kuramoto_sub_steps'] == sub]
            if len(runs) < 3:
                continue

            corrs = {}
            db256 = None
            for r in runs:
                corrs[r['n_sub']] = r['correlation']
                if r['n_sub'] == 256:
                    db256 = r.get('deep_blocked_match', 0)

            c128 = corrs.get(128, 0)
            c192 = corrs.get(192, 0)
            c256 = corrs.get(256, 0)
            mono = c128 <= c192 + 0.005 and c192 <= c256 + 0.005
            mono_str = "yes" if mono else "NO"

            print(f"{K:>5.1f} {sub:>4} {c128:>8.4f} {c192:>8.4f} {c256:>8.4f} "
                  f"{mono_str:>5} {db256:>7.3f}" if db256 else
                  f"{K:>5.1f} {sub:>4} {c128:>8.4f} {c192:>8.4f} {c256:>8.4f} "
                  f"{mono_str:>5}    —")

            # Score: prefer monotonic, high correlation, high deep-blocked
            if db256 is None:
                db256 = 0
            score = (10.0 if mono else 0.0) + c256 + db256
            if score > best_score:
                best_score = score
                best_config = (K, sub)

    if best_config is None:
        print("\nNo valid configurations found!")
        sys.exit(1)

    best_K, best_sub = best_config
    print(f"\nBest configuration: K={best_K}, sub_steps={best_sub}")

    # ═══════════════════════════════════════════════════════════════════
    # Phase 2: Confirmation (20M epochs, multiple seeds)
    # ═══════════════════════════════════════════════════════════════════
    print("\n" + "=" * 70)
    print(f"PHASE 2: Confirmation (20M epochs, seeds={CONFIRM_SEEDS})")
    print(f"  Configuration: K={best_K}, sub_steps={best_sub}")
    print("=" * 70)

    for seed in CONFIRM_SEEDS:
        for n_sub in N_SUBS:
            metrics = run_single(EPOCHS_CONFIRM, seed, n_sub, best_K, best_sub,
                                 label=f"seed={seed} ")
            if metrics:
                results['phase2_confirm'].append(metrics)

    # ─── Analyze Phase 2 ───
    print("\n" + "=" * 70)
    print("PHASE 2 RESULTS — Confirmation")
    print("=" * 70)

    # Mean correlations per n_sub
    mean_corrs = {}
    mean_db = {}
    for n_sub in N_SUBS:
        runs = [r for r in results['phase2_confirm'] if r['n_sub'] == n_sub]
        if runs:
            corrs = [r['correlation'] for r in runs]
            dbs = [r.get('deep_blocked_match', 0) for r in runs if r.get('deep_blocked_match') is not None]
            mean_corrs[n_sub] = np.mean(corrs)
            mean_db[n_sub] = np.mean(dbs) if dbs else 0
            print(f"  n_sub={n_sub}: corr={np.mean(corrs):.4f} ± {np.std(corrs):.4f}  "
                  f"deep_blocked={np.mean(dbs):.3f} ± {np.std(dbs):.3f}")

    # Richardson extrapolation
    all_data = dict(HISTORICAL)
    for n_sub, corr in mean_corrs.items():
        all_data[n_sub] = corr

    corr_inf, A = richardson_extrapolation(all_data)
    corr_inf_hist, A_hist = richardson_extrapolation(HISTORICAL)

    print(f"\n  Richardson extrapolation:")
    print(f"    Historical (n_sub ≤ 128, sequential):  corr_inf = {corr_inf_hist:.4f}")
    print(f"    Updated   (n_sub ≤ 256, mitigated):    corr_inf = {corr_inf:.4f}")
    print(f"    Shift: {corr_inf - corr_inf_hist:+.4f}")

    # Monotonicity check
    sorted_nsubs = sorted(mean_corrs.keys())
    monotonic = all(mean_corrs[sorted_nsubs[i]] <= mean_corrs[sorted_nsubs[i+1]] + 0.005
                    for i in range(len(sorted_nsubs) - 1))
    # Also check against historical n_sub=128
    if 128 in mean_corrs:
        monotonic = monotonic and (mean_corrs[128] >= HISTORICAL[128] - 0.01)

    # Deep-blocked at n_sub=256
    db256_pass = mean_db.get(256, 0) >= 0.90
    richardson_pass = 0.92 <= corr_inf <= 0.95

    results['best_config'] = {
        'phase_lock': best_K,
        'kuramoto_sub_steps': best_sub,
    }
    results['confirmation'] = {
        'mean_correlations': {str(k): round(v, 5) for k, v in mean_corrs.items()},
        'mean_deep_blocked': {str(k): round(v, 4) for k, v in mean_db.items()},
        'richardson_inf': round(corr_inf, 5),
        'richardson_A': round(A, 5),
        'richardson_inf_historical': round(corr_inf_hist, 5),
        'shift': round(corr_inf - corr_inf_hist, 5),
    }
    results['pass_criteria'] = {
        'richardson_in_range': richardson_pass,
        'monotonic': monotonic,
        'deep_blocked_256_above_090': db256_pass,
    }
    results['overall_pass'] = richardson_pass and monotonic and db256_pass

    # ─── Final verdict ───
    print(f"\n{'=' * 70}")
    if results['overall_pass']:
        print(f"GG2b PASSED")
        print(f"  Best config: K={best_K}, sub_steps={best_sub}")
        print(f"  Richardson: {corr_inf:.4f} (in [0.92, 0.95]: {'yes' if richardson_pass else 'NO'})")
        print(f"  Monotonic: {'yes' if monotonic else 'NO'}")
        print(f"  Deep-blocked n256: {mean_db.get(256, 0):.3f} (>= 0.90: {'yes' if db256_pass else 'NO'})")
    else:
        print(f"GG2b FAILED")
        if not richardson_pass:
            print(f"  Richardson {corr_inf:.4f} outside [0.92, 0.95]")
        if not monotonic:
            print(f"  Correlation not monotonically increasing")
        if not db256_pass:
            print(f"  Deep-blocked n256 = {mean_db.get(256, 0):.3f} < 0.90")
        print(f"  Best config tried: K={best_K}, sub_steps={best_sub}")
    print(f"{'=' * 70}")

    # Save results
    out_path = os.path.join(SCRIPT_DIR, 'gg2b_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return 0 if results['overall_pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
