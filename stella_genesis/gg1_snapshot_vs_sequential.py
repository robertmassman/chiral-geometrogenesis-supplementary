#!/usr/bin/env python3
"""
GG1: Snapshot vs Sequential — Genesis Dynamics GPU Readiness Test
=================================================================

Tests whether Genesis correlation dynamics survive GPU snapshot execution
semantics (all reads from epoch-start state) vs CPU sequential execution
(each update immediately visible).

Uses the definitive G1 configuration:
  WRITE (instr_mode=2), χ=0.15, cs=0.7, ε=0.1, μ=0.001
  + color_pressure=1, phase_lock=0.1, kuramoto_mode=1

Sweeps n_sub = {16, 32, 64}, comparing sequential (snapshot_mode=0) vs
snapshot (snapshot_mode=1).

Pass criterion: GPU correlation within 5% of CPU at each resolution.

Outputs gg1_results.json.
"""

import subprocess
import re
import json
import os
import sys
import time
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BINARY = os.path.join(SCRIPT_DIR, 'genesis_soup')
SOURCE = os.path.join(SCRIPT_DIR, 'genesis_soup.c')

# G1 definitive configuration
EPOCHS = 2000000       # 2M epochs (sufficient for convergence)
SEED = 42
CS = 0.7               # coupling_strength
MODE = 0               # VM+coupling
MU = 0.001             # mutation_rate
EPS = 0.1              # epsilon
CHI = 0.15             # chirality
CHI_MODE = 0           # pressure-asymmetry
INSTR_MODE = 2         # WRITE mode
WARP = 1.0             # uniform mesh
COLOR_PRESSURE = 1     # per-color WRITE gate
PHASE_LOCK = 0.1       # Kuramoto coupling K
KURAMOTO = 1           # full Kuramoto (continuous phase)
ENERGY_LAMBDA = 0      # energy functional off for base GG1
MASS_MODE = 0          # mass observable off

N_SUBS = [16, 32, 64]


def compile_binary():
    """Compile genesis_soup.c."""
    print("Compiling genesis_soup.c...")
    result = subprocess.run(
        ['cc', '-O3', '-o', BINARY, SOURCE, '-lm'],
        capture_output=True, text=True, cwd=SCRIPT_DIR
    )
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("Compilation successful.\n")


def build_command(n_sub, snapshot_mode):
    """Build the genesis_soup command line."""
    return [
        BINARY,
        str(EPOCHS), str(SEED), str(CS), str(MODE), str(n_sub),
        str(MU), str(EPS), str(CHI), str(CHI_MODE), str(INSTR_MODE),
        str(WARP), str(COLOR_PRESSURE), str(PHASE_LOCK), str(KURAMOTO),
        str(ENERGY_LAMBDA), str(MASS_MODE), '0', str(snapshot_mode)
    ]


def parse_output(text):
    """Parse genesis_soup stdout for key metrics."""
    metrics = {}

    # Parse final state epoch line
    final_section = False
    for line in text.split('\n'):
        if '=== Final State ===' in line:
            final_section = True
            continue
        if final_section and line.startswith('epoch='):
            # epoch=2000000  H_tp=1.4693 H_tm=1.4174  corr=0.8833  chi2=0.1031  ...
            m = re.search(r'corr=([\d.]+)', line)
            if m:
                metrics['correlation'] = float(m.group(1))
            m = re.search(r'chi2=([\d.]+)', line)
            if m:
                metrics['chi2'] = float(m.group(1))
            m = re.search(r'auto_tp=([\d.]+)', line)
            if m:
                metrics['auto_tp'] = float(m.group(1))
            m = re.search(r'auto_tm=([\d.]+)', line)
            if m:
                metrics['auto_tm'] = float(m.group(1))
            m = re.search(r'H_tp=([\d.]+)', line)
            if m:
                metrics['entropy_tp'] = float(m.group(1))
            m = re.search(r'H_tm=([\d.]+)', line)
            if m:
                metrics['entropy_tm'] = float(m.group(1))
            break

    # WRITE success rate
    m = re.search(r'WRITE success rate:\s+([\d.]+)%', text)
    if m:
        metrics['write_success_rate'] = float(m.group(1))

    # WRITE counts
    m = re.search(r'WRITE succeeded:\s+(\d+)', text)
    if m:
        metrics['write_count'] = int(m.group(1))
    m = re.search(r'WRITE blocked.*:\s+(\d+)', text)
    if m:
        metrics['write_blocked'] = int(m.group(1))

    # Phase-lock nudges
    m = re.search(r'Phase-lock nudges:\s+(\d+)', text)
    if m:
        metrics['phase_lock_nudges'] = int(m.group(1))

    # Correlation by P_ratio bins (deep-blocked zone)
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

    # Parse convergence trajectory (periodic reports)
    trajectory = []
    for line in text.split('\n'):
        if line.startswith('epoch=') and 'Final' not in text.split(line)[0].split('\n')[-1]:
            m_e = re.search(r'epoch=(\d+)', line)
            m_c = re.search(r'corr=([\d.]+)', line)
            m_x = re.search(r'chi2=([\d.]+)', line)
            if m_e and m_c:
                trajectory.append({
                    'epoch': int(m_e.group(1)),
                    'corr': float(m_c.group(1)),
                    'chi2': float(m_x.group(1)) if m_x else None
                })
    metrics['trajectory'] = trajectory

    return metrics


def run_test(n_sub, snapshot_mode):
    """Run genesis_soup and parse output."""
    mode_name = "snapshot" if snapshot_mode else "sequential"
    print(f"  Running n_sub={n_sub}, mode={mode_name}...", end=' ', flush=True)

    cmd = build_command(n_sub, snapshot_mode)
    t0 = time.time()
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=SCRIPT_DIR)
    elapsed = time.time() - t0

    if result.returncode != 0:
        print(f"FAILED (exit code {result.returncode})")
        print(result.stderr[:500])
        return None

    metrics = parse_output(result.stdout)
    metrics['wall_clock_s'] = round(elapsed, 1)
    print(f"corr={metrics.get('correlation', '?'):.4f} "
          f"chi2={metrics.get('chi2', '?'):.4f} "
          f"write={metrics.get('write_success_rate', '?'):.1f}% "
          f"({elapsed:.1f}s)")
    return metrics


def compute_deep_blocked_rate(metrics):
    """Extract the deep-blocked zone ([0.30,0.40)) match rate."""
    bins = metrics.get('pratio_bins', {})
    for key, val in bins.items():
        if key.startswith('[0.30'):
            return val['match_rate']
    # Fallback: average of all blocked bins
    blocked = [v['match_rate'] for v in bins.values() if v['gate'] == 'blocked']
    return sum(blocked) / len(blocked) if blocked else None


def main():
    compile_binary()

    results = {
        'test': 'GG1',
        'description': 'Snapshot vs Sequential — Genesis Dynamics GPU Readiness',
        'timestamp': datetime.now().isoformat(),
        'config': {
            'epochs': EPOCHS, 'seed': SEED, 'coupling_strength': CS,
            'mutation_rate': MU, 'epsilon': EPS, 'chirality': CHI,
            'instr_mode': INSTR_MODE, 'color_pressure': COLOR_PRESSURE,
            'phase_lock': PHASE_LOCK, 'kuramoto_mode': KURAMOTO,
        },
        'comparisons': [],
        'pass_criterion': 'GPU correlation within 5% of CPU at each resolution',
    }

    all_pass = True

    for n_sub in N_SUBS:
        print(f"\n=== n_sub={n_sub} ===")

        seq = run_test(n_sub, snapshot_mode=0)
        snap = run_test(n_sub, snapshot_mode=1)

        if not seq or not snap:
            print(f"  SKIPPED (run failed)")
            continue

        # Compute deltas
        corr_seq = seq['correlation']
        corr_snap = snap['correlation']
        corr_delta = abs(corr_snap - corr_seq)
        corr_pct = corr_delta / corr_seq * 100 if corr_seq > 0 else float('inf')

        chi2_seq = seq.get('chi2', 0)
        chi2_snap = snap.get('chi2', 0)

        deep_seq = compute_deep_blocked_rate(seq)
        deep_snap = compute_deep_blocked_rate(snap)

        write_seq = seq.get('write_success_rate', 0)
        write_snap = snap.get('write_success_rate', 0)

        # Pass/fail per criterion
        corr_pass = corr_pct < 5.0

        comparison = {
            'n_sub': n_sub,
            'sequential': {
                'correlation': corr_seq,
                'chi2': chi2_seq,
                'deep_blocked_rate': deep_seq,
                'write_success_rate': write_seq,
                'phase_lock_nudges': seq.get('phase_lock_nudges'),
                'auto_tp': seq.get('auto_tp'),
                'auto_tm': seq.get('auto_tm'),
                'wall_clock_s': seq.get('wall_clock_s'),
            },
            'snapshot': {
                'correlation': corr_snap,
                'chi2': chi2_snap,
                'deep_blocked_rate': deep_snap,
                'write_success_rate': write_snap,
                'phase_lock_nudges': snap.get('phase_lock_nudges'),
                'auto_tp': snap.get('auto_tp'),
                'auto_tm': snap.get('auto_tm'),
                'wall_clock_s': snap.get('wall_clock_s'),
            },
            'delta': {
                'correlation_abs': round(corr_delta, 6),
                'correlation_pct': round(corr_pct, 2),
                'chi2_abs': round(abs(chi2_snap - chi2_seq), 6),
                'deep_blocked_delta': round(abs(deep_snap - deep_seq), 4) if deep_seq and deep_snap else None,
                'write_rate_delta': round(abs(write_snap - write_seq), 1),
            },
            'pass': corr_pass,
        }
        results['comparisons'].append(comparison)

        if not corr_pass:
            all_pass = False

        # Print summary
        print(f"\n  {'Metric':<25} {'Sequential':>12} {'Snapshot':>12} {'Delta':>10} {'Pass':>6}")
        print(f"  {'-'*65}")
        print(f"  {'T+↔T- correlation':<25} {corr_seq:>12.4f} {corr_snap:>12.4f} "
              f"{corr_pct:>9.2f}% {'✓' if corr_pass else '✗':>5}")
        print(f"  {'|χ|²':<25} {chi2_seq:>12.4f} {chi2_snap:>12.4f} "
              f"{abs(chi2_snap - chi2_seq):>10.4f}")
        if deep_seq and deep_snap:
            print(f"  {'Deep-blocked rate':<25} {deep_seq:>12.4f} {deep_snap:>12.4f} "
                  f"{abs(deep_snap - deep_seq):>10.4f}")
        print(f"  {'WRITE success rate':<25} {write_seq:>11.1f}% {write_snap:>11.1f}% "
              f"{abs(write_snap - write_seq):>9.1f}%")
        print(f"  {'Phase-lock nudges':<25} {seq.get('phase_lock_nudges', 0):>12d} "
              f"{snap.get('phase_lock_nudges', 0):>12d}")

    results['overall_pass'] = all_pass

    # Save results
    out_path = os.path.join(SCRIPT_DIR, 'gg1_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    # Final verdict
    print(f"\n{'='*60}")
    if all_pass:
        print("GG1 PASSED: Snapshot correlation within 5% of sequential at all resolutions.")
        print("Genesis dynamics are confirmed snapshot-robust → GPU port is viable.")
    else:
        failed = [c for c in results['comparisons'] if not c['pass']]
        print(f"GG1 FAILED at {len(failed)} resolution(s):")
        for c in failed:
            print(f"  n_sub={c['n_sub']}: correlation delta = {c['delta']['correlation_pct']:.2f}%")
        print("Proceed to GG3 (Kuramoto isolation) to identify snapshot-sensitive mechanism.")
    print(f"{'='*60}")

    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
