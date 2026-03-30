#!/usr/bin/env python3
"""
Analyze mass coupling effectiveness across channels (Q3b/Q3c).

Compares:
  - M2: mass → mutation (original Q3)
  - M3: mass → Kuramoto force (Q3b)
  - M4: mass → geometric coupling (Q3c)
  - M5: combined mass coupling (Q3b + Q3c)

Outputs:
  - Coherence (corr) vs coupling strength for each channel
  - Saturation curves / diminishing returns
  - Channel comparison table
  - Summary for ROADMAP update
"""

import csv
import os
import sys
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))


def load_csv(path):
    """Load CSV, return list of dicts."""
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return list(csv.DictReader(f))


def avg_by_key(rows, key_col, val_cols):
    """Group rows by key_col, average val_cols."""
    groups = {}
    for r in rows:
        k = r[key_col].strip()
        if k not in groups:
            groups[k] = []
        groups[k].append(r)
    result = {}
    for k, rs in sorted(groups.items(), key=lambda x: float(x[0])):
        avgs = {}
        for col in val_cols:
            vals = []
            for r in rs:
                v = r.get(col, '').strip()
                if v:
                    try:
                        vals.append(float(v))
                    except ValueError:
                        pass
            avgs[col] = np.mean(vals) if vals else 0.0
            avgs[col + '_std'] = np.std(vals) if len(vals) > 1 else 0.0
        result[k] = avgs
    return result


def analyze_m2():
    """M2: mass-coupled mutation."""
    path = os.path.join(BASE, 'phase_m2_results', 'summary.csv')
    rows = load_csv(path)
    if not rows:
        print("  [M2] No data found")
        return None
    return avg_by_key(rows, 'mass_couple', ['corr', 'corr_ratio', 'mean_mass'])


def analyze_m3():
    """M3: mass-Kuramoto coupling."""
    path = os.path.join(BASE, 'phase_m3_results', 'summary.csv')
    rows = load_csv(path)
    if not rows:
        print("  [M3] No data found")
        return None
    return avg_by_key(rows, 'mass_kuramoto', ['corr', 'corr_ratio', 'mean_mass', 'mk_boosts', 'pl_events'])


def analyze_m4():
    """M4: mass-geometric coupling."""
    path = os.path.join(BASE, 'phase_m4_results', 'summary.csv')
    rows = load_csv(path)
    if not rows:
        print("  [M4] No data found")
        return None
    return avg_by_key(rows, 'mass_geo', ['corr', 'corr_ratio', 'mean_mass', 'mg_boosts', 'tp_to_tm', 'tm_to_tp'])


def analyze_m5():
    """M5: combined coupling."""
    path = os.path.join(BASE, 'phase_m5_results', 'summary.csv')
    rows = load_csv(path)
    if not rows:
        print("  [M5] No data found")
        return None
    # Group by (mk, mg, mc) tuple
    groups = {}
    for r in rows:
        key = (r['mass_kuramoto'].strip(), r['mass_geo'].strip(),
               r['mass_couple'].strip())
        if key not in groups:
            groups[key] = []
        groups[key].append(r)
    result = {}
    for key, rs in groups.items():
        corrs = [float(r['corr']) for r in rs if r.get('corr', '').strip()]
        crs = [float(r['corr_ratio']) for r in rs if r.get('corr_ratio', '').strip()]
        result[key] = {
            'corr': np.mean(corrs) if corrs else 0,
            'corr_std': np.std(corrs) if len(corrs) > 1 else 0,
            'corr_ratio': np.mean(crs) if crs else 0,
        }
    return result


def print_channel_comparison(m2, m3, m4):
    """Print side-by-side comparison of channels."""
    print("\n=== Channel Comparison: Coherence (corr) vs Coupling Strength ===\n")

    # Find baseline (coupling=0) for each
    baseline_corr = None
    if m3 and '0.0' in m3:
        baseline_corr = m3['0.0']['corr']
    elif m4 and '0.0' in m4:
        baseline_corr = m4['0.0']['corr']
    elif m2 and '0.0' in m2:
        baseline_corr = m2['0.0']['corr']

    if baseline_corr:
        print(f"Baseline (no mass coupling): corr = {baseline_corr:.4f}\n")

    print(f"{'Strength':>10s}  {'M2 (mutation)':>14s}  {'M3 (Kuramoto)':>14s}  {'M4 (geo)':>14s}")
    print("-" * 60)

    all_keys = set()
    for d in [m2, m3, m4]:
        if d:
            all_keys.update(d.keys())
    for k in sorted(all_keys, key=float):
        m2_val = f"{m2[k]['corr']:.4f}" if m2 and k in m2 else "—"
        m3_val = f"{m3[k]['corr']:.4f}" if m3 and k in m3 else "—"
        m4_val = f"{m4[k]['corr']:.4f}" if m4 and k in m4 else "—"
        print(f"{k:>10s}  {m2_val:>14s}  {m3_val:>14s}  {m4_val:>14s}")

    # Delta from baseline
    if baseline_corr:
        print(f"\n{'Δcorr':>10s}  {'M2':>14s}  {'M3':>14s}  {'M4':>14s}")
        print("-" * 60)
        for k in sorted(all_keys, key=float):
            m2_d = f"{m2[k]['corr'] - baseline_corr:+.4f}" if m2 and k in m2 else "—"
            m3_d = f"{m3[k]['corr'] - baseline_corr:+.4f}" if m3 and k in m3 else "—"
            m4_d = f"{m4[k]['corr'] - baseline_corr:+.4f}" if m4 and k in m4 else "—"
            print(f"{k:>10s}  {m2_d:>14s}  {m3_d:>14s}  {m4_d:>14s}")


def print_m3_detail(m3):
    """Detailed M3 analysis."""
    if not m3:
        return
    print("\n=== M3 Detail: Mass-Kuramoto Coupling ===\n")
    print(f"{'mk':>8s}  {'corr':>8s}  {'corr_ratio':>11s}  {'mean_mass':>10s}  {'mk_boosts':>10s}  {'pl_events':>10s}")
    print("-" * 65)
    for k in sorted(m3.keys(), key=float):
        d = m3[k]
        print(f"{k:>8s}  {d['corr']:8.4f}  {d['corr_ratio']:11.3f}  {d['mean_mass']:10.6f}  {d.get('mk_boosts', 0):10.0f}  {d.get('pl_events', 0):10.0f}")


def print_m4_detail(m4):
    """Detailed M4 analysis."""
    if not m4:
        return
    print("\n=== M4 Detail: Mass-Geometric Coupling ===\n")
    print(f"{'mg':>8s}  {'corr':>8s}  {'corr_ratio':>11s}  {'mean_mass':>10s}  {'mg_boosts':>10s}  {'tp→tm':>10s}  {'tm→tp':>10s}")
    print("-" * 80)
    for k in sorted(m4.keys(), key=float):
        d = m4[k]
        tp_tm = d.get('tp_to_tm', 0)
        tm_tp = d.get('tm_to_tp', 0)
        print(f"{k:>8s}  {d['corr']:8.4f}  {d['corr_ratio']:11.3f}  {d['mean_mass']:10.6f}  {d.get('mg_boosts', 0):10.0f}  {tp_tm:10.0f}  {tm_tp:10.0f}")


def print_m5_detail(m5):
    """Detailed M5 analysis."""
    if not m5:
        return
    print("\n=== M5 Detail: Combined Coupling ===\n")
    print(f"{'mk':>6s}  {'mg':>6s}  {'mc':>6s}  {'corr':>8s}  {'corr_std':>9s}  {'corr_ratio':>11s}")
    print("-" * 55)
    for key in sorted(m5.keys()):
        mk, mg, mc = key
        d = m5[key]
        label = "  ← TRIPLE" if float(mc) > 0 else ""
        print(f"{mk:>6s}  {mg:>6s}  {mc:>6s}  {d['corr']:8.4f}  {d['corr_std']:9.4f}  {d['corr_ratio']:11.3f}{label}")


def main():
    print("=" * 70)
    print("Mass Coupling Effectiveness Analysis (Q3b/Q3c)")
    print("=" * 70)

    m2 = analyze_m2()
    m3 = analyze_m3()
    m4 = analyze_m4()
    m5 = analyze_m5()

    if not any([m2, m3, m4, m5]):
        print("\nNo data found. Run the sweep scripts first:")
        print("  bash phase_m3_mass_kuramoto.sh")
        print("  bash phase_m4_mass_geo.sh")
        print("  bash phase_m5_mass_combined.sh")
        sys.exit(1)

    print_channel_comparison(m2, m3, m4)
    print_m3_detail(m3)
    print_m4_detail(m4)
    print_m5_detail(m5)

    # Summary verdict
    print("\n=== Summary ===\n")
    best_channel = "unknown"
    best_delta = 0
    channels = []
    if m3:
        baseline = m3.get('0.0', {}).get('corr', 0)
        best_m3 = max((d['corr'] for d in m3.values()), default=0)
        delta_m3 = best_m3 - baseline
        channels.append(('M3 (Kuramoto)', delta_m3, best_m3))
    if m4:
        baseline = m4.get('0.0', {}).get('corr', 0)
        best_m4 = max((d['corr'] for d in m4.values()), default=0)
        delta_m4 = best_m4 - baseline
        channels.append(('M4 (geo)', delta_m4, best_m4))
    if m2:
        baseline = m2.get('0.0', {}).get('corr', 0)
        best_m2 = max((d['corr'] for d in m2.values()), default=0)
        delta_m2 = best_m2 - baseline
        channels.append(('M2 (mutation)', delta_m2, best_m2))

    for name, delta, best in sorted(channels, key=lambda x: -x[1]):
        verdict = "EFFECTIVE" if delta > 0.01 else "MINIMAL" if delta > 0.001 else "NEGLIGIBLE"
        print(f"  {name:20s}: Δcorr = {delta:+.4f}  (peak corr = {best:.4f})  [{verdict}]")

    if m5:
        best_combined = max((d['corr'] for d in m5.values()), default=0)
        print(f"\n  Best combined (M5): corr = {best_combined:.4f}")


if __name__ == '__main__':
    main()
