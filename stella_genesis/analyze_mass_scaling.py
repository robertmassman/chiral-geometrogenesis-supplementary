#!/usr/bin/env python3
"""
Q4: Mass scaling analysis — does η ≈ 2/3 connect to mass dynamics?

Parses time-series output from genesis_soup runs (epoch, mass, autocorr,
grad_phi) and fits power-law relationships:
  - mass ∝ |∇φ|^α
  - mass ∝ (1 - autocorr)^η

Compares fitted η to the 2/3 threshold in the pressure SENSE gate.

Usage:
    python3 analyze_mass_scaling.py phase_m1_results/*.log
    python3 analyze_mass_scaling.py single_run.log

Related: Theorem 3.1.1, Def 0.1.3 (SENSE gate 2/3 threshold)
"""

import sys
import re
import os
import json
import numpy as np
from datetime import datetime


def parse_timeseries(lines):
    """Extract epoch-by-epoch data from genesis_soup output."""
    records = []
    current_epoch = 0
    current_corr = 0
    current_auto_tp = 0

    epoch_re = re.compile(
        r'epoch=(\d+)\s+.*corr=([\d.]+).*auto_tp=([\d.]+)'
    )
    mass_re = re.compile(
        r'mass:\s+mean=([\d.]+)\s+std=([\d.]+)\s+max=([\d.]+)\s+'
        r'\|grad_phi\|=([\d.]+)\s+v_chi=([\d.]+)\s+corr_ratio=([\d.]+)'
    )

    for line in lines:
        em = epoch_re.search(line)
        if em:
            current_epoch = int(em.group(1))
            current_corr = float(em.group(2))
            current_auto_tp = float(em.group(3))

        mm = mass_re.search(line)
        if mm:
            records.append({
                'epoch': current_epoch,
                'corr': current_corr,
                'auto_tp': current_auto_tp,
                'mean_mass': float(mm.group(1)),
                'std_mass': float(mm.group(2)),
                'max_mass': float(mm.group(3)),
                'grad_phi': float(mm.group(4)),
                'v_chi': float(mm.group(5)),
                'corr_ratio': float(mm.group(6)),
            })

    return records


def fit_power_law(x, y, label=''):
    """Fit y = a * x^eta via log-log linear regression.
    Returns (eta, a, r_squared, log_residuals)."""
    # Filter positive values
    mask = (x > 0) & (y > 0) & np.isfinite(x) & np.isfinite(y)
    if mask.sum() < 3:
        return None

    lx = np.log(x[mask])
    ly = np.log(y[mask])

    # Linear regression in log space
    n = len(lx)
    sx = np.sum(lx)
    sy = np.sum(ly)
    sxx = np.sum(lx**2)
    sxy = np.sum(lx * ly)

    denom = n * sxx - sx**2
    if abs(denom) < 1e-15:
        return None

    eta = (n * sxy - sx * sy) / denom
    log_a = (sy - eta * sx) / n
    a = np.exp(log_a)

    # R²
    y_pred = log_a + eta * lx
    ss_res = np.sum((ly - y_pred)**2)
    ss_tot = np.sum((ly - np.mean(ly))**2)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

    # Standard error of eta
    if n > 2 and denom > 0:
        mse = ss_res / (n - 2)
        se_eta = np.sqrt(mse * n / denom)
    else:
        se_eta = float('inf')

    return {
        'label': label,
        'eta': float(eta),
        'a': float(a),
        'r_squared': float(r2),
        'se_eta': float(se_eta),
        'n_points': int(mask.sum()),
        'eta_95ci': (float(eta - 1.96*se_eta), float(eta + 1.96*se_eta)),
    }


def analyze_single(records, source=''):
    """Analyze scaling relationships in a single time series."""
    if len(records) < 4:
        return None

    epochs = np.array([r['epoch'] for r in records])
    mass = np.array([r['mean_mass'] for r in records])
    grad = np.array([r['grad_phi'] for r in records])
    auto = np.array([r['auto_tp'] for r in records])
    corr = np.array([r['corr'] for r in records])

    results = {'source': source, 'n_records': len(records)}

    # Fit 1: mass ∝ |∇φ|^α
    fit_grad = fit_power_law(grad, mass, 'mass vs |∇φ|')
    results['fit_mass_vs_grad'] = fit_grad

    # Fit 2: mass ∝ (1 - autocorr)^η
    disorder = 1.0 - auto  # high autocorr → low disorder → less mass
    fit_disorder = fit_power_law(disorder, mass, 'mass vs (1-auto_tp)')
    results['fit_mass_vs_disorder'] = fit_disorder

    # Fit 3: |∇φ| ∝ (1 - autocorr)^β
    fit_grad_disorder = fit_power_law(disorder, grad, '|∇φ| vs (1-auto_tp)')
    results['fit_grad_vs_disorder'] = fit_grad_disorder

    return results


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyze_mass_scaling.py <log_file(s)>")
        sys.exit(1)

    all_results = []
    all_records = []

    for filepath in sys.argv[1:]:
        if not os.path.exists(filepath):
            print(f"Skipping {filepath} (not found)")
            continue

        with open(filepath) as f:
            lines = f.readlines()

        records = parse_timeseries(lines)
        if not records:
            print(f"Skipping {filepath} (no mass data)")
            continue

        result = analyze_single(records, source=os.path.basename(filepath))
        if result:
            all_results.append(result)
            all_records.extend(records)

    if not all_results:
        print("ERROR: No usable data found.")
        sys.exit(1)

    print("=" * 65)
    print("Q4: Mass Scaling Analysis — η Exponent Fitting (Thm 3.1.1)")
    print("=" * 65)
    print(f"Files analyzed: {len(all_results)}")
    print(f"Total data points: {sum(r['n_records'] for r in all_results)}")
    print()

    # Report per-file fits
    for r in all_results:
        print(f"--- {r['source']} ({r['n_records']} points) ---")
        for key, label in [
            ('fit_mass_vs_grad', 'mass ∝ |∇φ|^α'),
            ('fit_mass_vs_disorder', 'mass ∝ (1-auto)^η'),
            ('fit_grad_vs_disorder', '|∇φ| ∝ (1-auto)^β'),
        ]:
            fit = r.get(key)
            if fit:
                exp_name = 'α' if 'grad' in key and 'disorder' not in key else \
                           'η' if 'disorder' in key and 'grad' not in key else 'β'
                ci = fit['eta_95ci']
                print(f"  {label}:  {exp_name} = {fit['eta']:.4f} ± {fit['se_eta']:.4f}  "
                      f"R² = {fit['r_squared']:.4f}  (95% CI: [{ci[0]:.3f}, {ci[1]:.3f}])")
            else:
                print(f"  {label}:  insufficient data")
        print()

    # Aggregate: fit across all records pooled
    if len(all_records) >= 5:
        print("=== Pooled Fit (all runs combined) ===")
        pooled = analyze_single(all_records, source='POOLED')
        if pooled:
            for key, label, exp in [
                ('fit_mass_vs_grad', 'mass ∝ |∇φ|^α', 'α'),
                ('fit_mass_vs_disorder', 'mass ∝ (1-auto)^η', 'η'),
                ('fit_grad_vs_disorder', '|∇φ| ∝ (1-auto)^β', 'β'),
            ]:
                fit = pooled.get(key)
                if fit:
                    ci = fit['eta_95ci']
                    print(f"  {label}:  {exp} = {fit['eta']:.4f} ± {fit['se_eta']:.4f}  "
                          f"R² = {fit['r_squared']:.4f}")
        print()

    # Compare to 2/3
    print("=== Comparison to η = 2/3 ===")
    key_fit = all_results[0].get('fit_mass_vs_disorder') if all_results else None
    if key_fit:
        eta = key_fit['eta']
        target = 2/3
        print(f"  Fitted η = {eta:.4f}")
        print(f"  Target (2/3 from SENSE gate) = {target:.4f}")
        print(f"  Difference: {abs(eta - target):.4f}")
        if key_fit['se_eta'] < float('inf'):
            t_stat = abs(eta - target) / key_fit['se_eta']
            consistent = t_stat < 2.0
            print(f"  t-statistic: {t_stat:.2f} "
                  f"({'consistent' if consistent else 'inconsistent'} at 95% level)")
    print()

    # Save
    output = {
        'theorem': '3.1.1',
        'question': 'Q4',
        'title': 'Mass scaling exponent analysis',
        'timestamp': datetime.now().isoformat(),
        'per_file': all_results,
        'reference_eta': 2/3,
    }
    outfile = 'mass_scaling_results.json'
    with open(outfile, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"Results saved to {outfile}")


if __name__ == '__main__':
    main()
