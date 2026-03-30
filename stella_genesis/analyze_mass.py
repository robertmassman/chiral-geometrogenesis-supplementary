#!/usr/bin/env python3
"""
Analyze phase-gradient mass observable from genesis_soup output.

Parses the 'mass:' diagnostic lines and plots the evolution of
mass density, phase gradients, and spatial correlation over epochs.

Usage:
    python3 analyze_mass.py < genesis_output.log
    python3 analyze_mass.py genesis_output.log
    ./genesis_soup ... | python3 analyze_mass.py

Related Documents:
- Theorem 3.1.1: Phase-Gradient Mass Generation
- Prop 0.0.17l: ω₀ = 220 MeV
- Prop 0.0.17m: v_χ = 88.0 MeV
- Prop 3.1.1c: g_χ = 4π/9

Verification Date: 2026-03-23
"""

import sys
import re
import json
from datetime import datetime

def parse_output(lines):
    """Parse genesis_soup stdout for epoch + mass diagnostic lines."""
    data = []
    current_epoch = 0

    epoch_re = re.compile(r'epoch=(\d+)')
    mass_re = re.compile(
        r'mass:\s+mean=([\d.]+)\s+std=([\d.]+)\s+max=([\d.]+)\s+'
        r'\|grad_phi\|=([\d.]+)\s+v_chi=([\d.]+)\s+corr_ratio=([\d.]+)'
    )

    for line in lines:
        em = epoch_re.search(line)
        if em:
            current_epoch = int(em.group(1))

        mm = mass_re.search(line)
        if mm:
            data.append({
                'epoch': current_epoch,
                'mean_mass': float(mm.group(1)),
                'std_mass': float(mm.group(2)),
                'max_mass': float(mm.group(3)),
                'grad_phi': float(mm.group(4)),
                'v_chi': float(mm.group(5)),
                'corr_ratio': float(mm.group(6)),
            })

    return data


def analyze(data):
    """Compute summary statistics and trends."""
    if len(data) < 2:
        return {'error': 'Need at least 2 data points'}

    initial = data[0]
    final = data[-1]

    # Mass evolution trend: linear regression of mean_mass vs epoch
    n = len(data)
    sx = sum(d['epoch'] for d in data)
    sy = sum(d['mean_mass'] for d in data)
    sxy = sum(d['epoch'] * d['mean_mass'] for d in data)
    sxx = sum(d['epoch']**2 for d in data)
    denom = n * sxx - sx * sx
    if denom > 0:
        slope = (n * sxy - sx * sy) / denom
    else:
        slope = 0.0

    # Gradient decrease (signature of synchronization → mass reduction)
    grad_decrease = (initial['grad_phi'] - final['grad_phi']) / initial['grad_phi']

    # Correlation ratio increase (mass clustering)
    corr_change = final['corr_ratio'] - initial['corr_ratio']

    # Physical scale conversion:
    # On the lattice, mass is in units of MASS_PREFACTOR * v_chi_norm * |∇φ|
    # To convert to MeV: multiply by v_χ = 88.0 MeV (the VEV scale)
    V_CHI_MEV = 88.0  # MeV, from Prop 0.0.17m
    mass_scale_mev = final['mean_mass'] * V_CHI_MEV

    return {
        'n_points': n,
        'epochs_total': final['epoch'],
        'initial_mean_mass': initial['mean_mass'],
        'final_mean_mass': final['mean_mass'],
        'mass_trend_slope': slope,
        'mass_trend_direction': 'decreasing' if slope < 0 else 'increasing',
        'grad_phi_decrease_pct': grad_decrease * 100,
        'initial_grad_phi': initial['grad_phi'],
        'final_grad_phi': final['grad_phi'],
        'initial_corr_ratio': initial['corr_ratio'],
        'final_corr_ratio': final['corr_ratio'],
        'corr_ratio_change': corr_change,
        'v_chi': final['v_chi'],
        'mass_scale_estimate_mev': mass_scale_mev,
        'interpretation': {
            'grad_decrease': (
                'Phase gradients decreased — Kuramoto sync reducing ∇φ. '
                'This is the expected behavior: synchronization → less mass.'
                if grad_decrease > 0.02 else
                'Phase gradients roughly stable — phases not strongly synchronizing.'
            ),
            'corr_ratio': (
                'Mass is spatially clustered (corr_ratio > 1) — '
                'mass-like structure has spatial organization.'
                if final['corr_ratio'] > 1.01 else
                'Mass is spatially uniform — no emergent mass clustering.'
            ),
        }
    }


def main():
    # Read from file or stdin
    if len(sys.argv) > 1 and sys.argv[1] != '-':
        with open(sys.argv[1]) as f:
            lines = f.readlines()
    else:
        lines = sys.stdin.readlines()

    data = parse_output(lines)

    if not data:
        print("ERROR: No mass diagnostic lines found in input.")
        print("Ensure genesis_soup was run with mass_mode=1 (argv[16]=1)")
        sys.exit(1)

    analysis = analyze(data)

    # Print summary
    print("=" * 60)
    print("Phase-Gradient Mass Observable Analysis (Thm 3.1.1)")
    print("=" * 60)
    print(f"Data points: {analysis['n_points']}")
    print(f"Epochs: {analysis['epochs_total']}")
    print()
    print("--- Mass Density ---")
    print(f"  Initial mean: {analysis['initial_mean_mass']:.6f}")
    print(f"  Final mean:   {analysis['final_mean_mass']:.6f}")
    print(f"  Trend:        {analysis['mass_trend_direction']} "
          f"(slope={analysis['mass_trend_slope']:.2e})")
    print()
    print("--- Phase Gradient |∇φ| ---")
    print(f"  Initial: {analysis['initial_grad_phi']:.4f}")
    print(f"  Final:   {analysis['final_grad_phi']:.4f}")
    print(f"  Change:  {analysis['grad_phi_decrease_pct']:+.1f}%")
    print(f"  → {analysis['interpretation']['grad_decrease']}")
    print()
    print("--- Spatial Clustering ---")
    print(f"  Initial corr_ratio: {analysis['initial_corr_ratio']:.3f}")
    print(f"  Final corr_ratio:   {analysis['final_corr_ratio']:.3f}")
    print(f"  → {analysis['interpretation']['corr_ratio']}")
    print()
    print("--- Physical Scale Estimate ---")
    print(f"  v_χ = 88.0 MeV (Prop 0.0.17m)")
    print(f"  Lattice mass × v_χ ≈ {analysis['mass_scale_estimate_mev']:.1f} MeV")
    print(f"  (This is a rough lattice→physical conversion, not a precision prediction)")
    print()

    # Save JSON results
    results = {
        'theorem': '3.1.1',
        'title': 'Phase-Gradient Mass Observable (Genesis Soup)',
        'timestamp': datetime.now().isoformat(),
        'data': data,
        'analysis': analysis,
    }
    outfile = 'mass_observable_results.json'
    with open(outfile, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Results saved to {outfile}")


if __name__ == '__main__':
    main()
