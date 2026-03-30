#!/usr/bin/env python3
"""
Phase M6: Long-run convergence analysis (Q6 + Q7)

Q6: Does combined coupling (mk=5, mg=5) close the coherence gap with longer runs?
    - Extracts coherence time series from periodic log reports
    - Tests whether coherence is still rising or has plateaued

Q7: Does the 73.5% color-vertex fraction converge to 2/3 or 3/4 long-term?
    - Loads mass_geography.json for each run length
    - Computes color-vertex mass fraction per epoch count
    - Tests convergence toward theoretical targets

References:
- Q3d baseline: corr=0.816 at (mk=5, mg=5) for 2M epochs
- Q4b baseline: 73.5% color-vertex fraction at 2M epochs
- Theoretical targets: 2/3 ≈ 0.667, 3/4 = 0.75
"""

import os
import re
import json
import glob
import csv
import sys
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(BASE, 'phase_m6_results')


# ── Q6: Coherence convergence from log time series ──────────────────

def parse_log_timeseries(logfile):
    """Extract (epoch, corr, mass_mean, mass_corr_ratio) from periodic reports."""
    epochs, corrs, mass_means, mass_corr_ratios = [], [], [], []

    with open(logfile) as f:
        for line in f:
            # epoch= lines contain corr
            m = re.match(r'epoch=(\d+)\s.*corr=([0-9.]+)', line)
            if m:
                epochs.append(int(m.group(1)))
                corrs.append(float(m.group(2)))

            # mass: lines contain mean and corr_ratio
            m2 = re.match(r'\s*mass:\s*mean=([0-9.]+)\s.*corr_ratio=([0-9.]+)', line)
            if m2:
                mass_means.append(float(m2.group(1)))
                mass_corr_ratios.append(float(m2.group(2)))

    return {
        'epochs': np.array(epochs),
        'corr': np.array(corrs),
        'mass_mean': np.array(mass_means),
        'mass_corr_ratio': np.array(mass_corr_ratios),
    }


def analyze_coherence_convergence():
    """Q6: Is coherence still rising at long times?"""
    print("=" * 70)
    print("Q6: Coherence Convergence with Run Length")
    print("=" * 70)

    # Load summary CSV
    summary_file = os.path.join(OUTDIR, 'summary.csv')
    if not os.path.exists(summary_file):
        print(f"ERROR: {summary_file} not found. Run phase_m6_long_convergence.sh first.")
        return False

    rows = []
    with open(summary_file) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    # Group by epoch count
    epoch_groups = {}
    for row in rows:
        e = int(row['epochs'])
        if e not in epoch_groups:
            epoch_groups[e] = []
        epoch_groups[e].append(row)

    print(f"\n{'Epochs':>12s}  {'corr_mean':>10s}  {'corr_std':>9s}  "
          f"{'corr_ratio':>11s}  {'mean_mass':>10s}")
    print("-" * 60)

    epoch_list = sorted(epoch_groups.keys())
    corr_means = []
    for e in epoch_list:
        group = epoch_groups[e]
        corrs = [float(r['corr']) for r in group]
        crs = [float(r['corr_ratio']) for r in group]
        masses = [float(r['mean_mass']) for r in group]
        cm = np.mean(corrs)
        cs = np.std(corrs)
        corr_means.append(cm)
        print(f"{e:12d}  {cm:10.4f}  {cs:9.4f}  "
              f"{np.mean(crs):11.3f}  {np.mean(masses):10.6f}")

    # Trend analysis
    if len(epoch_list) >= 3:
        log_e = np.log10(np.array(epoch_list, dtype=float))
        cm_arr = np.array(corr_means)
        coeffs = np.polyfit(log_e, cm_arr, 1)
        print(f"\nLinear fit (corr vs log₁₀(epochs)): slope = {coeffs[0]:.4f}")
        if coeffs[0] > 0.005:
            print("  → Coherence is STILL RISING — longer runs would help")
        elif coeffs[0] > 0:
            print("  → Coherence rising slowly — approaching plateau")
        else:
            print("  → Coherence has PLATEAUED or is declining")

    # Time series from individual logs
    print("\n--- Coherence time-series snapshots (last 5 reports per run) ---\n")
    for e in epoch_list:
        for seed in [42, 123, 7]:
            logfile = os.path.join(OUTDIR, f'E{e}_S{seed}.log')
            if not os.path.exists(logfile):
                continue
            ts = parse_log_timeseries(logfile)
            if len(ts['corr']) >= 5:
                last5 = ts['corr'][-5:]
                trend = last5[-1] - last5[0]
                print(f"  E={e:>10d} S={seed}: last 5 corr = "
                      f"[{', '.join(f'{c:.4f}' for c in last5)}]  "
                      f"Δ={trend:+.4f}")

    return True


# ── Q7: Color-vertex fraction convergence ────────────────────────────

def compute_color_vertex_fraction(geofile):
    """Compute fraction of total mass in color vertices (V1+V2+V3) for both surfaces."""
    with open(geofile) as f:
        data = json.load(f)

    fractions = []
    for surface in ['tp', 'tm']:
        mass = np.array(data[f'mass_{surface}'])
        pos = np.array(data[f'{surface}_pos'])
        vertices = np.array(data['tv_plus'] if surface == 'tp' else data['tv_minus'])

        n_sites = len(mass)
        # Assign each site to nearest vertex
        assignments = np.zeros(n_sites, dtype=int)
        for i in range(n_sites):
            dists = np.linalg.norm(pos[i] - vertices, axis=1)
            assignments[i] = np.argmin(dists)

        # Color vertices are V1, V2, V3 (V0 is the origin vertex)
        vertex_masses = np.array([mass[assignments == v].sum() for v in range(4)])
        total = mass.sum()
        if total > 0:
            color_frac = vertex_masses[1:].sum() / total
            fractions.append(color_frac)

            # Z₃ symmetry: CV of color vertex masses
            cv = vertex_masses[1:].std() / vertex_masses[1:].mean() if vertex_masses[1:].mean() > 0 else float('inf')
        else:
            fractions.append(0.0)

    return np.mean(fractions)


def analyze_vertex_fraction_convergence():
    """Q7: Does color-vertex fraction converge to 2/3 or 3/4?"""
    print("\n" + "=" * 70)
    print("Q7: Color-Vertex Mass Fraction Convergence")
    print("=" * 70)

    # Find all geography files
    geo_files = sorted(glob.glob(os.path.join(OUTDIR, 'E*_geography.json')))
    if not geo_files:
        print(f"ERROR: No geography files found in {OUTDIR}/")
        print("Run phase_m6_long_convergence.sh first.")
        return False

    # Parse epoch and seed from filenames
    results = []
    for gf in geo_files:
        basename = os.path.basename(gf)
        m = re.match(r'E(\d+)_S(\d+)_geography\.json', basename)
        if not m:
            continue
        epoch = int(m.group(1))
        seed = int(m.group(2))
        frac = compute_color_vertex_fraction(gf)
        results.append((epoch, seed, frac))

    if not results:
        print("No valid geography files found.")
        return False

    # Group by epoch
    epoch_fracs = {}
    for epoch, seed, frac in results:
        if epoch not in epoch_fracs:
            epoch_fracs[epoch] = []
        epoch_fracs[epoch].append(frac)

    print(f"\n{'Epochs':>12s}  {'frac_mean':>10s}  {'frac_std':>9s}  "
          f"{'Δ from 2/3':>10s}  {'Δ from 3/4':>10s}")
    print("-" * 58)

    epoch_list = sorted(epoch_fracs.keys())
    frac_means = []
    for e in epoch_list:
        fracs = epoch_fracs[e]
        fm = np.mean(fracs)
        fs = np.std(fracs)
        frac_means.append(fm)
        d23 = fm - 2/3
        d34 = fm - 3/4
        print(f"{e:12d}  {fm:10.4f}  {fs:9.4f}  "
              f"{d23:+10.4f}  {d34:+10.4f}")

    # Convergence analysis
    if len(epoch_list) >= 2:
        fm_arr = np.array(frac_means)
        print(f"\n  Range: [{fm_arr.min():.4f}, {fm_arr.max():.4f}]")
        print(f"  Span: {fm_arr.max() - fm_arr.min():.4f}")

        # Which target is closer?
        d23_final = abs(fm_arr[-1] - 2/3)
        d34_final = abs(fm_arr[-1] - 3/4)
        closer = "2/3" if d23_final < d34_final else "3/4"
        print(f"  Longest-run fraction: {fm_arr[-1]:.4f}")
        print(f"  Closer to: {closer} (distance: {min(d23_final, d34_final):.4f})")

        # Trend: is it moving toward a target?
        if len(epoch_list) >= 3:
            log_e = np.log10(np.array(epoch_list, dtype=float))
            coeffs = np.polyfit(log_e, fm_arr, 1)
            print(f"\n  Linear fit (frac vs log₁₀(epochs)): slope = {coeffs[0]:+.4f}")
            if abs(coeffs[0]) < 0.005:
                print(f"  → Fraction has CONVERGED near {fm_arr[-1]:.3f}")
            elif coeffs[0] > 0:
                print(f"  → Fraction is RISING toward 3/4")
            else:
                print(f"  → Fraction is FALLING toward 2/3")

    return True


# ── Per-run detailed geography analysis ──────────────────────────────

def detailed_geography_report():
    """Extended QCD analysis per geography file."""
    print("\n" + "=" * 70)
    print("Detailed Geography: Per-Run Vertex Mass Budgets")
    print("=" * 70)

    geo_files = sorted(glob.glob(os.path.join(OUTDIR, 'E*_S42_geography.json')))
    if not geo_files:
        return

    for gf in geo_files:
        basename = os.path.basename(gf)
        m = re.match(r'E(\d+)_S(\d+)_geography\.json', basename)
        if not m:
            continue
        epoch = int(m.group(1))

        with open(gf) as f:
            data = json.load(f)

        print(f"\n--- E={epoch}, seed=42 ---")

        for surface in ['tp', 'tm']:
            mass = np.array(data[f'mass_{surface}'])
            pos = np.array(data[f'{surface}_pos'])
            vertices = np.array(data['tv_plus'] if surface == 'tp' else data['tv_minus'])

            n_sites = len(mass)
            assignments = np.zeros(n_sites, dtype=int)
            for i in range(n_sites):
                dists = np.linalg.norm(pos[i] - vertices, axis=1)
                assignments[i] = np.argmin(dists)

            vertex_masses = np.array([mass[assignments == v].sum() for v in range(4)])
            total = mass.sum()
            color_masses = vertex_masses[1:]
            cv = color_masses.std() / color_masses.mean() if color_masses.mean() > 0 else 0

            print(f"  {surface.upper()}: V0={vertex_masses[0]:.1f}  "
                  f"V1={vertex_masses[1]:.1f}  V2={vertex_masses[2]:.1f}  "
                  f"V3={vertex_masses[3]:.1f}  "
                  f"color_frac={color_masses.sum()/total:.3f}  "
                  f"Z₃_CV={cv:.3f}")


# ── Main ─────────────────────────────────────────────────────────────

def main():
    print("=" * 70)
    print("Phase M6: Long-Run Convergence Analysis (Q6 + Q7)")
    print("Best coupling: mk=5.0, mg=5.0")
    print("=" * 70)

    ok1 = analyze_coherence_convergence()
    ok2 = analyze_vertex_fraction_convergence()
    if ok1 and ok2:
        detailed_geography_report()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("Q6: Check corr trend above — rising = longer runs help")
    print("Q7: Check color-vertex fraction — converging to 2/3 or 3/4?")
    print("=" * 70)


if __name__ == '__main__':
    main()
