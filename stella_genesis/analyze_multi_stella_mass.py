#!/usr/bin/env python3
"""
Phase M7: Multi-stella mass topology analysis (Q5)

Q5: Does the multi-stella FCC lattice change mass topology or scaling exponent?

Compares single-stella (genesis_soup, with Kuramoto + mass coupling) vs
multi-stella (soup_multi_stella, Z₃ VM-only) mass distributions:
- Color-vertex fraction (cvf): does inter-stella coupling change where mass sits?
- Correlation ratio: does lattice geometry affect mass clustering?
- Phase gradient profile: how does Z₃ discrete ∇φ compare to continuous Kuramoto ∇φ?
- Scaling exponent: mass ~ d^(-α) from vertex — same α across configurations?

References:
- Q4b: single-stella cvf ≈ 0.735, corr_ratio ≈ 1.12
- Q6/Q7: cvf converges to ~0.74, corr plateaus at ~0.80 (with coupling)
"""

import os
import csv
import json
import glob
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(BASE, 'phase_m7_results')


def load_summary():
    """Load summary CSV."""
    path = os.path.join(OUTDIR, 'summary.csv')
    if not os.path.exists(path):
        print(f"ERROR: {path} not found. Run phase_m7_multi_stella_mass.sh first.")
        return None
    rows = []
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)
    return rows


def compare_configurations(rows):
    """Compare mass metrics across single vs multi-stella configurations."""
    print("=" * 70)
    print("Q5: Single-Stella vs Multi-Stella Mass Topology")
    print("=" * 70)

    configs = {}
    for row in rows:
        key = (row['type'], int(row['lattice_size']), int(row['n_stellae']))
        if key not in configs:
            configs[key] = []
        configs[key].append(row)

    print(f"\n{'Config':>20s}  {'mean_mass':>10s}  {'corr_ratio':>10s}  "
          f"{'cvf':>8s}  {'grad_phi':>10s}")
    print("-" * 65)

    results = {}
    for key in sorted(configs.keys()):
        group = configs[key]
        label = f"{key[0]} L={key[1]} ({key[2]}st)"
        mm = [float(r['mean_mass']) for r in group]
        cr = [float(r['corr_ratio']) for r in group]
        cvf = [float(r['cvf']) for r in group]
        gp = [float(r['mean_grad']) for r in group]
        results[key] = {
            'mean_mass': (np.mean(mm), np.std(mm)),
            'corr_ratio': (np.mean(cr), np.std(cr)),
            'cvf': (np.mean(cvf), np.std(cvf)),
            'grad_phi': (np.mean(gp), np.std(gp)),
        }
        print(f"{label:>20s}  {np.mean(mm):10.6f}  {np.mean(cr):10.3f}  "
              f"{np.mean(cvf):8.4f}  {np.mean(gp):10.4f}")

    # Comparison
    print("\n--- Comparison ---")
    single_key = ('single', 1, 1)
    if single_key in results:
        s = results[single_key]
        for key in sorted(results.keys()):
            if key == single_key:
                continue
            m = results[key]
            label = f"{key[0]} L={key[1]}"
            d_cvf = m['cvf'][0] - s['cvf'][0]
            d_cr = m['corr_ratio'][0] - s['corr_ratio'][0]
            d_mm = m['mean_mass'][0] - s['mean_mass'][0]
            print(f"  {label} vs single: Δcvf={d_cvf:+.4f}  Δcorr_ratio={d_cr:+.3f}  "
                  f"Δmean_mass={d_mm:+.4f}")

    return results


def analyze_geography(geo_pattern, label):
    """Analyze a geography JSON file for mass distribution profile."""
    files = sorted(glob.glob(os.path.join(OUTDIR, geo_pattern)))
    if not files:
        return None

    all_alpha = []
    all_cvf = []
    all_z3cv = []

    for gf in files:
        with open(gf) as f:
            data = json.load(f)

        for surface in ['tp', 'tm']:
            mass = np.array(data[f'mass_{surface}'])
            dist = np.array(data[f'dist_vertex_{surface}'])
            pos = np.array(data[f'{surface}_pos'])
            verts = np.array(data['tv_plus'] if surface == 'tp' else data['tv_minus'])

            # Power-law fit: mass ~ d^(-alpha)
            bins = np.linspace(0, dist.max() * 1.01, 11)
            bc, bm = [], []
            for i in range(len(bins) - 1):
                mask = (dist >= bins[i]) & (dist < bins[i + 1])
                if mask.sum() > 0:
                    bc.append((bins[i] + bins[i + 1]) / 2)
                    bm.append(mass[mask].mean())
            if len(bc) > 3:
                bc, bm = np.array(bc), np.array(bm)
                valid = (bc > 0) & (bm > 0)
                if valid.sum() > 2:
                    coeffs = np.polyfit(np.log(bc[valid]), np.log(bm[valid]), 1)
                    all_alpha.append(-coeffs[0])

            # Color-vertex fraction
            assignments = np.argmin(
                np.linalg.norm(pos[:, None, :] - verts[None, :, :], axis=2), axis=1)
            vm = np.array([mass[assignments == v].sum() for v in range(4)])
            total = mass.sum()
            if total > 0:
                all_cvf.append(vm[1:].sum() / total)
                # Z₃ symmetry
                color_masses = vm[1:]
                if color_masses.mean() > 0:
                    all_z3cv.append(color_masses.std() / color_masses.mean())

    if all_alpha:
        print(f"  {label}: α={np.mean(all_alpha):.3f}±{np.std(all_alpha):.3f}  "
              f"cvf={np.mean(all_cvf):.4f}±{np.std(all_cvf):.4f}  "
              f"Z₃_CV={np.mean(all_z3cv):.3f}±{np.std(all_z3cv):.3f}")
    return {'alpha': all_alpha, 'cvf': all_cvf, 'z3cv': all_z3cv}


def geography_comparison():
    """Compare mass decay profiles across configurations."""
    print("\n" + "=" * 70)
    print("Mass Decay Profile: mass ~ d^(-α) from nearest vertex")
    print("=" * 70 + "\n")

    results = {}
    for pattern, label in [
        ('single_S*_geography.json', 'Single-stella'),
        ('multi_L2_S*_geography.json', 'Multi L=2 (4st)'),
        ('multi_L4_S*_geography.json', 'Multi L=4 (32st)'),
    ]:
        r = analyze_geography(pattern, label)
        if r:
            results[label] = r

    # Compare α values
    if len(results) >= 2:
        print("\n--- Scaling exponent comparison ---")
        keys = list(results.keys())
        for k in keys:
            alphas = results[k]['alpha']
            if alphas:
                print(f"  {k}: α = {np.mean(alphas):.3f} "
                      f"(95% CI [{np.percentile(alphas, 2.5):.3f}, "
                      f"{np.percentile(alphas, 97.5):.3f}])")

    return results


def main():
    print("=" * 70)
    print("Phase M7: Multi-Stella Mass Topology Analysis (Q5)")
    print("=" * 70)

    rows = load_summary()
    if not rows:
        return

    config_results = compare_configurations(rows)
    geo_results = geography_comparison()

    print("\n" + "=" * 70)
    print("Q5 SUMMARY")
    print("=" * 70)
    print()

    # Determine if mass topology changes
    single_key = ('single', 1, 1)
    if single_key in config_results:
        s = config_results[single_key]
        multi_keys = [k for k in config_results if k != single_key]
        if multi_keys:
            # Check if CVF differs significantly
            cvf_diffs = []
            cr_diffs = []
            for k in multi_keys:
                m = config_results[k]
                cvf_diffs.append(abs(m['cvf'][0] - s['cvf'][0]))
                cr_diffs.append(abs(m['corr_ratio'][0] - s['corr_ratio'][0]))

            max_cvf_diff = max(cvf_diffs)
            max_cr_diff = max(cr_diffs)

            if max_cvf_diff < 0.03 and max_cr_diff < 0.05:
                print("Mass topology is ROBUST to multi-stella lattice geometry.")
                print(f"  CVF variation: ≤{max_cvf_diff:.3f} (< 0.03 threshold)")
                print(f"  Corr_ratio variation: ≤{max_cr_diff:.3f} (< 0.05 threshold)")
                print("  → The stella's internal vertex structure determines mass")
                print("    distribution, not the inter-stella lattice topology.")
            elif max_cvf_diff < 0.05:
                print("Mass topology shows MINOR changes with multi-stella geometry.")
                print(f"  CVF variation: ≤{max_cvf_diff:.3f}")
                print(f"  Corr_ratio variation: ≤{max_cr_diff:.3f}")
            else:
                print("Mass topology CHANGES significantly with multi-stella geometry.")
                print(f"  CVF variation: {max_cvf_diff:.3f}")
                print(f"  Corr_ratio variation: {max_cr_diff:.3f}")

    print()
    print("Key comparison:")
    print("  Single-stella (genesis_soup): continuous Kuramoto phases + mass coupling")
    print("  Multi-stella (soup_multi_stella): discrete Z₃ trits, no Kuramoto/coupling")
    print("  If cvf and α match → mass topology is a geometric invariant of ∂S")
    print("=" * 70)


if __name__ == '__main__':
    main()
