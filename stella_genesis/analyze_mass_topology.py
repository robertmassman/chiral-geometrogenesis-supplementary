#!/usr/bin/env python3
"""
Q2: Mass distribution vs pressure topology analysis.

Reads mass_geography.json and analyzes whether mass density correlates
with pressure ratio (vertex dominance) and distance from vertices.

Usage:
    python3 analyze_mass_topology.py [mass_geography.json]

Related: Theorem 3.1.1 (Phase-Gradient Mass), Def 0.1.3 (Pressure Functions)
"""

import json
import sys
import numpy as np
from datetime import datetime


def load_geography(filename='mass_geography.json'):
    with open(filename) as f:
        return json.load(f)


def bin_analysis(values, bins_by, bin_edges, label):
    """Bin values by bins_by using bin_edges, compute stats per bin."""
    results = []
    for i in range(len(bin_edges) - 1):
        lo, hi = bin_edges[i], bin_edges[i + 1]
        mask = (bins_by >= lo) & (bins_by < hi)
        n = mask.sum()
        if n == 0:
            continue
        vals = values[mask]
        results.append({
            'bin': f'[{lo:.2f},{hi:.2f})',
            'n_sites': int(n),
            'mean': float(np.mean(vals)),
            'std': float(np.std(vals)),
            'median': float(np.median(vals)),
            'min': float(np.min(vals)),
            'max': float(np.max(vals)),
        })
    return results


def main():
    filename = sys.argv[1] if len(sys.argv) > 1 else 'mass_geography.json'
    data = load_geography(filename)

    n = data['n_sites']
    mass_tp = np.array(data['mass_tp'])
    mass_tm = np.array(data['mass_tm'])
    p_ratio_tp = np.array(data['p_ratio_tp'])
    p_ratio_tm = np.array(data['p_ratio_tm'])
    dist_tp = np.array(data['dist_vertex_tp'])
    dist_tm = np.array(data['dist_vertex_tm'])
    grad_tp = np.array(data['grad_phi_tp'])
    grad_tm = np.array(data['grad_phi_tm'])
    vchi_tp = np.array(data['vchi_tp'])
    vchi_tm = np.array(data['vchi_tm'])

    # Combine T+ and T- for overall statistics
    mass_all = np.concatenate([mass_tp, mass_tm])
    p_ratio_all = np.concatenate([p_ratio_tp, p_ratio_tm])
    dist_all = np.concatenate([dist_tp, dist_tm])
    grad_all = np.concatenate([grad_tp, grad_tm])
    vchi_all = np.concatenate([vchi_tp, vchi_tm])

    print("=" * 65)
    print("Q2: Mass Distribution vs Pressure Topology (Thm 3.1.1)")
    print("=" * 65)
    print(f"Sites: {n} per tetrahedron, {2*n} total")
    print(f"Epoch: {data['epoch']}")
    print()

    # --- Correlation analysis ---
    print("--- Pearson Correlations ---")
    corr_p = np.corrcoef(mass_all, p_ratio_all)[0, 1]
    corr_d = np.corrcoef(mass_all, dist_all)[0, 1]
    corr_g = np.corrcoef(mass_all, grad_all)[0, 1]
    corr_v = np.corrcoef(mass_all, vchi_all)[0, 1]
    print(f"  mass vs P_ratio:       r = {corr_p:+.4f}")
    print(f"  mass vs dist_vertex:   r = {corr_d:+.4f}")
    print(f"  mass vs |∇φ|:          r = {corr_g:+.4f}")
    print(f"  mass vs v_χ:           r = {corr_v:+.4f}")
    print()

    # Spearman rank correlation
    from scipy.stats import spearmanr
    rho_p, pval_p = spearmanr(mass_all, p_ratio_all)
    rho_d, pval_d = spearmanr(mass_all, dist_all)
    print("--- Spearman Rank Correlations ---")
    print(f"  mass vs P_ratio:       ρ = {rho_p:+.4f}  (p={pval_p:.2e})")
    print(f"  mass vs dist_vertex:   ρ = {rho_d:+.4f}  (p={pval_d:.2e})")
    print()

    # --- Binned analysis: mass by P_ratio ---
    print("--- Mass by Pressure Ratio ---")
    p_edges = np.linspace(0, 1, 11)
    bins_p = bin_analysis(mass_all, p_ratio_all, p_edges, 'P_ratio')
    print(f"{'P_ratio bin':<14} {'n':>6} {'mean_mass':>10} {'std':>8} {'median':>8}")
    print("-" * 50)
    for b in bins_p:
        print(f"{b['bin']:<14} {b['n_sites']:>6} {b['mean']:>10.4f} "
              f"{b['std']:>8.4f} {b['median']:>8.4f}")
    print()

    # --- Binned analysis: mass by vertex distance ---
    print("--- Mass by Distance from Nearest Vertex ---")
    d_edges = [0, 0.3, 0.6, 0.9, 1.2, 1.5, 2.0]
    bins_d = bin_analysis(mass_all, dist_all, d_edges, 'dist')
    print(f"{'dist bin':<14} {'n':>6} {'mean_mass':>10} {'std':>8} {'median':>8}")
    print("-" * 50)
    for b in bins_d:
        print(f"{b['bin']:<14} {b['n_sites']:>6} {b['mean']:>10.4f} "
              f"{b['std']:>8.4f} {b['median']:>8.4f}")
    print()

    # --- Decomposition: mass = prefactor * v_chi * |grad_phi| ---
    print("--- Decomposition: which factor drives mass variation? ---")
    cv_grad = np.std(grad_all) / np.mean(grad_all) if np.mean(grad_all) > 0 else 0
    cv_vchi = np.std(vchi_all) / np.mean(vchi_all) if np.mean(vchi_all) > 0 else 0
    cv_mass = np.std(mass_all) / np.mean(mass_all) if np.mean(mass_all) > 0 else 0
    print(f"  CV(|∇φ|) = {cv_grad:.4f}")
    print(f"  CV(v_χ)  = {cv_vchi:.4f}")
    print(f"  CV(mass) = {cv_mass:.4f}")
    dominant = '|∇φ| (phase gradient)' if cv_grad > cv_vchi else 'v_χ (pressure VEV)'
    print(f"  → Dominant source of variation: {dominant}")
    print()

    # --- Physical interpretation ---
    # Where is mass highest?
    high_mass_mask = mass_all > np.percentile(mass_all, 90)
    low_mass_mask = mass_all < np.percentile(mass_all, 10)
    print("--- Where is mass concentrated? (top 10% vs bottom 10%) ---")
    print(f"  High-mass sites: mean P_ratio={np.mean(p_ratio_all[high_mass_mask]):.3f}, "
          f"mean dist={np.mean(dist_all[high_mass_mask]):.3f}")
    print(f"  Low-mass sites:  mean P_ratio={np.mean(p_ratio_all[low_mass_mask]):.3f}, "
          f"mean dist={np.mean(dist_all[low_mass_mask]):.3f}")
    print()

    # Save results
    results = {
        'theorem': '3.1.1',
        'question': 'Q2',
        'title': 'Mass distribution vs pressure topology',
        'timestamp': datetime.now().isoformat(),
        'n_sites': n,
        'epoch': data['epoch'],
        'correlations': {
            'pearson_mass_pratio': corr_p,
            'pearson_mass_dist': corr_d,
            'pearson_mass_grad': corr_g,
            'pearson_mass_vchi': corr_v,
            'spearman_mass_pratio': rho_p,
            'spearman_mass_dist': rho_d,
        },
        'bins_by_pratio': bins_p,
        'bins_by_dist': bins_d,
        'cv_grad': cv_grad,
        'cv_vchi': cv_vchi,
        'cv_mass': cv_mass,
        'dominant_variation_source': dominant,
    }
    outfile = 'mass_topology_results.json'
    with open(outfile, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Results saved to {outfile}")


if __name__ == '__main__':
    main()
