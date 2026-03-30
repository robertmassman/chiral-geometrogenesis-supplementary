#!/usr/bin/env python3
"""
COUPLE Site Selection Pattern Analysis
=======================================

Investigates whether programs evolve to preferentially COUPLE at
geometrically strategic locations on the stella octangula.

Loads the couple_geography.json dump from genesis_soup and correlates
per-site COUPLE frequency with geometric features (distance to vertices,
pressure ratio, pressure differential).

Usage:
    python3 analyze_couple_geography.py [couple_geography.json]
"""

import json
import sys
import numpy as np
from scipy import stats

# Optional plotting
try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from mpl_toolkits.mplot3d import Axes3D
    HAS_MPL = True
except ImportError:
    HAS_MPL = False


def load_data(path):
    with open(path) as f:
        d = json.load(f)
    return {k: np.array(v) if isinstance(v, list) else v for k, v in d.items()}


def compute_geometric_features(data):
    """Compute per-site geometric features for T+ and T- surfaces."""
    tp_pos = data['tp_pos']    # (N, 3)
    tm_pos = data['tm_pos']    # (N, 3)
    tv_plus = data['tv_plus']  # (4, 3)
    tv_minus = data['tv_minus']  # (4, 3)
    n = data['n_sites']

    features = {}

    # Distance to nearest own-vertex and other-vertex (T+ surface)
    dist_own_tp = np.min([np.linalg.norm(tp_pos - v, axis=1) for v in tv_plus], axis=0)
    dist_other_tp = np.min([np.linalg.norm(tp_pos - v, axis=1) for v in tv_minus], axis=0)

    # Distance to nearest own-vertex and other-vertex (T- surface)
    dist_own_tm = np.min([np.linalg.norm(tm_pos - v, axis=1) for v in tv_minus], axis=0)
    dist_other_tm = np.min([np.linalg.norm(tm_pos - v, axis=1) for v in tv_plus], axis=0)

    # Pressure ratios
    pp_tp = data['pp_at_tp']
    pm_tp = data['pm_at_tp']
    pp_tm = data['pp_at_tm']
    pm_tm = data['pm_at_tm']

    sum_tp = pp_tp + pm_tp
    sum_tm = pp_tm + pm_tm

    pressure_ratio_tp = np.where(sum_tp > 1e-10, pp_tp / sum_tp, 0.5)
    pressure_ratio_tm = np.where(sum_tm > 1e-10, pm_tm / sum_tm, 0.5)

    pressure_diff_tp = np.where(sum_tp > 1e-10, np.abs(pp_tp - pm_tp) / sum_tp, 0.0)
    pressure_diff_tm = np.where(sum_tm > 1e-10, np.abs(pm_tm - pp_tm) / sum_tm, 0.0)

    is_own_dominant_tp = pp_tp > pm_tp
    is_own_dominant_tm = pm_tm > pp_tm

    features['tp'] = {
        'dist_own_vertex': dist_own_tp,
        'dist_other_vertex': dist_other_tp,
        'pressure_ratio': pressure_ratio_tp,
        'pressure_differential': pressure_diff_tp,
        'is_own_dominant': is_own_dominant_tp,
    }
    features['tm'] = {
        'dist_own_vertex': dist_own_tm,
        'dist_other_vertex': dist_other_tm,
        'pressure_ratio': pressure_ratio_tm,
        'pressure_differential': pressure_diff_tm,
        'is_own_dominant': is_own_dominant_tm,
    }
    return features


def compute_couple_rates(data):
    """Compute per-site COUPLE rates normalized by visit frequency."""
    visit = data['visit_hist'].astype(float)
    couple_tp = data['couple_hist_tp'].astype(float)
    couple_tm = data['couple_hist_tm'].astype(float)

    # Avoid division by zero
    safe_visit = np.maximum(visit, 1.0)
    rate_tp = couple_tp / safe_visit
    rate_tm = couple_tm / safe_visit

    # Combined rate (total COUPLE flags per visit)
    rate_combined = (couple_tp + couple_tm) / safe_visit

    return rate_tp, rate_tm, rate_combined, visit


def binned_analysis(feature, rate, n_bins=10, label='feature'):
    """Bin sites by feature value and compute mean COUPLE rate per bin."""
    bins = np.linspace(feature.min(), feature.max() + 1e-10, n_bins + 1)
    bin_idx = np.digitize(feature, bins) - 1
    bin_idx = np.clip(bin_idx, 0, n_bins - 1)

    bin_centers = []
    bin_means = []
    bin_stds = []
    bin_counts = []

    for b in range(n_bins):
        mask = bin_idx == b
        if mask.sum() > 0:
            bin_centers.append((bins[b] + bins[b + 1]) / 2)
            bin_means.append(rate[mask].mean())
            bin_stds.append(rate[mask].std() / max(1, np.sqrt(mask.sum())))
            bin_counts.append(mask.sum())

    return np.array(bin_centers), np.array(bin_means), np.array(bin_stds), np.array(bin_counts)


def chi_squared_test(couple_hist, visit_hist):
    """Test whether COUPLE is spatially uniform given visits."""
    total_couple = couple_hist.sum()
    total_visit = visit_hist.sum()
    if total_visit == 0 or total_couple == 0:
        return 0.0, 1.0

    # Expected: each site gets couple proportional to visits
    global_rate = total_couple / total_visit
    expected = visit_hist * global_rate

    # Only use sites with expected > 5 for chi-squared validity
    mask = expected > 5
    if mask.sum() < 10:
        return 0.0, 1.0

    chi2 = np.sum((couple_hist[mask] - expected[mask])**2 / expected[mask])
    dof = mask.sum() - 1
    p_value = 1.0 - stats.chi2.cdf(chi2, dof)
    return chi2, p_value


def dominance_comparison(features, rate, surface_label):
    """Compare COUPLE rate at own-dominant vs other-dominant sites."""
    own_dom = features['is_own_dominant']
    rate_own = rate[own_dom].mean()
    rate_other = rate[~own_dom].mean()
    n_own = own_dom.sum()
    n_other = (~own_dom).sum()

    # Two-sample t-test
    t_stat, p_val = stats.ttest_ind(rate[own_dom], rate[~own_dom])

    return {
        'own_dominant_mean': float(rate_own),
        'other_dominant_mean': float(rate_other),
        'n_own': int(n_own),
        'n_other': int(n_other),
        'ratio': float(rate_own / max(rate_other, 1e-10)),
        't_statistic': float(t_stat),
        'p_value': float(p_val),
    }


def run_correlations(features, rate, surface_label):
    """Compute Spearman correlations between COUPLE rate and features."""
    results = {}
    for name, feat in features.items():
        if name == 'is_own_dominant':
            continue
        rho, p = stats.spearmanr(feat, rate)
        results[name] = {
            'spearman_rho': float(rho),
            'p_value': float(p),
            'significant': bool(p < 0.01),
        }
    return results


def plot_binned(features_tp, rate_tp, features_tm, rate_tm, outpath):
    """4-panel plot: COUPLE rate vs each geometric feature."""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    feat_names = [
        ('dist_own_vertex', 'Distance to nearest own vertex'),
        ('dist_other_vertex', 'Distance to nearest other vertex'),
        ('pressure_ratio', 'Pressure ratio P_own/(P_own+P_other)'),
        ('pressure_differential', 'Pressure differential |ΔP|/(P₊+P₋)'),
    ]

    for ax, (key, title) in zip(axes.flat, feat_names):
        # T+ surface
        cx, my, sy, _ = binned_analysis(features_tp[key], rate_tp, n_bins=12, label=key)
        ax.errorbar(cx, my, yerr=sy, fmt='o-', label='T₊', color='#2196F3',
                    capsize=3, markersize=5)

        # T- surface
        cx2, my2, sy2, _ = binned_analysis(features_tm[key], rate_tm, n_bins=12, label=key)
        ax.errorbar(cx2, my2, yerr=sy2, fmt='s--', label='T₋', color='#F44336',
                    capsize=3, markersize=5)

        # Global mean
        global_mean = np.concatenate([rate_tp, rate_tm]).mean()
        ax.axhline(global_mean, color='gray', linestyle=':', alpha=0.7,
                   label=f'Global mean ({global_mean:.4f})')

        ax.set_xlabel(title)
        ax.set_ylabel('COUPLE rate (per visit)')
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)

    fig.suptitle('COUPLE Site Selection vs Geometric Features', fontsize=14, y=1.02)
    plt.tight_layout()
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"Saved binned plot: {outpath}")
    plt.close()


def plot_3d_scatter(data, rate_tp, rate_tm, outpath):
    """3D scatter of site positions colored by COUPLE rate."""
    fig = plt.figure(figsize=(14, 6))

    for idx, (pos_key, rate, label, tv_key) in enumerate([
        ('tp_pos', rate_tp, 'T₊ surface', 'tv_plus'),
        ('tm_pos', rate_tm, 'T₋ surface', 'tv_minus'),
    ]):
        ax = fig.add_subplot(1, 2, idx + 1, projection='3d')
        pos = data[pos_key]
        sc = ax.scatter(pos[:, 0], pos[:, 1], pos[:, 2],
                        c=rate, cmap='hot', s=15, alpha=0.8)

        # Overlay vertices
        verts = data[tv_key]
        ax.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
                   c='lime', s=200, marker='^', edgecolors='black',
                   linewidths=1.5, zorder=5, label='Own vertices')

        other_key = 'tv_minus' if tv_key == 'tv_plus' else 'tv_plus'
        other_verts = data[other_key]
        ax.scatter(other_verts[:, 0], other_verts[:, 1], other_verts[:, 2],
                   c='cyan', s=200, marker='v', edgecolors='black',
                   linewidths=1.5, zorder=5, label='Other vertices')

        ax.set_title(f'{label} — COUPLE rate')
        ax.legend(fontsize=8, loc='upper left')
        plt.colorbar(sc, ax=ax, shrink=0.6, label='COUPLE rate')

    plt.tight_layout()
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"Saved 3D scatter: {outpath}")
    plt.close()


def plot_histogram(rate_tp, rate_tm, outpath):
    """Histogram of COUPLE rates across sites."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    ax1.hist(rate_tp, bins=30, color='#2196F3', alpha=0.7, edgecolor='black')
    ax1.axvline(rate_tp.mean(), color='red', linestyle='--',
                label=f'Mean = {rate_tp.mean():.4f}')
    ax1.set_xlabel('COUPLE rate (per visit)')
    ax1.set_ylabel('Number of sites')
    ax1.set_title('T₊ COUPLE rate distribution')
    ax1.legend()

    ax2.hist(rate_tm, bins=30, color='#F44336', alpha=0.7, edgecolor='black')
    ax2.axvline(rate_tm.mean(), color='blue', linestyle='--',
                label=f'Mean = {rate_tm.mean():.4f}')
    ax2.set_xlabel('COUPLE rate (per visit)')
    ax2.set_ylabel('Number of sites')
    ax2.set_title('T₋ COUPLE rate distribution')
    ax2.legend()

    plt.tight_layout()
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"Saved histogram: {outpath}")
    plt.close()


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'couple_geography.json'
    print(f"Loading {path}...")
    data = load_data(path)

    n = data['n_sites']
    epochs = data['total_epochs']
    print(f"Sites: {n}, Epochs: {epochs}")

    # Compute features and rates
    features = compute_geometric_features(data)
    rate_tp, rate_tm, rate_combined, visit = compute_couple_rates(data)

    # Basic stats
    print(f"\n=== Visit Statistics ===")
    print(f"Total visits: {visit.sum():.0f}")
    print(f"Mean visits/site: {visit.mean():.1f} (std={visit.std():.1f})")
    print(f"Min/Max visits: {visit.min():.0f} / {visit.max():.0f}")
    cv_visit = visit.std() / visit.mean()
    print(f"Visit CV (coefficient of variation): {cv_visit:.3f}")

    print(f"\n=== COUPLE Histogram Statistics ===")
    couple_tp = data['couple_hist_tp'].astype(float)
    couple_tm = data['couple_hist_tm'].astype(float)
    print(f"Total COUPLE flags — T₊: {couple_tp.sum():.0f}, T₋: {couple_tm.sum():.0f}")
    print(f"Mean COUPLE rate — T₊: {rate_tp.mean():.4f}, T₋: {rate_tm.mean():.4f}")
    print(f"Std  COUPLE rate — T₊: {rate_tp.std():.4f}, T₋: {rate_tm.std():.4f}")
    cv_tp = rate_tp.std() / max(rate_tp.mean(), 1e-10)
    cv_tm = rate_tm.std() / max(rate_tm.mean(), 1e-10)
    print(f"COUPLE rate CV — T₊: {cv_tp:.3f}, T₋: {cv_tm:.3f}")

    # Chi-squared test
    print(f"\n=== Chi-Squared Test (spatial uniformity) ===")
    chi2_tp, p_chi2_tp = chi_squared_test(couple_tp, visit)
    chi2_tm, p_chi2_tm = chi_squared_test(couple_tm, visit)
    print(f"T₊: χ²={chi2_tp:.1f}, p={p_chi2_tp:.2e} {'*** SIGNIFICANT' if p_chi2_tp < 0.01 else '(not significant)'}")
    print(f"T₋: χ²={chi2_tm:.1f}, p={p_chi2_tm:.2e} {'*** SIGNIFICANT' if p_chi2_tm < 0.01 else '(not significant)'}")

    # Spearman correlations
    print(f"\n=== Spearman Correlations (COUPLE rate vs geometric features) ===")
    corr_tp = run_correlations(features['tp'], rate_tp, 'T+')
    corr_tm = run_correlations(features['tm'], rate_tm, 'T-')

    print(f"\n{'Feature':<30} {'T₊ ρ':>8} {'p':>12} {'T₋ ρ':>8} {'p':>12}")
    print("-" * 72)
    for key in corr_tp:
        tp = corr_tp[key]
        tm = corr_tm[key]
        sig_tp = '***' if tp['significant'] else ''
        sig_tm = '***' if tm['significant'] else ''
        print(f"{key:<30} {tp['spearman_rho']:>+8.4f} {tp['p_value']:>12.2e} {sig_tp:>3} "
              f"{tm['spearman_rho']:>+8.4f} {tm['p_value']:>12.2e} {sig_tm:>3}")

    # Dominance comparison
    print(f"\n=== Own-Dominant vs Other-Dominant Sites ===")
    dom_tp = dominance_comparison(features['tp'], rate_tp, 'T+')
    dom_tm = dominance_comparison(features['tm'], rate_tm, 'T-')

    for label, dom in [('T₊', dom_tp), ('T₋', dom_tm)]:
        print(f"\n{label}:")
        print(f"  Own-dominant sites ({dom['n_own']}): mean rate = {dom['own_dominant_mean']:.4f}")
        print(f"  Other-dominant sites ({dom['n_other']}): mean rate = {dom['other_dominant_mean']:.4f}")
        print(f"  Ratio: {dom['ratio']:.3f}x")
        print(f"  t-test: t={dom['t_statistic']:.3f}, p={dom['p_value']:.2e}"
              f" {'*** SIGNIFICANT' if dom['p_value'] < 0.01 else ''}")

    # Top/bottom sites analysis
    print(f"\n=== Top/Bottom Sites by COUPLE Rate (T₊) ===")
    sorted_idx = np.argsort(rate_tp)[::-1]
    print("Top 10 sites:")
    for i in sorted_idx[:10]:
        pos = data['tp_pos'][i]
        pr = features['tp']['pressure_ratio'][i]
        dov = features['tp']['dist_own_vertex'][i]
        print(f"  site {i}: rate={rate_tp[i]:.4f}, visits={visit[i]:.0f}, "
              f"P_ratio={pr:.3f}, dist_own_v={dov:.3f}, "
              f"pos=({pos[0]:.2f},{pos[1]:.2f},{pos[2]:.2f})")

    print("Bottom 10 sites (visited >0):")
    visited_idx = sorted_idx[visit[sorted_idx] > 0]
    for i in visited_idx[-10:]:
        pos = data['tp_pos'][i]
        pr = features['tp']['pressure_ratio'][i]
        dov = features['tp']['dist_own_vertex'][i]
        print(f"  site {i}: rate={rate_tp[i]:.4f}, visits={visit[i]:.0f}, "
              f"P_ratio={pr:.3f}, dist_own_v={dov:.3f}, "
              f"pos=({pos[0]:.2f},{pos[1]:.2f},{pos[2]:.2f})")

    # Save results JSON
    results = {
        'n_sites': int(n),
        'total_epochs': int(epochs),
        'visit_stats': {
            'total': float(visit.sum()),
            'mean': float(visit.mean()),
            'std': float(visit.std()),
            'cv': float(cv_visit),
        },
        'couple_stats': {
            'total_tp': float(couple_tp.sum()),
            'total_tm': float(couple_tm.sum()),
            'mean_rate_tp': float(rate_tp.mean()),
            'mean_rate_tm': float(rate_tm.mean()),
            'cv_tp': float(cv_tp),
            'cv_tm': float(cv_tm),
        },
        'chi_squared': {
            'tp': {'chi2': float(chi2_tp), 'p_value': float(p_chi2_tp)},
            'tm': {'chi2': float(chi2_tm), 'p_value': float(p_chi2_tm)},
        },
        'correlations': {'tp': corr_tp, 'tm': corr_tm},
        'dominance': {'tp': dom_tp, 'tm': dom_tm},
    }

    out_json = path.replace('.json', '_results.json')
    with open(out_json, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out_json}")

    # Plots
    if HAS_MPL:
        base = path.replace('.json', '')
        plot_binned(features['tp'], rate_tp, features['tm'], rate_tm,
                    f'{base}_binned.png')
        plot_3d_scatter(data, rate_tp, rate_tm, f'{base}_3d.png')
        plot_histogram(rate_tp, rate_tm, f'{base}_histogram.png')
    else:
        print("\nmatplotlib not available — skipping plots")

    # Summary verdict
    print(f"\n{'='*60}")
    print("VERDICT")
    print(f"{'='*60}")

    any_significant = any(
        corr_tp[k]['significant'] or corr_tm[k]['significant']
        for k in corr_tp
    )
    chi2_significant = p_chi2_tp < 0.01 or p_chi2_tm < 0.01
    dom_significant = dom_tp['p_value'] < 0.01 or dom_tm['p_value'] < 0.01

    if chi2_significant:
        print("COUPLE is spatially NON-UNIFORM (chi-squared significant)")
    else:
        print("COUPLE is spatially UNIFORM (chi-squared not significant)")

    if any_significant:
        print("Significant correlations found with geometric features:")
        for k in corr_tp:
            if corr_tp[k]['significant']:
                print(f"  T₊: {k} (ρ={corr_tp[k]['spearman_rho']:+.4f})")
            if corr_tm[k]['significant']:
                print(f"  T₋: {k} (ρ={corr_tm[k]['spearman_rho']:+.4f})")
    else:
        print("No significant correlations with geometric features")

    if dom_significant:
        for label, dom in [('T₊', dom_tp), ('T₋', dom_tm)]:
            if dom['p_value'] < 0.01:
                higher = 'own-dominant' if dom['own_dominant_mean'] > dom['other_dominant_mean'] else 'other-dominant'
                print(f"  {label}: {higher} sites have significantly higher COUPLE rate ({dom['ratio']:.2f}x)")

    return results


if __name__ == '__main__':
    main()
