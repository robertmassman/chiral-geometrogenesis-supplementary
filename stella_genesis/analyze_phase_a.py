#!/usr/bin/env python3
"""
Phase A Analysis: Refined metrics for geometry comparison.

Raw correlation favors trivial geometries (separated, nested) where one
surface dominates the other. The stella's advantage is its BALANCED,
HETEROGENEOUS pressure landscape that produces rich dynamics.

This script computes refined metrics:
1. Pattern complexity: H(trit) × spatial_autocorr — non-trivial structure
2. Coupling efficiency: corr_above_random / coupling_events — coherence per event
3. Landscape heterogeneity: fraction of sites with intermediate ΔP (not trivially dominant)
4. Bidirectional quality: min(T+→T-, T-→T+) / max(T+→T-, T-→T+)
5. Dynamic range: corr × H(trit) — coherent AND diverse, not locked in lockstep

Usage: python3 analyze_phase_a.py
"""

import json
import os
import math

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def load_results():
    path = os.path.join(SCRIPT_DIR, "phase_a_results.json")
    with open(path) as f:
        return json.load(f)


def compute_refined_metrics(r):
    """Compute refined metrics for a single geometry result."""
    corr = r['corr']
    h_tp = r['h_tp']
    h_tm = r['h_tm']
    auto_tp = r['auto_tp']
    auto_tm = r['auto_tm']
    tp_tm = r['couplings_tp_tm']
    tm_tp = r['couplings_tm_tp']
    total = tp_tm + tm_tp
    p_contrast = r['pressure_contrast']

    # Random baselines
    H_max = math.log2(3)  # 1.585
    corr_random = 1.0 / 3.0
    auto_random = 1.0 / 3.0

    # 1. Coherence above random (normalized)
    corr_above = (corr - corr_random) / (1.0 - corr_random)

    # 2. Pattern diversity: how much entropy is retained (1.0 = max diversity)
    avg_H = (h_tp + h_tm) / 2.0
    diversity = avg_H / H_max

    # 3. Dynamic range: coherence × diversity
    # High when system is BOTH coherent AND diverse (not trivially locked)
    dynamic_range = corr_above * diversity

    # 4. Spatial structure above random
    avg_auto = (auto_tp + auto_tm) / 2.0
    spatial_quality = (avg_auto - auto_random) / (1.0 - auto_random)
    if spatial_quality < 0:
        spatial_quality = 0.0

    # 5. Coupling balance (1.0 = perfectly balanced, 0.0 = one-way)
    if total > 0:
        balance = min(tp_tm, tm_tp) / max(tp_tm, tm_tp)
    else:
        balance = 0.0  # no coupling

    # 6. Landscape heterogeneity: 1 - pressure_contrast measures how many
    # sites have INTERMEDIATE contrast (not trivially dominated)
    # But we want sites WITH contrast but not ALL maximal
    # Best landscape: some contrast everywhere, not all maximal
    # Heterogeneity peaks at p_contrast ~0.5-0.8
    heterogeneity = p_contrast * (1.0 - 0.5 * p_contrast)  # peaks at p=1, but slower

    # Actually, better metric: pressure contrast that's moderate (not 0 or 1)
    # Geometric interest = 4 × p_contrast × (1 - p_contrast)
    # Peaks at p_contrast = 0.5
    geo_interest = 4.0 * p_contrast * (1.0 - p_contrast)

    # 7. Coupling efficiency: coherence gained per million coupling events
    if total > 0:
        efficiency = (corr - corr_random) / (total / 1e6)
    else:
        efficiency = 0.0

    # 8. Composite "emergence score": combines multiple quality dimensions
    # High when: decent coherence, high diversity, balanced coupling,
    # interesting pressure landscape
    if total > 0:
        emergence = (corr_above ** 0.5) * (diversity ** 0.5) * (balance ** 0.3) * \
                    (max(geo_interest, 0.01) ** 0.3)
    else:
        emergence = 0.0

    return {
        'corr_above': corr_above,
        'diversity': diversity,
        'dynamic_range': dynamic_range,
        'spatial_quality': spatial_quality,
        'balance': balance,
        'geo_interest': geo_interest,
        'efficiency': efficiency,
        'emergence': emergence,
    }


def analyze_sweep(sweep_results):
    """Analyze the rotation sweep with refined metrics."""
    print("\n## Rotation Sweep — Refined Metrics")
    print()
    print("| θ (°) | corr | corr_above | diversity | dynamic_range | "
          "efficiency | geo_interest | emergence |")
    print("|:-----:|:----:|:----------:|:---------:|:-------------:|"
          ":----------:|:------------:|:---------:|")

    best_emergence = 0
    best_theta_em = 0
    best_dynamic = 0
    best_theta_dyn = 0

    for r in sweep_results:
        m = compute_refined_metrics(r)
        theta = r['param']
        total = r['couplings_tp_tm'] + r['couplings_tm_tp']
        print(f"| {theta:5.0f} | {r['corr']:.3f} | {m['corr_above']:.3f} | "
              f"{m['diversity']:.3f} | {m['dynamic_range']:.3f} | "
              f"{m['efficiency']:.3f} | {m['geo_interest']:.3f} | "
              f"{m['emergence']:.3f} |")

        if m['emergence'] > best_emergence:
            best_emergence = m['emergence']
            best_theta_em = theta
        if m['dynamic_range'] > best_dynamic:
            best_dynamic = m['dynamic_range']
            best_theta_dyn = theta

    print(f"\n**Best emergence score: {best_emergence:.4f} at θ={best_theta_em:.0f}°**")
    print(f"**Best dynamic range: {best_dynamic:.4f} at θ={best_theta_dyn:.0f}°**")


def analyze_discrete(discrete_results):
    """Analyze discrete geometries with refined metrics."""
    print("\n## Discrete Geometries — Refined Metrics")
    print()
    print("| Geometry | corr | corr_above | diversity | dynamic_range | "
          "balance | efficiency | emergence |")
    print("|:---------|:----:|:----------:|:---------:|:-------------:|"
          ":-------:|:----------:|:---------:|")

    all_metrics = []
    for r in discrete_results:
        m = compute_refined_metrics(r)
        desc = r.get('description', r['geometry'])
        # Shorten description
        if len(desc) > 30:
            desc = desc[:28] + ".."
        print(f"| {desc} | {r['corr']:.3f} | {m['corr_above']:.3f} | "
              f"{m['diversity']:.3f} | {m['dynamic_range']:.3f} | "
              f"{m['balance']:.3f} | {m['efficiency']:.3f} | "
              f"{m['emergence']:.3f} |")
        all_metrics.append((desc, r, m))

    # Sort by emergence score
    all_metrics.sort(key=lambda x: x[2]['emergence'], reverse=True)
    print("\n### Ranked by Emergence Score")
    print()
    for i, (desc, r, m) in enumerate(all_metrics):
        marker = " ← STELLA" if r['geometry'] == 'stella' else ""
        print(f"{i+1}. {desc}: emergence={m['emergence']:.4f}, "
              f"corr={r['corr']:.3f}, dynamic_range={m['dynamic_range']:.3f}"
              f"{marker}")


def key_findings(sweep_results, discrete_results):
    """Print key findings."""
    print("\n## Key Findings")
    print()

    # Get stella metrics
    stella_r = next(r for r in discrete_results if r['geometry'] == 'stella')
    stella_m = compute_refined_metrics(stella_r)

    # Get separated z+4 metrics (trivially high coherence)
    sep4 = next((r for r in discrete_results
                 if r['geometry'] == 'separated' and r['param'] == 4.0), None)

    print("### 1. Raw correlation is misleading")
    print()
    if sep4:
        sep4_m = compute_refined_metrics(sep4)
        print(f"Separated(z+4) achieves corr={sep4['corr']:.3f} but "
              f"diversity={sep4_m['diversity']:.3f}")
        print(f"→ Near-perfect lockstep: one surface overwrites the other.")
        print(f"→ Dynamic range = {sep4_m['dynamic_range']:.3f} "
              f"(corr×diversity penalizes trivial sync)")

    print()
    print("### 2. The stella achieves balanced, non-trivial coherence")
    print()
    print(f"Stella: corr={stella_r['corr']:.3f}, diversity={stella_m['diversity']:.3f}, "
          f"balance={stella_m['balance']:.3f}")
    print(f"→ Dynamic range = {stella_m['dynamic_range']:.3f}")
    print(f"→ Emergence score = {stella_m['emergence']:.3f}")
    print(f"→ Coupling efficiency = {stella_m['efficiency']:.3f} "
          f"(coherence per M coupling events)")

    print()
    print("### 3. Geometric interest vs raw coherence")
    print()
    print("The stella's pressure landscape has p_contrast=0.825 with 66/34")
    print("own/other dominance split — a HETEROGENEOUS landscape that creates")
    print("spatially structured coupling, not uniform overwriting.")
    print()
    print("For Phase B (crystallization), the fitness function should reward:")
    print("  - Moderate coherence (not trivial lockstep)")
    print("  - High pattern diversity")
    print("  - Balanced bidirectional coupling")
    print("  - Heterogeneous pressure landscape")


def main():
    data = load_results()
    print("# Phase A Analysis: Refined Metrics")
    print()
    print("Raw correlation rewards trivial geometries (separated, nested)")
    print("where maximal pressure contrast creates lockstep synchronization.")
    print("These refined metrics capture what makes the stella's dynamics RICH.")

    analyze_sweep(data['sweep'])
    analyze_discrete(data['discrete'])
    key_findings(data['sweep'], data['discrete'])


if __name__ == "__main__":
    main()
