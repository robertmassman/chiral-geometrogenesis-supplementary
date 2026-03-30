#!/usr/bin/env python3
"""
Analyze Chirality × Enhanced VM Phase Diagram
===============================================

Reads chirality_phase_diagram_results.json and produces:
1. 2D heatmap of correlation for each mode
2. Δcorr(enhanced − classic) phase diagram with crossover boundary
3. Three-way comparison showing which mode wins at each (χ, cs)
4. χ*(cs) crossover curve with interpolation
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm
from scipy.interpolate import interp1d

INPUT_FILE = "chirality_phase_diagram_results.json"


def load_results():
    with open(INPUT_FILE) as f:
        data = json.load(f)
    return data['metadata'], data['results']


def build_grid(results, metric='corr'):
    """Build 2D grids for each mode."""
    cs_vals = sorted(set(r['cs'] for r in results))
    chi_vals = sorted(set(r['chi'] for r in results))
    modes = sorted(set(r['instr_mode'] for r in results))

    grids = {}
    for mode in modes:
        grid = np.full((len(cs_vals), len(chi_vals)), np.nan)
        for r in results:
            if r['instr_mode'] == mode:
                i = cs_vals.index(r['cs'])
                j = chi_vals.index(r['chi'])
                grid[i, j] = r.get(metric, np.nan)
        grids[mode] = grid

    return cs_vals, chi_vals, grids


def find_crossover(cs_vals, chi_vals, grids):
    """Find χ*(cs) where enhanced-classic Δcorr crosses zero."""
    crossovers = {}
    delta = grids['enhanced'] - grids['classic']

    for i, cs in enumerate(cs_vals):
        row = delta[i, :]
        # Find sign change
        for j in range(len(chi_vals) - 1):
            if row[j] > 0 and row[j+1] <= 0:
                # Linear interpolation for crossover
                chi_star = chi_vals[j] + (0 - row[j]) / (row[j+1] - row[j]) * (chi_vals[j+1] - chi_vals[j])
                crossovers[cs] = chi_star
                break
        else:
            if np.all(row >= 0):
                crossovers[cs] = None  # enhanced always wins
            else:
                crossovers[cs] = 0.0   # classic always wins

    return crossovers


def plot_phase_diagram(cs_vals, chi_vals, grids, crossovers):
    """Generate the full phase diagram figure."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 11))

    chi_arr = np.array(chi_vals)
    cs_arr = np.array(cs_vals)

    # --- Panel A: Enhanced − Classic Δcorr ---
    ax = axes[0, 0]
    delta = grids['enhanced'] - grids['classic']
    vmax = max(abs(np.nanmin(delta)), abs(np.nanmax(delta)))
    norm = TwoSlopeNorm(vmin=-vmax, vcenter=0, vmax=vmax)
    im = ax.pcolormesh(chi_arr, cs_arr, delta, cmap='RdBu_r', norm=norm, shading='nearest')
    cb = fig.colorbar(im, ax=ax, label='Δcorr (enhanced − classic)')

    # Overlay crossover line
    cs_cross = []
    chi_cross = []
    for cs, chi_star in sorted(crossovers.items()):
        if chi_star is not None:
            cs_cross.append(cs)
            chi_cross.append(chi_star)
    if len(cs_cross) >= 2:
        ax.plot(chi_cross, cs_cross, 'k-o', lw=2, ms=6, label='χ* crossover')
        ax.legend(loc='upper left', fontsize=9)

    ax.set_xlabel('Chirality χ')
    ax.set_ylabel('Coupling strength cs')
    ax.set_title('A) Enhanced − Classic (Δcorr)')

    # --- Panel B: Winner map ---
    ax = axes[0, 1]
    winner = np.zeros_like(delta)
    for i in range(len(cs_vals)):
        for j in range(len(chi_vals)):
            vals = {m: grids[m][i, j] for m in grids if not np.isnan(grids[m][i, j])}
            if not vals:
                winner[i, j] = np.nan
                continue
            best = max(vals, key=vals.get)
            winner[i, j] = {'classic': 0, 'enhanced': 1, 'write': 2}[best]

    cmap = plt.cm.colors.ListedColormap(['#d62728', '#2ca02c', '#1f77b4'])
    bounds = [-0.5, 0.5, 1.5, 2.5]
    norm_w = plt.cm.colors.BoundaryNorm(bounds, cmap.N)
    im = ax.pcolormesh(chi_arr, cs_arr, winner, cmap=cmap, norm=norm_w, shading='nearest')
    cb = fig.colorbar(im, ax=ax, ticks=[0, 1, 2])
    cb.ax.set_yticklabels(['classic', 'enhanced', 'write'])

    ax.set_xlabel('Chirality χ')
    ax.set_ylabel('Coupling strength cs')
    ax.set_title('B) Best mode at each (χ, cs)')

    # --- Panel C: Correlation heatmap for each mode (stacked) ---
    ax = axes[1, 0]
    for mode, color, marker in [('classic', '#d62728', 's'),
                                 ('enhanced', '#2ca02c', 'o'),
                                 ('write', '#1f77b4', '^')]:
        # Plot corr vs χ for each cs, using line opacity for cs
        for i, cs in enumerate(cs_vals):
            alpha = 0.3 + 0.7 * (i / (len(cs_vals) - 1))
            row = grids[mode][i, :]
            label = f'{mode} cs={cs}' if i == len(cs_vals) - 1 else None
            ax.plot(chi_vals, row, color=color, alpha=alpha, marker=marker,
                    ms=4, lw=1.2, label=label)

    ax.set_xlabel('Chirality χ')
    ax.set_ylabel('Correlation')
    ax.set_title('C) corr vs χ (opacity = cs)')
    ax.legend(fontsize=7, ncol=3, loc='lower right')
    ax.axhline(1/3, color='gray', ls='--', alpha=0.3, label='random')
    ax.set_ylim(0.3, 1.0)

    # --- Panel D: χ* vs cs crossover curve ---
    ax = axes[1, 1]
    cs_cross = []
    chi_cross = []
    for cs in sorted(crossovers.keys()):
        chi_star = crossovers[cs]
        if chi_star is not None:
            cs_cross.append(cs)
            chi_cross.append(chi_star)

    if cs_cross:
        ax.plot(cs_cross, chi_cross, 'ko-', lw=2, ms=8)

        # Interpolate if enough points
        if len(cs_cross) >= 3:
            cs_fine = np.linspace(min(cs_cross), max(cs_cross), 100)
            f = interp1d(cs_cross, chi_cross, kind='quadratic', fill_value='extrapolate')
            ax.plot(cs_fine, f(cs_fine), 'k--', alpha=0.4)

        # Shade regions
        ax.fill_between([0, 1.1], 0, [0, 0], alpha=0.1, color='green',
                        label='enhanced wins (below χ*)')
        if chi_cross:
            ax.axhline(np.mean(chi_cross), color='gray', ls=':', alpha=0.3)

    ax.set_xlabel('Coupling strength cs')
    ax.set_ylabel('Crossover χ*')
    ax.set_title('D) Crossover boundary χ*(cs)')
    ax.set_xlim(0, 1.05)
    ax.set_ylim(0, 1.05)
    ax.legend(fontsize=9)

    plt.suptitle('Chirality × Enhanced VM Phase Diagram\n'
                 '(RESULTS-Phase1 Item #1)', fontsize=13, fontweight='bold')
    plt.tight_layout()
    plt.savefig('chirality_phase_diagram.png', dpi=150, bbox_inches='tight')
    print("Saved chirality_phase_diagram.png")
    plt.close()


def print_summary(cs_vals, chi_vals, grids, crossovers):
    """Print text summary of findings."""
    print("=" * 70)
    print("CHIRALITY × ENHANCED VM PHASE DIAGRAM — SUMMARY")
    print("=" * 70)

    delta = grids['enhanced'] - grids['classic']
    delta_w = grids.get('write', grids['classic']) - grids['classic']

    print("\nΔcorr (enhanced − classic) grid:")
    header = "cs\\χ"
    print(f"{header:>6}", end="")
    for chi in chi_vals:
        print(f" {chi:6.2f}", end="")
    print()
    for i, cs in enumerate(cs_vals):
        print(f"{cs:6.1f}", end="")
        for j in range(len(chi_vals)):
            v = delta[i, j]
            marker = "*" if v < 0 else " "
            print(f" {v:+5.3f}{marker}", end="")
        print()
    print("  (* = classic wins)")

    print("\nCrossover χ*(cs):")
    for cs in sorted(crossovers.keys()):
        chi_star = crossovers[cs]
        if chi_star is not None:
            print(f"  cs={cs:.1f}: χ* ≈ {chi_star:.3f}")
        else:
            print(f"  cs={cs:.1f}: no crossover (enhanced always wins)")

    # Best mode summary
    print("\nBest mode at each grid point:")
    header = "cs\\χ"
    print(f"{header:>6}", end="")
    for chi in chi_vals:
        print(f" {chi:6.2f}", end="")
    print()
    for i, cs in enumerate(cs_vals):
        print(f"{cs:6.1f}", end="")
        for j in range(len(chi_vals)):
            vals = {m: grids[m][i, j] for m in grids}
            best = max(vals, key=vals.get)
            abbr = {'classic': 'C', 'enhanced': 'E', 'write': 'W'}[best]
            print(f" {abbr:>6}", end="")
        print()

    # Key findings
    print("\n" + "=" * 70)
    print("KEY FINDINGS")
    print("=" * 70)

    cs_cross_vals = [(cs, chi_star) for cs, chi_star in crossovers.items()
                     if chi_star is not None]
    if cs_cross_vals:
        avg_chi_star = np.mean([c[1] for c in cs_cross_vals])
        print(f"\n1. Mean crossover: χ* ≈ {avg_chi_star:.3f}")
        print(f"   Range: {min(c[1] for c in cs_cross_vals):.3f} – "
              f"{max(c[1] for c in cs_cross_vals):.3f}")

        # Check if χ* depends on cs
        if len(cs_cross_vals) >= 2:
            cs_arr = np.array([c[0] for c in cs_cross_vals])
            chi_arr = np.array([c[1] for c in cs_cross_vals])
            corr_coeff = np.corrcoef(cs_arr, chi_arr)[0, 1]
            print(f"\n2. χ* vs cs correlation: r = {corr_coeff:.3f}")
            if abs(corr_coeff) > 0.7:
                direction = "increases" if corr_coeff > 0 else "decreases"
                print(f"   → χ* {direction} with cs (strong dependence)")
            else:
                print(f"   → χ* is roughly independent of cs")

    # Count wins
    total = len(cs_vals) * len(chi_vals)
    for mode in grids:
        wins = 0
        for i in range(len(cs_vals)):
            for j in range(len(chi_vals)):
                vals = {m: grids[m][i, j] for m in grids}
                if max(vals, key=vals.get) == mode:
                    wins += 1
        print(f"\n3. {mode}: wins {wins}/{total} grid points ({100*wins/total:.0f}%)")


def main():
    meta, results = load_results()
    cs_vals, chi_vals, grids = build_grid(results, metric='corr')
    crossovers = find_crossover(cs_vals, chi_vals, grids)

    print_summary(cs_vals, chi_vals, grids, crossovers)
    plot_phase_diagram(cs_vals, chi_vals, grids, crossovers)

    print("\nDone. See chirality_phase_diagram.png for the phase diagram plot.")


if __name__ == "__main__":
    main()
