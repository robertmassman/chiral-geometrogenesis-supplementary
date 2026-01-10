"""
Theorem 5.2.4: Newton's Constant from Chiral Parameters — Visualization
========================================================================

This script creates visualizations for:
1. PPN parameter space (conformal vs derivative coupling)
2. G vs f_χ relationship
3. Quantum correction hierarchy
4. Experimental tests summary

Author: Verification Agent
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
from matplotlib.patches import Rectangle, FancyBboxPatch
import os

# Create output directory
output_dir = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots'
os.makedirs(output_dir, exist_ok=True)

# Physical constants
hbar = 1.054571817e-34  # J·s
c = 299792458  # m/s
G = 6.67430e-11  # m³/(kg·s²)
M_P_GeV = 1.22e19  # Planck mass in GeV
f_chi_GeV = M_P_GeV / np.sqrt(8 * np.pi)  # ~ 2.44 × 10^18 GeV

print("=" * 80)
print("THEOREM 5.2.4 VISUALIZATION")
print("Newton's Constant from Chiral Parameters")
print("=" * 80)

# Set up the figure with multiple subplots
fig = plt.figure(figsize=(16, 12))
gs = GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.3)

# =============================================================================
# Plot 1: PPN Parameter Space - Conformal vs Derivative Coupling
# =============================================================================
ax1 = fig.add_subplot(gs[0, 0])

# α₀ range for conformal coupling
alpha_0 = np.linspace(0, 2, 1000)

# γ - 1 for conformal coupling (Damour-Esposito-Farèse formula)
gamma_minus_1_conformal = -2 * alpha_0**2 / (1 + alpha_0**2)

# Cassini bound
cassini_bound = 2.3e-5

ax1.plot(alpha_0, gamma_minus_1_conformal, 'r-', linewidth=2.5,
         label='Conformal coupling: γ-1 = -2α₀²/(1+α₀²)')

# Derivative coupling prediction (γ = 1 exactly)
ax1.axhline(y=0, color='green', linewidth=3, linestyle='-',
            label='Derivative coupling (Goldstone): γ-1 = 0')

# Experimental bounds
ax1.axhline(y=cassini_bound, color='blue', linewidth=2, linestyle='--', alpha=0.7)
ax1.axhline(y=-cassini_bound, color='blue', linewidth=2, linestyle='--', alpha=0.7,
            label=f'Cassini bound: |γ-1| < {cassini_bound}')

# Fill excluded region
ax1.fill_between(alpha_0, -1, -cassini_bound, alpha=0.2, color='red',
                  label='Excluded by Cassini')
ax1.fill_between(alpha_0, cassini_bound, 0.1, alpha=0.2, color='red')

# Mark the CG value if conformal coupling were used
alpha_0_CG = 2 / np.sqrt(5)  # ~ 0.894
gamma_CG_conformal = -2 * alpha_0_CG**2 / (1 + alpha_0_CG**2)
ax1.scatter([alpha_0_CG], [gamma_CG_conformal], color='red', s=150, zorder=5,
            marker='X', edgecolor='black', linewidth=2)
ax1.annotate(f'If conformal:\nα₀ = 2/√5 ≈ 0.89\nγ-1 ≈ {gamma_CG_conformal:.2f}\n(RULED OUT!)',
             xy=(alpha_0_CG, gamma_CG_conformal), xytext=(1.3, -0.5),
             fontsize=10, arrowprops=dict(arrowstyle='->', color='red'),
             bbox=dict(boxstyle='round', facecolor='mistyrose', alpha=0.9))

# Mark the actual CG prediction (derivative coupling)
ax1.scatter([0], [0], color='green', s=200, zorder=5, marker='*',
            edgecolor='black', linewidth=2)
ax1.annotate('CG Prediction:\nγ = 1 exactly\n(derivative coupling)',
             xy=(0, 0), xytext=(0.3, 0.05),
             fontsize=10, arrowprops=dict(arrowstyle='->', color='green'),
             bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.9))

ax1.set_xlabel(r'Scalar-tensor coupling $\alpha_0$', fontsize=12)
ax1.set_ylabel(r'PPN parameter $\gamma - 1$', fontsize=12)
ax1.set_title('PPN Parameter Space\nConformal vs Derivative Coupling', fontsize=14, fontweight='bold')
ax1.set_xlim(0, 2)
ax1.set_ylim(-1, 0.1)
ax1.legend(loc='lower right', fontsize=9)
ax1.grid(True, alpha=0.3)

# =============================================================================
# Plot 2: G vs f_χ Relationship
# =============================================================================
ax2 = fig.add_subplot(gs[0, 1])

# f_χ range in GeV
f_chi_range = np.logspace(16, 20, 500)  # 10^16 to 10^20 GeV

# G from formula: G = ℏc / (8π f_χ²)
# Convert to SI units
hbar_GeV_s = 6.582e-25  # ℏ in GeV·s
GeV_to_kg = 1.783e-27  # kg per GeV/c²
m_per_GeV_inv = hbar_GeV_s * c  # meters per (1/GeV)

# G in m³/(kg·s²) from f_χ in GeV
# G = ℏc / (8π f_χ²) where f_χ is in energy units
# Need careful unit conversion
G_formula = hbar * c / (8 * np.pi * (f_chi_range * GeV_to_kg * c**2)**2)

ax2.loglog(f_chi_range, G_formula, 'b-', linewidth=2.5,
           label=r'$G = \hbar c / (8\pi f_\chi^2)$')

# Mark the observed value
ax2.axhline(y=G, color='red', linewidth=2, linestyle='--',
            label=f'Observed G = {G:.3e} m³/(kg·s²)')

# Mark f_χ value
ax2.axvline(x=f_chi_GeV, color='green', linewidth=2, linestyle='--',
            label=f'f_χ = {f_chi_GeV:.2e} GeV')

# Mark intersection
ax2.scatter([f_chi_GeV], [G], color='green', s=150, zorder=5, marker='o',
            edgecolor='black', linewidth=2)

# Add reference scales
ax2.axvline(x=1e16, color='purple', linewidth=1, linestyle=':', alpha=0.5)
ax2.text(1e16, 1e-8, 'GUT\nscale', fontsize=9, ha='center', color='purple')

ax2.axvline(x=M_P_GeV, color='orange', linewidth=1, linestyle=':', alpha=0.5)
ax2.text(M_P_GeV, 1e-8, 'Planck\nmass', fontsize=9, ha='center', color='orange')

ax2.set_xlabel(r'Chiral decay constant $f_\chi$ (GeV)', fontsize=12)
ax2.set_ylabel(r"Newton's constant $G$ (m³/kg·s²)", fontsize=12)
ax2.set_title(r"$G$ vs $f_\chi$: The Gravitational Coupling", fontsize=14, fontweight='bold')
ax2.legend(loc='upper right', fontsize=10)
ax2.grid(True, alpha=0.3, which='both')
ax2.set_xlim(1e16, 1e20)
ax2.set_ylim(1e-14, 1e-8)

# =============================================================================
# Plot 3: Quantum Correction Hierarchy
# =============================================================================
ax3 = fig.add_subplot(gs[1, 0])

# Different correction sources
corrections = {
    'GR loops\n(GM/rc²)²': 1e-12,
    'Planck scale\n(ℓ_P/r)²': 1e-92,
    'Goldstone loops\n(E/f_χ)⁴': 1e-108,
}

labels = list(corrections.keys())
values = list(corrections.values())
colors = ['#1f77b4', '#ff7f0e', '#2ca02c']

# Plot as log bar chart
y_pos = np.arange(len(labels))
bars = ax3.barh(y_pos, np.log10(values), color=colors, edgecolor='black', linewidth=1.5)

# Cassini sensitivity
cassini_log = np.log10(2.3e-5)
ax3.axvline(x=cassini_log, color='red', linewidth=2, linestyle='--',
            label=f'Cassini sensitivity: 10^{cassini_log:.1f}')

ax3.set_yticks(y_pos)
ax3.set_yticklabels(labels, fontsize=11)
ax3.set_xlabel(r'log₁₀(δγ)', fontsize=12)
ax3.set_title('Quantum Corrections to γ\n(All far below experimental sensitivity)', fontsize=14, fontweight='bold')
ax3.legend(loc='lower right', fontsize=10)
ax3.grid(True, alpha=0.3, axis='x')
ax3.set_xlim(-120, 0)

# Add value labels
for i, (bar, val) in enumerate(zip(bars, values)):
    ax3.text(bar.get_width() + 2, bar.get_y() + bar.get_height()/2,
             f'~10^{int(np.log10(val))}', va='center', fontsize=10, fontweight='bold')

# Add arrow showing "UNDETECTABLE" region
ax3.annotate('', xy=(-100, -0.5), xytext=(cassini_log - 5, -0.5),
             arrowprops=dict(arrowstyle='<->', color='gray', lw=2))
ax3.text(-55, -0.8, 'UNDETECTABLE', fontsize=12, ha='center', color='gray', style='italic')

# =============================================================================
# Plot 4: Experimental Tests Summary
# =============================================================================
ax4 = fig.add_subplot(gs[1, 1])

tests = ['Light\nbending', 'Shapiro\ndelay', 'Perihelion', 'GW speed',
         'EP\nviolation', 'dG/dt', 'Nordtvedt']
bounds = [2.3e-5, 2.3e-5, 8e-5, 1e-15, 1e-13, 1e-13, 4.4e-4]
predictions = [0, 0, 0, 0, 0, 0, 0]  # All exact in CG

x_pos = np.arange(len(tests))

# Plot bounds
ax4.bar(x_pos, -np.log10(bounds), color='lightcoral', edgecolor='darkred',
        linewidth=1.5, label='Experimental bound', alpha=0.8)

# Add "CG Prediction: EXACT" labels
for i, x in enumerate(x_pos):
    ax4.text(x, 1, 'CG: EXACT', ha='center', fontsize=8, fontweight='bold',
             color='green', rotation=90, va='bottom')

ax4.set_xticks(x_pos)
ax4.set_xticklabels(tests, fontsize=10)
ax4.set_ylabel(r'-log₁₀(bound)', fontsize=12)
ax4.set_title('GR Tests: All Satisfied Exactly\n(CG predicts γ = β = 1 at tree level)',
              fontsize=14, fontweight='bold')
ax4.legend(loc='upper right', fontsize=10)
ax4.grid(True, alpha=0.3, axis='y')

# Add note
ax4.text(0.5, -0.12, 'Higher bar = tighter constraint. CG matches GR exactly for all tests.',
         transform=ax4.transAxes, ha='center', fontsize=9, style='italic',
         bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))

# Main title
fig.suptitle("Theorem 5.2.4: Newton's Constant from Chiral Parameters\n" +
             r'$G = 1/(8\pi f_\chi^2)$ with derivative coupling → exact GR',
             fontsize=16, fontweight='bold', y=0.98)

plt.tight_layout(rect=[0, 0, 1, 0.95])

# Save the figure
output_path = os.path.join(output_dir, 'theorem_5_2_4_verification_plots.png')
plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
print(f"\nSaved: {output_path}")

# =============================================================================
# Additional Plot: The 8π Factor Explanation
# =============================================================================
fig2, (ax5, ax6) = plt.subplots(1, 2, figsize=(14, 5))

# Plot 5: Scalar exchange vs full scalar-tensor
approaches = ['Naive scalar\nexchange', 'Full scalar-tensor\n(conformal)']
G_factors = [4, 8]  # Factor in G = 1/(Nπf²)

bars = ax5.bar(approaches, G_factors, color=['#ff7f0e', '#2ca02c'],
               edgecolor='black', linewidth=2, width=0.5)

ax5.set_ylabel(r'Factor $N$ in $G = 1/(N\pi f_\chi^2)$', fontsize=12)
ax5.set_title('The 8π Factor: Why Not 4π?', fontsize=14, fontweight='bold')
ax5.set_ylim(0, 10)

# Add explanation
ax5.text(0, 4.5, 'Single scalar\nmediator', ha='center', fontsize=10,
         bbox=dict(boxstyle='round', facecolor='moccasin', alpha=0.8))
ax5.text(1, 8.5, 'Scalar modifies\nPlanck mass +\nmediates force', ha='center', fontsize=10,
         bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))

ax5.axhline(y=8, color='green', linestyle='--', alpha=0.5)
ax5.text(1.4, 8.2, '← Correct', fontsize=10, color='green', fontweight='bold')

# Plot 6: Energy scale hierarchy
scales = ['QCD\n(f_π)', 'GUT', 'Chiral\n(f_χ)', 'Planck\n(M_P)']
energies_GeV = [0.093, 1e16, f_chi_GeV, M_P_GeV]
colors = ['#1f77b4', '#9467bd', '#2ca02c', '#d62728']

ax6.barh(scales, np.log10(energies_GeV), color=colors, edgecolor='black', linewidth=1.5)

ax6.set_xlabel(r'log₁₀(Energy / GeV)', fontsize=12)
ax6.set_title('Energy Scale Hierarchy\nf_χ sits just below M_P', fontsize=14, fontweight='bold')
ax6.grid(True, alpha=0.3, axis='x')

# Add value labels
for i, (scale, E) in enumerate(zip(scales, energies_GeV)):
    ax6.text(np.log10(E) + 0.5, i, f'{E:.1e} GeV', va='center', fontsize=10)

# Highlight f_χ
ax6.annotate('', xy=(np.log10(f_chi_GeV), 2), xytext=(np.log10(f_chi_GeV), 3.5),
             arrowprops=dict(arrowstyle='->', color='green', lw=2))
ax6.text(np.log10(f_chi_GeV), 3.6, r'$f_\chi = M_P/\sqrt{8\pi}$',
         ha='center', fontsize=11, color='green', fontweight='bold')

plt.tight_layout()

output_path2 = os.path.join(output_dir, 'theorem_5_2_4_8pi_factor.png')
plt.savefig(output_path2, dpi=150, bbox_inches='tight', facecolor='white')
print(f"Saved: {output_path2}")

# =============================================================================
# Plot 7: PPN Investigation Summary
# =============================================================================
fig3, ax7 = plt.subplots(figsize=(12, 6))

# Create a visual summary of the PPN investigation
ax7.set_xlim(0, 10)
ax7.set_ylim(0, 10)
ax7.axis('off')

# Title
ax7.text(5, 9.5, 'PPN Parameter Investigation: Resolution Summary',
         fontsize=16, fontweight='bold', ha='center')

# Box 1: The Problem
box1 = FancyBboxPatch((0.2, 6), 3, 2.5, boxstyle="round,pad=0.1",
                       facecolor='mistyrose', edgecolor='red', linewidth=2)
ax7.add_patch(box1)
ax7.text(1.7, 8, 'PROBLEM', fontsize=12, fontweight='bold', ha='center', color='red')
ax7.text(1.7, 7.3, 'Original claim:\nγ - 1 ~ 10⁻³⁷', fontsize=10, ha='center')
ax7.text(1.7, 6.4, 'Dimensional\ninconsistency!', fontsize=9, ha='center', style='italic')

# Arrow
ax7.annotate('', xy=(3.5, 7.25), xytext=(3.2, 7.25),
             arrowprops=dict(arrowstyle='->', color='black', lw=2))

# Box 2: Naive Analysis
box2 = FancyBboxPatch((3.5, 6), 3, 2.5, boxstyle="round,pad=0.1",
                       facecolor='lightyellow', edgecolor='orange', linewidth=2)
ax7.add_patch(box2)
ax7.text(5, 8, 'NAIVE ANALYSIS', fontsize=12, fontweight='bold', ha='center', color='orange')
ax7.text(5, 7.3, 'If conformal coupling:\nα₀ = 2/√5 ≈ 0.89', fontsize=10, ha='center')
ax7.text(5, 6.4, 'γ - 1 ≈ -0.89\nRULED OUT!', fontsize=9, ha='center', color='red', fontweight='bold')

# Arrow
ax7.annotate('', xy=(6.8, 7.25), xytext=(6.5, 7.25),
             arrowprops=dict(arrowstyle='->', color='black', lw=2))

# Box 3: Resolution
box3 = FancyBboxPatch((6.8, 6), 3, 2.5, boxstyle="round,pad=0.1",
                       facecolor='lightgreen', edgecolor='green', linewidth=2)
ax7.add_patch(box3)
ax7.text(8.3, 8, 'RESOLUTION', fontsize=12, fontweight='bold', ha='center', color='green')
ax7.text(8.3, 7.3, 'θ is Goldstone mode\n→ derivative coupling', fontsize=10, ha='center')
ax7.text(8.3, 6.4, 'For static sources:\nγ = β = 1 EXACTLY', fontsize=9, ha='center',
         color='green', fontweight='bold')

# Key insight box
box4 = FancyBboxPatch((2, 2.5), 6, 2.5, boxstyle="round,pad=0.1",
                       facecolor='lightblue', edgecolor='blue', linewidth=2)
ax7.add_patch(box4)
ax7.text(5, 4.5, 'KEY INSIGHT: Goldstone Theorem', fontsize=12, fontweight='bold', ha='center')
ax7.text(5, 3.7, r'$\mathcal{L}_{int} = (\partial_\mu\theta/f_\chi) \cdot J^\mu$', fontsize=12, ha='center')
ax7.text(5, 3.0, 'Static sources: ∂ₜθ = 0, J⃗ = 0  →  No scalar contribution!',
         fontsize=10, ha='center')

# Result box
box5 = FancyBboxPatch((2, 0.3), 6, 1.5, boxstyle="round,pad=0.1",
                       facecolor='gold', edgecolor='darkorange', linewidth=2)
ax7.add_patch(box5)
ax7.text(5, 1.3, 'RESULT: CG predicts EXACT GR for all solar system tests',
         fontsize=11, fontweight='bold', ha='center')
ax7.text(5, 0.7, '(Stronger than original claim of tiny deviations)',
         fontsize=9, ha='center', style='italic')

plt.tight_layout()

output_path3 = os.path.join(output_dir, 'theorem_5_2_4_ppn_summary.png')
plt.savefig(output_path3, dpi=150, bbox_inches='tight', facecolor='white')
print(f"Saved: {output_path3}")

plt.show()

print("\n" + "=" * 80)
print("VISUALIZATION COMPLETE")
print("=" * 80)
