#!/usr/bin/env python3
"""
Visualization of the Holographic Derivation of ρ = M_P² H₀²

This script creates figures illustrating:
1. The scale hierarchy from Planck to Hubble
2. The holographic information bound
3. The derivation chain from SU(3) to ρ_vac
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle
from matplotlib.collections import PatchCollection
import matplotlib.gridspec as gridspec

# Set up style
plt.style.use('default')
plt.rcParams['figure.facecolor'] = 'white'
plt.rcParams['axes.facecolor'] = 'white'
plt.rcParams['font.family'] = 'sans-serif'

# Physical constants
M_P_GeV = 1.22e19
H_0_GeV = 1.44e-42
rho_obs_GeV4 = 2.5e-47
rho_formula_GeV4 = M_P_GeV**2 * H_0_GeV**2

# Create figure with multiple panels
fig = plt.figure(figsize=(16, 12))
gs = gridspec.GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.25)

# =============================================================================
# Panel 1: Scale Hierarchy
# =============================================================================
ax1 = fig.add_subplot(gs[0, 0])

scales = {
    'Planck': (19, 'M_P ~ 10^19 GeV', '#e74c3c'),
    'GUT': (16, 'Λ_GUT ~ 10^16 GeV', '#9b59b6'),
    'EW': (2, 'v_EW ~ 10^2 GeV', '#3498db'),
    'QCD': (-1, 'Λ_QCD ~ 10^-1 GeV', '#2ecc71'),
    'Hubble': (-42, 'H_0 ~ 10^-42 GeV', '#f39c12'),
}

y_pos = np.arange(len(scales))
colors = [v[2] for v in scales.values()]
values = [v[0] for v in scales.values()]
labels = [v[1] for v in scales.values()]
names = list(scales.keys())

bars = ax1.barh(y_pos, values, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
ax1.set_yticks(y_pos)
ax1.set_yticklabels(names, fontsize=12, fontweight='bold')
ax1.set_xlabel('log₁₀(Scale/GeV)', fontsize=12)
ax1.set_title('Energy Scale Hierarchy', fontsize=14, fontweight='bold')

# Add text labels on bars
for bar, label in zip(bars, labels):
    width = bar.get_width()
    ax1.annotate(label, xy=(width, bar.get_y() + bar.get_height()/2),
                xytext=(5, 0), textcoords='offset points',
                va='center', ha='left', fontsize=10)

# Add arrows showing the key relationships
ax1.annotate('', xy=(19, 4.5), xytext=(-42, 4.5),
            arrowprops=dict(arrowstyle='<->', color='red', lw=2))
ax1.text(-12, 4.7, '10^61 orders of magnitude', fontsize=10, color='red', fontweight='bold')

ax1.set_xlim(-50, 30)
ax1.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
ax1.grid(axis='x', alpha=0.3)

# =============================================================================
# Panel 2: Vacuum Energy Comparison
# =============================================================================
ax2 = fig.add_subplot(gs[0, 1])

# Different estimates of vacuum energy
estimates = {
    'Planck (naive)': (76, '#e74c3c'),
    'GUT': (64, '#9b59b6'),
    'EW': (8, '#3498db'),
    'QCD': (-3, '#2ecc71'),
    'M_P²H₀² formula': (-46, '#f39c12'),
    'Observed': (-47, '#27ae60'),
}

y_pos = np.arange(len(estimates))
values = [v[0] for v in estimates.values()]
colors = [v[1] for v in estimates.values()]
names = list(estimates.keys())

bars = ax2.barh(y_pos, values, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
ax2.set_yticks(y_pos)
ax2.set_yticklabels(names, fontsize=11, fontweight='bold')
ax2.set_xlabel('log₁₀(ρ/GeV⁴)', fontsize=12)
ax2.set_title('Vacuum Energy Density Estimates', fontsize=14, fontweight='bold')

# Add dashed line at observed value
ax2.axvline(x=-47, color='#27ae60', linestyle='--', linewidth=2, alpha=0.7)

# Highlight the gap
ax2.annotate('', xy=(76, 5.5), xytext=(-47, 5.5),
            arrowprops=dict(arrowstyle='<->', color='red', lw=2))
ax2.text(10, 5.7, '123 orders: The CC Problem', fontsize=10, color='red', fontweight='bold')

# Show formula agreement
ax2.annotate('Factor ~10', xy=(-47, -0.5), xytext=(-30, -0.8),
            fontsize=9, color='green', fontweight='bold',
            arrowprops=dict(arrowstyle='->', color='green'))

ax2.set_xlim(-60, 90)
ax2.grid(axis='x', alpha=0.3)

# =============================================================================
# Panel 3: Derivation Flow Diagram
# =============================================================================
ax3 = fig.add_subplot(gs[1, 0])
ax3.set_xlim(0, 10)
ax3.set_ylim(0, 10)
ax3.axis('off')
ax3.set_title('First-Principles Derivation Chain', fontsize=14, fontweight='bold', pad=20)

# Define boxes
boxes = [
    (5, 9.2, 'SU(3) Color Structure\n(Def 0.1.1)', '#e8f4f8'),
    (5, 7.8, 'Phase Cancellation\n(Thm 0.2.3)', '#e8f8e8'),
    (2.5, 6.4, 'M_P from QCD\n(Thm 5.2.6)', '#f8e8e8'),
    (7.5, 6.4, 'S = A/(4ℓ_P²)\n(Thm 5.2.5)', '#f8f8e8'),
    (5, 5.0, 'Thermodynamic Gravity\n(Thm 5.2.3)', '#e8e8f8'),
    (5, 3.6, 'Cosmological Horizon\nS_H = π(L_H/ℓ_P)²', '#f0e8f8'),
    (5, 2.2, 'Holographic Energy\nE_DOF = M_P/√N', '#f8e8f0'),
    (5, 0.8, 'ρ = M_P² H₀²', '#d4edda'),
]

# Draw boxes
for x, y, text, color in boxes:
    bbox = FancyBboxPatch((x-1.8, y-0.5), 3.6, 0.9,
                         boxstyle="round,pad=0.05,rounding_size=0.2",
                         facecolor=color, edgecolor='black', linewidth=1.5)
    ax3.add_patch(bbox)
    ax3.text(x, y, text, ha='center', va='center', fontsize=9, fontweight='bold')

# Draw arrows
arrow_style = dict(arrowstyle='->', color='#333333', lw=1.5)
arrows = [
    ((5, 8.7), (5, 8.3)),
    ((5, 7.3), (3.5, 6.85)),  # Split to M_P
    ((5, 7.3), (6.5, 6.85)),  # Split to S
    ((3.5, 5.95), (4.3, 5.45)),  # M_P to Thermodynamic
    ((6.5, 5.95), (5.7, 5.45)),  # S to Thermodynamic
    ((5, 4.55), (5, 4.15)),
    ((5, 3.15), (5, 2.75)),
    ((5, 1.75), (5, 1.35)),
]

for start, end in arrows:
    ax3.annotate('', xy=end, xytext=start, arrowprops=arrow_style)

# =============================================================================
# Panel 4: The Holographic Connection
# =============================================================================
ax4 = fig.add_subplot(gs[1, 1])
ax4.set_xlim(-2, 2)
ax4.set_ylim(-2, 2)
ax4.set_aspect('equal')
ax4.axis('off')
ax4.set_title('Holographic Information Bound', fontsize=14, fontweight='bold', pad=20)

# Draw the Hubble sphere
theta = np.linspace(0, 2*np.pi, 100)
ax4.plot(1.5*np.cos(theta), 1.5*np.sin(theta), 'b-', linewidth=3, label='Hubble Horizon')
ax4.fill(1.5*np.cos(theta), 1.5*np.sin(theta), alpha=0.1, color='blue')

# Draw the central region (Planck scale)
ax4.add_patch(Circle((0, 0), 0.05, color='red', zorder=5))
ax4.text(0.15, 0.1, 'Planck\nscale', fontsize=8, va='center')

# Draw info bits on the boundary
n_bits = 24
for i in range(n_bits):
    angle = 2*np.pi*i/n_bits
    x, y = 1.5*np.cos(angle), 1.5*np.sin(angle)
    ax4.add_patch(Circle((x, y), 0.08, color='orange', alpha=0.7))

# Add labels
ax4.text(0, -1.85, 'S = A/(4ℓ_P²) information bits', fontsize=11, ha='center', fontweight='bold')
ax4.text(0, 1.85, 'L_H = c/H₀', fontsize=11, ha='center', style='italic')

# Add arrows showing energy flow
ax4.annotate('', xy=(0.5, 0), xytext=(1.3, 0),
            arrowprops=dict(arrowstyle='<-', color='green', lw=2))
ax4.text(0.9, 0.2, 'E_DOF = M_P/√N', fontsize=9, ha='center', color='green')

# Formula box
formula_box = FancyBboxPatch((-1.7, -1.5), 3.4, 0.6,
                             boxstyle="round,pad=0.05",
                             facecolor='#fffdd0', edgecolor='black', linewidth=2)
ax4.add_patch(formula_box)
ax4.text(0, -1.2, r'ρ = (N × E_DOF)/V = M_P² H₀²', fontsize=11,
         ha='center', fontweight='bold')

# =============================================================================
# Save figure
# =============================================================================
plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_5_1_2_holographic_derivation.png',
            dpi=150, bbox_inches='tight', facecolor='white')
plt.close()

print("Figure saved: plots/theorem_5_1_2_holographic_derivation.png")

# =============================================================================
# Second figure: Detailed numerical comparison
# =============================================================================
fig2, axes = plt.subplots(1, 2, figsize=(14, 6))

# Panel 1: Log scale comparison
ax = axes[0]
categories = ['Planck\nM_P⁴', 'Standard QFT\n(with cutoff)', 'QCD\nΛ_QCD⁴',
              'Formula\nM_P²H₀²', 'Observed\nρ_Λ']
values = [76, 76, -3, -46, -47]
colors = ['#e74c3c', '#e74c3c', '#2ecc71', '#f39c12', '#27ae60']

bars = ax.bar(categories, values, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
ax.set_ylabel('log₁₀(ρ/GeV⁴)', fontsize=12)
ax.set_title('Vacuum Energy: The Cosmic Puzzle Solved', fontsize=14, fontweight='bold')
ax.axhline(y=-47, color='#27ae60', linestyle='--', linewidth=2, alpha=0.7, label='Observed')

# Add text annotations
ax.text(0, 78, '~10⁷⁶', ha='center', fontsize=10, fontweight='bold')
ax.text(1, 78, '~10⁷⁶', ha='center', fontsize=10, fontweight='bold')
ax.text(2, -1, '~10⁻³', ha='center', fontsize=10, fontweight='bold')
ax.text(3, -44, '~10⁻⁴⁶', ha='center', fontsize=10, fontweight='bold', color='orange')
ax.text(4, -45, '~10⁻⁴⁷', ha='center', fontsize=10, fontweight='bold', color='green')

# Add bracket showing agreement
ax.annotate('', xy=(3.5, -46), xytext=(3.5, -47),
            arrowprops=dict(arrowstyle='<->', color='green', lw=2))
ax.text(3.8, -46.5, 'Factor ~10', fontsize=10, color='green', fontweight='bold')

ax.set_ylim(-60, 90)
ax.grid(axis='y', alpha=0.3)

# Panel 2: The key ratio
ax = axes[1]

# Create a visual representation of the scale ratio
ax.set_xlim(0, 10)
ax.set_ylim(0, 10)
ax.axis('off')
ax.set_title('The Key Ratio: (H₀/M_P)²', fontsize=14, fontweight='bold')

# Draw the main equation
ax.text(5, 8.5, r'$\rho_{vac} = M_P^2 \times H_0^2$', fontsize=20, ha='center',
        fontweight='bold', color='#2c3e50')

ax.text(5, 7.2, '= M_P⁴ × (H₀/M_P)²', fontsize=16, ha='center', color='#34495e')

ax.text(5, 5.8, '= 10⁷⁶ × 10⁻¹²²', fontsize=14, ha='center', color='#7f8c8d')

ax.text(5, 4.5, '= 10⁻⁴⁶ GeV⁴', fontsize=18, ha='center', fontweight='bold', color='#27ae60')

# Draw the comparison
ax.text(5, 3.0, '━━━━━━━━━━━━━━━━━━━', fontsize=14, ha='center', color='gray')

ax.text(5, 2.2, 'Observed: 10⁻⁴⁷ GeV⁴', fontsize=14, ha='center', color='#3498db')

ax.text(5, 1.2, '✓ Agreement within factor ~10', fontsize=14, ha='center',
        fontweight='bold', color='#27ae60')

# Add a box around the key insight
box = FancyBboxPatch((1.5, 0.3), 7, 9, boxstyle="round,pad=0.1",
                     facecolor='none', edgecolor='#2c3e50', linewidth=2)
ax.add_patch(box)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_5_1_2_numerical_comparison.png',
            dpi=150, bbox_inches='tight', facecolor='white')
plt.close()

print("Figure saved: plots/theorem_5_1_2_numerical_comparison.png")

# =============================================================================
# Summary output
# =============================================================================
print("\n" + "="*70)
print("SUMMARY: First-Principles Derivation of ρ = M_P² H₀²")
print("="*70)
print(f"""
Key Results:
  • Formula prediction: ρ = {rho_formula_GeV4:.2e} GeV⁴
  • Observed value:     ρ = {rho_obs_GeV4:.2e} GeV⁴
  • Agreement factor:   {rho_formula_GeV4/rho_obs_GeV4:.1f}

The derivation uses:
  1. S = A/(4ℓ_P²) - DERIVED in Theorem 5.2.5
  2. M_P from QCD  - DERIVED in Theorem 5.2.6 (93% agreement)
  3. Cosmological horizon: L_H = c/H₀
  4. Holographic energy distribution: E_DOF = M_P/√N

The 10⁻¹²² suppression factor is (H₀/M_P)² - the ratio of
the smallest dynamical scale to the largest mass scale.
This is NOT fine-tuning; it's the natural holographic bound.
""")
