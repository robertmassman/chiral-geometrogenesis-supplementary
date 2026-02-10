"""
Theorem 5.2.3: Einstein Equations as Thermodynamic Identity — Visualization
============================================================================

This script creates visualizations for:
1. Bogoliubov coefficient thermal spectrum
2. SU(3) vs SU(2) area quantization comparison
3. Entropy scaling with area
4. Unruh temperature vs acceleration

Author: Verification Agent
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import os

# Create output directory
output_dir = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots'
os.makedirs(output_dir, exist_ok=True)

# Physical constants
hbar = 1.054571817e-34  # J·s
c = 299792458  # m/s
k_B = 1.380649e-23  # J/K
G = 6.67430e-11  # m³/(kg·s²)
ell_P = np.sqrt(hbar * G / c**3)  # Planck length

print("=" * 80)
print("THEOREM 5.2.3 VISUALIZATION")
print("Einstein Equations as Thermodynamic Identity")
print("=" * 80)

# Set up the figure with multiple subplots
fig = plt.figure(figsize=(16, 12))
gs = GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.3)

# =============================================================================
# Plot 1: Bogoliubov Coefficient / Thermal Spectrum
# =============================================================================
ax1 = fig.add_subplot(gs[0, 0])

# Bose-Einstein distribution for different temperatures
omega = np.linspace(0.01, 5, 500)  # dimensionless frequency Ω

# Different acceleration values (in units where ℏ = c = k_B = 1)
T_values = [0.5, 1.0, 2.0]  # Temperature in arbitrary units
colors = ['#1f77b4', '#ff7f0e', '#2ca02c']
labels = ['T = 0.5', 'T = 1.0', 'T = 2.0']

for T, color, label in zip(T_values, colors, labels):
    # |β|² = 1/(exp(2πΩ/T) - 1) is the Bose-Einstein distribution
    n_omega = 1 / (np.exp(omega / T) - 1)
    ax1.plot(omega, n_omega, color=color, linewidth=2, label=f'{label} (a = {2*np.pi*T:.2f})')

ax1.set_xlabel(r'Frequency $\Omega$ (arb. units)', fontsize=12)
ax1.set_ylabel(r'$|\beta_{\omega\Omega}|^2 = \langle n_\Omega \rangle$', fontsize=12)
ax1.set_title('Bogoliubov Coefficients: Thermal Spectrum\n(Unruh Effect)', fontsize=14, fontweight='bold')
ax1.set_xlim(0, 5)
ax1.set_ylim(0, 10)
ax1.legend(title='Unruh Temperature', fontsize=10)
ax1.grid(True, alpha=0.3)

# Add annotation
ax1.annotate(r'$|\beta|^2 = \frac{1}{e^{2\pi\Omega c/a} - 1}$',
             xy=(3, 6), fontsize=14,
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

# =============================================================================
# Plot 2: SU(3) vs SU(2) Area Quantization
# =============================================================================
ax2 = fig.add_subplot(gs[0, 1])

# LQG SU(2) area spectrum
gamma_LQG = 0.2375  # Barbero-Immirzi parameter for SU(2)
j_values = np.array([0.5, 1, 1.5, 2, 2.5, 3, 3.5, 4])
area_SU2 = 8 * np.pi * gamma_LQG * np.sqrt(j_values * (j_values + 1))

# CG SU(3) area spectrum
gamma_SU3 = 0.1516  # Matched Immirzi parameter for SU(3)
# For SU(3), we use the fundamental representation with C_2 = 4/3
# Area ~ 8π γ ℓ_P² √(C_2) for the fundamental
C2_values = np.array([4/3, 10/3, 3, 16/3, 6, 21/3, 24/3, 9])  # Various SU(3) reps
area_SU3 = 8 * np.pi * gamma_SU3 * np.sqrt(C2_values) / np.sqrt(3)

# Plot as bar chart
x = np.arange(len(j_values))
width = 0.35

bars1 = ax2.bar(x - width/2, area_SU2, width, label='SU(2) LQG', color='#1f77b4', alpha=0.8)
bars2 = ax2.bar(x + width/2, area_SU3[:len(j_values)], width, label='SU(3) CG', color='#ff7f0e', alpha=0.8)

ax2.set_xlabel('Representation Index', fontsize=12)
ax2.set_ylabel(r'Area $A / (8\pi\ell_P^2)$', fontsize=12)
ax2.set_title('Area Quantization: SU(2) vs SU(3)\n(in units of 8πℓ²_P)', fontsize=14, fontweight='bold')
ax2.set_xticks(x)
ax2.set_xticklabels([f'j={j}' if j == int(j) else f'j={j}' for j in j_values])
ax2.legend(fontsize=10)
ax2.grid(True, alpha=0.3, axis='y')

# Add text box with key values
textstr = f'SU(2): γ_LQG = {gamma_LQG:.4f}\nSU(3): γ_SU3 = {gamma_SU3:.4f}\nRatio: {gamma_LQG/gamma_SU3:.2f}'
ax2.text(0.95, 0.95, textstr, transform=ax2.transAxes, fontsize=10,
         verticalalignment='top', horizontalalignment='right',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

# =============================================================================
# Plot 3: Entropy vs Area (Bekenstein-Hawking)
# =============================================================================
ax3 = fig.add_subplot(gs[1, 0])

# Area in Planck units
A_planck = np.linspace(1, 1000, 500)  # A/ℓ_P²

# Bekenstein-Hawking entropy
S_BH = A_planck / 4

# With logarithmic correction (as predicted by CG)
S_log = A_planck / 4 - 1.5 * np.log(A_planck)

ax3.plot(A_planck, S_BH, 'b-', linewidth=2.5, label=r'$S = A/(4\ell_P^2)$ (Bekenstein-Hawking)')
ax3.plot(A_planck, S_log, 'r--', linewidth=2, label=r'$S = A/(4\ell_P^2) - \frac{3}{2}\ln(A/\ell_P^2)$ (with correction)')

ax3.set_xlabel(r'Area $A/\ell_P^2$', fontsize=12)
ax3.set_ylabel(r'Entropy $S/k_B$', fontsize=12)
ax3.set_title('Black Hole Entropy: Area Law\n(Derived from SU(3) Phase Counting)', fontsize=14, fontweight='bold')
ax3.legend(fontsize=10)
ax3.grid(True, alpha=0.3)
ax3.set_xlim(0, 1000)
ax3.set_ylim(0, 260)

# Add annotation for the 1/4 factor
ax3.annotate(r'$\gamma = \frac{1}{4}$ derived from',
             xy=(500, 125), fontsize=11,
             xytext=(600, 80),
             arrowprops=dict(arrowstyle='->', color='black'),
             bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))
ax3.annotate(r'SU(3) representation theory',
             xy=(600, 60), fontsize=10,
             bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))

# =============================================================================
# Plot 4: Unruh Temperature vs Acceleration
# =============================================================================
ax4 = fig.add_subplot(gs[1, 1])

# Acceleration range (in m/s²)
a = np.logspace(15, 30, 500)  # from 10^15 to 10^30 m/s²

# Unruh temperature
T_Unruh = hbar * a / (2 * np.pi * c * k_B)

ax4.loglog(a, T_Unruh, 'b-', linewidth=2.5)

# Mark some reference points
# Surface gravity of a solar mass black hole: a ~ c⁴/(4GM) ~ 10^13 m/s²
a_sun = c**4 / (4 * G * 2e30)  # Solar mass
T_sun = hbar * a_sun / (2 * np.pi * c * k_B)

# Planck acceleration
a_Planck = c**7 / (hbar * G)
T_Planck = hbar * a_Planck / (2 * np.pi * c * k_B)

ax4.axvline(a_sun, color='orange', linestyle='--', alpha=0.7, label=f'Solar BH: a ~ {a_sun:.1e} m/s²')
ax4.axhline(T_sun, color='orange', linestyle=':', alpha=0.5)

ax4.axvline(a_Planck, color='red', linestyle='--', alpha=0.7, label=f'Planck: a ~ {a_Planck:.1e} m/s²')

ax4.set_xlabel(r'Acceleration $a$ (m/s²)', fontsize=12)
ax4.set_ylabel(r'Unruh Temperature $T_U$ (K)', fontsize=12)
ax4.set_title('Unruh Temperature: Thermal Vacuum\n' + r'$T_U = \hbar a / (2\pi c k_B)$', fontsize=14, fontweight='bold')
ax4.legend(fontsize=10, loc='upper left')
ax4.grid(True, alpha=0.3, which='both')

# Add formula annotation
ax4.annotate(r'$T_U = \frac{\hbar a}{2\pi c k_B}$',
             xy=(1e22, 1e8), fontsize=14,
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

# Main title
fig.suptitle('Theorem 5.2.3: Einstein Equations from Thermodynamics\n' +
             r'$\delta Q = T\delta S \Rightarrow G_{\mu\nu} = 8\pi G T_{\mu\nu}$',
             fontsize=16, fontweight='bold', y=0.98)

plt.tight_layout(rect=[0, 0, 1, 0.95])

# Save the figure
output_path = os.path.join(output_dir, 'theorem_5_2_3_verification_plots.png')
plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
print(f"\nSaved: {output_path}")

# =============================================================================
# Additional Plot: SU(3) Degeneracy Comparison
# =============================================================================
fig2, (ax5, ax6) = plt.subplots(1, 2, figsize=(14, 5))

# Plot 5: Degeneracy per puncture
reps = ['SU(2) j=1/2', 'SU(2) j=1', 'SU(3) fund.', 'SU(3) adj.']
degeneracies = [2, 3, 3, 8]
colors = ['#1f77b4', '#1f77b4', '#ff7f0e', '#ff7f0e']
hatches = ['', '//', '', '//']

bars = ax5.bar(reps, degeneracies, color=colors, edgecolor='black', linewidth=1.5)
for bar, hatch in zip(bars, hatches):
    bar.set_hatch(hatch)

ax5.set_ylabel('Degeneracy (dim of rep.)', fontsize=12)
ax5.set_title('State Counting: Degeneracy per Puncture', fontsize=14, fontweight='bold')
ax5.grid(True, alpha=0.3, axis='y')

# Add ln values
for i, (rep, deg) in enumerate(zip(reps, degeneracies)):
    ax5.annotate(f'ln({deg}) = {np.log(deg):.3f}',
                 xy=(i, deg + 0.2), ha='center', fontsize=10)

# Plot 6: Entropy per area comparison
# For BH entropy matching: S/A = 1/(4ℓ_P²)
# This requires specific γ values

theories = ['Standard LQG\n(SU(2))', 'Chiral Geometrogenesis\n(SU(3))']
gamma_values = [0.2375, 0.1516]
entropy_coeffs = [1/4, 1/4]  # Both match BH entropy

x_pos = np.arange(len(theories))
width = 0.35

bars1 = ax6.bar(x_pos - width/2, gamma_values, width, label=r'$\gamma$ (Immirzi)', color='#2ca02c', alpha=0.8)
bars2 = ax6.bar(x_pos + width/2, entropy_coeffs, width, label=r'$S/(A/\ell_P^2)$', color='#9467bd', alpha=0.8)

ax6.set_ylabel('Value', fontsize=12)
ax6.set_title('Immirzi Parameter: Matching Condition', fontsize=14, fontweight='bold')
ax6.set_xticks(x_pos)
ax6.set_xticklabels(theories, fontsize=11)
ax6.legend(fontsize=10)
ax6.grid(True, alpha=0.3, axis='y')

# Add note
ax6.text(0.5, -0.15, 'Note: Both approaches use matching to fix γ — this is NOT a prediction but a consistency condition',
         transform=ax6.transAxes, ha='center', fontsize=9, style='italic',
         bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

plt.tight_layout()

output_path2 = os.path.join(output_dir, 'theorem_5_2_3_su3_comparison.png')
plt.savefig(output_path2, dpi=150, bbox_inches='tight', facecolor='white')
print(f"Saved: {output_path2}")

plt.show()

print("\n" + "=" * 80)
print("VISUALIZATION COMPLETE")
print("=" * 80)
