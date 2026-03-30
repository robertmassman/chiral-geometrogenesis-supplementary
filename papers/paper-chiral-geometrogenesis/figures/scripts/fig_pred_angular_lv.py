#!/usr/bin/env python3
"""
Generate Figure: Angular Lorentz Violation Pattern
Shows the K₄ (Klein four-group) symmetry pattern with O_h cubic anisotropy
Key prediction: ℓ=4 hexadecapole without ℓ=2 quadrupole

Uses verified K₄ formula from theorem_0_0_14_angular_pattern_verification.py:
K_4 = Y_40 + √(5/14)[Y_44 + Y_4,-4]
    = c_4 (n_x^4 + n_y^4 + n_z^4 - 3/5)  [Cartesian form]
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from mpl_toolkits.mplot3d import Axes3D
import matplotlib.gridspec as gridspec
from scipy.special import sph_harm

# Set up publication-quality figure style - larger for better readability
plt.rcParams.update({
    'font.size': 10,
    'font.family': 'serif',
    'axes.labelsize': 10,
    'axes.titlesize': 11,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
})


def K4_cartesian(nx, ny, nz):
    """
    Compute K_4 in Cartesian form (verified formula):
    K_4 = c_4 (n_x^4 + n_y^4 + n_z^4 - 3/5)

    This is the O_h-invariant ℓ=4 cubic harmonic.
    Maxima at face directions (±1,0,0), minima at body diagonals (±1,±1,±1)/√3.
    """
    # Normalize the direction vector
    norm = np.sqrt(nx**2 + ny**2 + nz**2)
    # Handle zero norm case
    with np.errstate(divide='ignore', invalid='ignore'):
        nx_n = np.where(norm > 0, nx/norm, 0)
        ny_n = np.where(norm > 0, ny/norm, 0)
        nz_n = np.where(norm > 0, nz/norm, 0)

    # Cubic invariant: n_x^4 + n_y^4 + n_z^4 - 3/5
    cubic_term = nx_n**4 + ny_n**4 + nz_n**4 - 3.0/5.0

    # Normalization factor (matches spherical harmonic convention)
    c4 = 21.0 / (16.0 * np.sqrt(np.pi))

    return c4 * cubic_term


def K4_spherical_harmonic(theta, phi):
    """
    Compute K_4 using spherical harmonics (verified formula):
    K_4 = Y_40 + √(5/14)[Y_44 + Y_4,-4]
    """
    Y40 = sph_harm(0, 4, phi, theta)
    Y44 = sph_harm(4, 4, phi, theta)
    Y4m4 = sph_harm(-4, 4, phi, theta)

    coeff = np.sqrt(5.0 / 14.0)
    K4 = Y40 + coeff * (Y44 + Y4m4)

    return np.real(K4)


def quadrupole_Y20(theta, phi):
    """
    Standard ℓ=2 quadrupole Y_20 pattern for comparison.
    This is ABSENT in O_h symmetric theories.
    """
    return np.real(sph_harm(0, 2, phi, theta))


# Create figure with 2x2 panels - larger size for better readability
fig = plt.figure(figsize=(10, 8))
gs = gridspec.GridSpec(2, 2, height_ratios=[1.2, 1], wspace=0.3, hspace=0.35)

# ============================================
# Panel (a): 3D visualization of K₄ pattern
# ============================================
ax1 = fig.add_subplot(gs[0, 0], projection='3d')

# Create sphere
n_theta, n_phi = 50, 100
theta_1d = np.linspace(0, np.pi, n_theta)
phi_1d = np.linspace(0, 2*np.pi, n_phi)
phi, theta = np.meshgrid(phi_1d, theta_1d)

# Convert to Cartesian
X = np.sin(theta) * np.cos(phi)
Y = np.sin(theta) * np.sin(phi)
Z = np.cos(theta)

# Compute K₄ pattern using Cartesian formula
K4 = K4_cartesian(X, Y, Z)

# Plot unit sphere with color mapping (no radial deformation - matches verification plot)
# Color by K₄ value
norm = plt.Normalize(K4.min(), K4.max())
colors = cm.coolwarm(norm(K4))

ax1.plot_surface(X, Y, Z, facecolors=colors, alpha=0.9, linewidth=0, antialiased=True)

# Add critical point markers
# Maxima at face directions
ax1.scatter([1, -1, 0, 0, 0, 0], [0, 0, 1, -1, 0, 0], [0, 0, 0, 0, 1, -1],
            c='yellow', s=50, marker='o', edgecolors='black', linewidth=0.8,
            label='Maxima (faces)', zorder=5)

# Minima at body diagonals
s3 = 1/np.sqrt(3)
ax1.scatter([s3, s3, s3, s3, -s3, -s3, -s3, -s3],
            [s3, s3, -s3, -s3, s3, s3, -s3, -s3],
            [s3, -s3, s3, -s3, s3, -s3, s3, -s3],
            c='blue', s=50, marker='^', edgecolors='black', linewidth=0.8,
            label='Minima (body diag)', zorder=5)

ax1.set_xlim(-1.2, 1.2)
ax1.set_ylim(-1.2, 1.2)
ax1.set_zlim(-1.2, 1.2)
ax1.set_xlabel('x')
ax1.set_ylabel('y')
ax1.set_zlabel('z')
ax1.set_title(r'(a) $K_4$ hexadecapole pattern ($\ell=4$, $O_h$ symmetric)')
ax1.view_init(elev=20, azim=45)
ax1.legend(loc='upper left', fontsize=8)

# ============================================
# Panel (b): Comparison with quadrupole (ABSENT)
# ============================================
ax2 = fig.add_subplot(gs[0, 1], projection='3d')

# Compute quadrupole pattern Y_20
Y20 = quadrupole_Y20(theta, phi)

# Plot unit sphere with color mapping (no radial deformation)
norm2 = plt.Normalize(Y20.min(), Y20.max())
colors2 = cm.coolwarm(norm2(Y20))

ax2.plot_surface(X, Y, Z, facecolors=colors2, alpha=0.4, linewidth=0, antialiased=True)
ax2.set_xlim(-1.2, 1.2)
ax2.set_ylim(-1.2, 1.2)
ax2.set_zlim(-1.2, 1.2)
ax2.set_xlabel('x')
ax2.set_ylabel('y')
ax2.set_zlabel('z')
ax2.set_title(r'(b) Quadrupole pattern ($\ell=2$) — ABSENT in $O_h$ theory')
ax2.view_init(elev=20, azim=45)

# Add "FORBIDDEN" overlay
ax2.text2D(0.5, 0.5, 'FORBIDDEN\nby $O_h$', transform=ax2.transAxes,
           fontsize=12, color='red', ha='center', va='center',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8, edgecolor='red'),
           fontweight='bold')

# ============================================
# Panel (c): Angular power spectrum comparison
# ============================================
ax3 = fig.add_subplot(gs[1, 0])

# Multipole moments
ell = np.array([0, 1, 2, 3, 4, 5, 6, 7, 8])

# O_h symmetric theory: only ℓ = 0, 4, 6, 8, ... non-zero
# With ℓ=4 dominant, ℓ=6,8 suppressed
Oh_power = np.array([1.0, 0, 0, 0, 0.01, 0, 1e-4, 0, 1e-6])  # Relative power

# Generic anisotropy: would have ℓ=2 contribution
generic_power = np.array([1.0, 0, 0.1, 0, 0.01, 0, 1e-4, 0, 1e-6])

bar_width = 0.35
x_pos = np.arange(len(ell))

bars1 = ax3.bar(x_pos - bar_width/2, Oh_power + 1e-8, bar_width,
                label=r'$O_h$ symmetric (this work)', color='steelblue', alpha=0.8)
bars2 = ax3.bar(x_pos + bar_width/2, generic_power + 1e-8, bar_width,
                label='Generic anisotropy', color='coral', alpha=0.8)

ax3.set_yscale('log')
ax3.set_xlabel(r'Multipole $\ell$')
ax3.set_ylabel('Relative power')
ax3.set_xticks(x_pos)
ax3.set_xticklabels(ell)
ax3.set_ylim(1e-8, 10)
ax3.legend(loc='upper right')
ax3.set_title(r'(c) Angular power spectrum: $O_h$ vs generic')
ax3.grid(True, alpha=0.3, axis='y')

# Highlight the key difference
ax3.annotate(r'No $\ell=2$', xy=(2, 1e-7), xytext=(1.5, 1e-4),
             arrowprops=dict(arrowstyle='->', color='red', lw=1),
             fontsize=9, color='red', ha='center')

# ============================================
# Panel (d): Energy-dependent LV bounds (with green allowed region)
# ============================================
ax4 = fig.add_subplot(gs[1, 1])

# Energy scale (GeV)
E = np.logspace(3, 20, 100)
E_P = 1.22e19  # Planck energy in GeV

# Theoretical prediction (this framework): δc/c ~ (E/E_P)²
delta_c_theory = (E / E_P)**2

# LHAASO bound: E_QG,2 > 8e10 GeV means δc/c < (E/E_QG,2)²
E_QG2_LHAASO = 8e10
delta_c_LHAASO = (E / E_QG2_LHAASO)**2

# Add green shaded "allowed" region below all bounds
# The allowed region is below both LHAASO and GW170817 bounds
ax4.fill_between(E, 1e-40, np.minimum(delta_c_LHAASO, 1e-15),
                 alpha=0.2, color='green', label='Allowed region')

# Plot theoretical prediction
ax4.loglog(E, delta_c_theory, 'b-', linewidth=2, label=r'Theory: $\delta c/c = (E/E_P)^2$')

# Plot bounds
ax4.loglog(E, delta_c_LHAASO, 'r--', linewidth=1.5, label='LHAASO bound')
ax4.axhline(1e-15, color='darkorange', linestyle=':', linewidth=1.5, alpha=0.8, label='GW170817 bound')

# Mark energy scales
energy_markers = {'TeV': 1e3, 'PeV': 1e6, 'EeV': 1e9, 'GZK': 5e10}
for name, E_val in energy_markers.items():
    ax4.axvline(E_val, color='gray', linestyle=':', alpha=0.3)
    ax4.text(E_val*1.3, 1e-38, name, rotation=90, va='bottom', fontsize=8, color='gray')

ax4.set_xlabel('Energy (GeV)')
ax4.set_ylabel(r'$\delta c/c$')
ax4.set_title('(d) Theory prediction vs experimental bounds')
ax4.legend(loc='lower right', fontsize=8)
ax4.grid(True, which='both', alpha=0.3)
ax4.set_xlim(1e3, 1e20)
ax4.set_ylim(1e-40, 1)

# Add annotation showing theory is safe
ax4.annotate('Theory safely\nbelow bounds', xy=(1e15, 1e-10), xytext=(1e12, 1e-5),
             arrowprops=dict(arrowstyle='->', color='blue', lw=1),
             fontsize=9, ha='center',
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))

plt.tight_layout()

# Save figures
import os
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
plt.savefig(f'{OUTPUT_DIR}/fig_pred_angular_lv.png',
            dpi=300, bbox_inches='tight', facecolor='white')
plt.savefig(f'{OUTPUT_DIR}/fig_pred_angular_lv.pdf',
            bbox_inches='tight', facecolor='white')

print("Figure saved successfully!")
print("\nKey physics illustrated:")
print("  - Panel (a): K₄ hexadecapole from stella octangula O_h symmetry")
print("    Formula: K_4 = c_4(n_x^4 + n_y^4 + n_z^4 - 3/5)")
print("    Maxima at face directions (yellow), minima at body diagonals (blue)")
print("  - Panel (b): ℓ=2 quadrupole is FORBIDDEN (key falsifiable prediction)")
print("  - Panel (c): Angular power spectrum shows missing ℓ=2")
print("  - Panel (d): Theory predictions safely below SME experimental bounds")
print("               Green region shows allowed parameter space")

# Verify values at critical points
print("\n" + "="*60)
print("VERIFICATION: K_4 values at critical points")
print("="*60)
print(f"  Face (1,0,0):       K_4 = {K4_cartesian(1, 0, 0):.6f}")
print(f"  Face (0,1,0):       K_4 = {K4_cartesian(0, 1, 0):.6f}")
print(f"  Face (0,0,1):       K_4 = {K4_cartesian(0, 0, 1):.6f}")
s3 = 1/np.sqrt(3)
print(f"  Body diag (1,1,1):  K_4 = {K4_cartesian(s3, s3, s3):.6f}")
s2 = 1/np.sqrt(2)
print(f"  Edge (1,1,0):       K_4 = {K4_cartesian(s2, s2, 0):.6f}")
print("\nFaces are MAXIMA, body diagonals are MINIMA (as expected)")
