"""
Fiber Bundle Visualization for Theorem 3.0.3
=============================================

This script creates detailed visualizations of the temporal fiber structure:
1. W-axis and color vertices in 3D
2. VEV magnitude maps
3. Phase evolution along the fiber
4. Bundle structure diagram

Author: Verification Agent
Date: 2025-01-14
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import FancyArrowPatch
from mpl_toolkits.mplot3d import proj3d

# ============================================================================
# SETUP: Stella Octangula Geometry  
# ============================================================================

# Color vertices (stella octangula = two interlocked tetrahedra)
R_vertex = np.array([1, -1, -1])
G_vertex = np.array([-1, 1, -1])
B_vertex = np.array([-1, -1, 1])
W_vertex = np.array([1, 1, 1])

# Normalize to unit sphere
R_norm = R_vertex / np.linalg.norm(R_vertex)
G_norm = G_vertex / np.linalg.norm(G_vertex)
B_norm = B_vertex / np.linalg.norm(B_vertex)
W_norm = W_vertex / np.linalg.norm(W_vertex)

# W-direction
W_direction = W_norm

EPSILON = 0.1
A0 = 1.0

def pressure(x, x_c, epsilon=EPSILON):
    """Pressure function P_c(x) = 1/(|x - x_c|² + ε²)"""
    r_sq = np.sum((np.asarray(x) - np.asarray(x_c))**2)
    return 1.0 / (r_sq + epsilon**2)

def compute_vev(x, a0=A0, epsilon=EPSILON):
    """Compute VEV magnitude v_χ(x)."""
    P_R = pressure(x, R_vertex, epsilon)
    P_G = pressure(x, G_vertex, epsilon)
    P_B = pressure(x, B_vertex, epsilon)
    vev_sq = (a0**2 / 2) * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)
    return np.sqrt(max(0, vev_sq))

print("=" * 80)
print("FIBER BUNDLE VISUALIZATION - Theorem 3.0.3")
print("=" * 80)

# ============================================================================
# FIGURE 1: 3D Geometry Overview
# ============================================================================

fig1 = plt.figure(figsize=(16, 6))

# Plot 1a: Stella octangula with W-axis
ax1 = fig1.add_subplot(131, projection='3d')

# Plot color vertices
ax1.scatter(*R_vertex, c='red', s=200, label='R (1,-1,-1)', marker='o', edgecolors='black')
ax1.scatter(*G_vertex, c='green', s=200, label='G (-1,1,-1)', marker='o', edgecolors='black')
ax1.scatter(*B_vertex, c='blue', s=200, label='B (-1,-1,1)', marker='o', edgecolors='black')
ax1.scatter(*W_vertex, c='white', s=200, label='W (1,1,1)', marker='o', edgecolors='black')

# Draw tetrahedron edges (R, G, B form one tetrahedron)
for v1, v2, color in [
    (R_vertex, G_vertex, 'gray'),
    (G_vertex, B_vertex, 'gray'),
    (B_vertex, R_vertex, 'gray'),
]:
    ax1.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]], 
             c=color, linestyle='-', alpha=0.5, linewidth=1)

# W-axis line
t_vals = np.linspace(-2, 2, 50)
W_line = np.array([t * W_direction for t in t_vals])
ax1.plot(W_line[:, 0], W_line[:, 1], W_line[:, 2], 
         'k-', linewidth=3, label='W-axis (nodal line)')

# Draw equidistance lines from a point on W-axis
W_point = 1.5 * W_direction
ax1.scatter(*W_point, c='gold', s=100, marker='*', edgecolors='black')
for v, c in [(R_vertex, 'red'), (G_vertex, 'green'), (B_vertex, 'blue')]:
    ax1.plot([W_point[0], v[0]], [W_point[1], v[1]], [W_point[2], v[2]],
             c=c, linestyle='--', alpha=0.6, linewidth=2)

ax1.set_xlabel('x', fontsize=12)
ax1.set_ylabel('y', fontsize=12)
ax1.set_zlabel('z', fontsize=12)
ax1.set_title('Stella Octangula: W-axis Equidistant from R,G,B', fontsize=12)
ax1.legend(loc='upper left', fontsize=8)

# Plot 1b: VEV in plane perpendicular to W-axis
ax2 = fig1.add_subplot(132)

# Basis vectors perpendicular to W
e1 = np.array([1, -1, 0]) / np.sqrt(2)
e2 = np.array([1, 1, -2]) / np.sqrt(6)

n_grid = 100
extent = 2.5
u_vals = np.linspace(-extent, extent, n_grid)
v_vals = np.linspace(-extent, extent, n_grid)
U, V = np.meshgrid(u_vals, v_vals)

VEV_perp = np.zeros_like(U)
for i in range(n_grid):
    for j in range(n_grid):
        x = U[i, j] * e1 + V[i, j] * e2
        VEV_perp[i, j] = compute_vev(x)

im2 = ax2.contourf(U, V, VEV_perp, levels=50, cmap='magma')
plt.colorbar(im2, ax=ax2, label='VEV v_χ')

# Mark the W-axis (origin)
ax2.plot(0, 0, 'w*', markersize=15, markeredgecolor='black', label='W-axis (v_χ=0)')

# Mark projections of R, G, B vertices
for v, label, c in [(R_vertex, 'R', 'red'), (G_vertex, 'G', 'green'), (B_vertex, 'B', 'blue')]:
    u_proj = np.dot(v, e1)
    v_proj = np.dot(v, e2)
    ax2.plot(u_proj, v_proj, 'o', c=c, markersize=10, markeredgecolor='white', label=label)

ax2.set_xlabel('e₁ direction', fontsize=12)
ax2.set_ylabel('e₂ direction', fontsize=12)
ax2.set_title('VEV in Plane ⟂ to W-axis', fontsize=12)
ax2.legend(fontsize=8)
ax2.set_aspect('equal')

# Plot 1c: VEV along radial directions from W-axis
ax3 = fig1.add_subplot(133)

r_vals = np.linspace(0, 3, 200)

# VEV along e1 direction (perpendicular to W)
vev_e1 = [compute_vev(r * e1) for r in r_vals]

# VEV along e2 direction
vev_e2 = [compute_vev(r * e2) for r in r_vals]

# VEV along a mixed direction
e_mix = (e1 + e2) / np.sqrt(2)
vev_mix = [compute_vev(r * e_mix) for r in r_vals]

# VEV along W-direction (should be zero)
vev_w = [compute_vev(r * W_direction) for r in r_vals]

ax3.plot(r_vals, vev_e1, 'r-', linewidth=2, label='Along e₁')
ax3.plot(r_vals, vev_e2, 'g-', linewidth=2, label='Along e₂')
ax3.plot(r_vals, vev_mix, 'b-', linewidth=2, label='Along (e₁+e₂)/√2')
ax3.plot(r_vals, vev_w, 'k--', linewidth=2, label='Along W-axis')

ax3.set_xlabel('Distance from origin', fontsize=12)
ax3.set_ylabel('VEV v_χ', fontsize=12)
ax3.set_title('VEV vs Distance in Different Directions', fontsize=12)
ax3.legend(fontsize=10)
ax3.grid(True, alpha=0.3)
ax3.set_xlim(0, 3)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_3_0_3_geometry_overview.png',
            dpi=150, bbox_inches='tight')
print("Saved: theorem_3_0_3_geometry_overview.png")

# ============================================================================
# FIGURE 2: Phase Fiber Visualization
# ============================================================================

fig2 = plt.figure(figsize=(16, 6))

# Plot 2a: Phase evolution along the fiber
ax4 = fig2.add_subplot(131)

# At a fixed point off W-axis, show phase evolution
x_fixed = np.array([0.5, 0.2, -0.1])
v_chi_fixed = compute_vev(x_fixed)
Phi_spatial = 0.3  # Fixed spatial phase

lambda_vals = np.linspace(0, 4*np.pi, 500)
phase_vals = (Phi_spatial + lambda_vals) % (2*np.pi)

# Real and imaginary parts of χ
chi_real = v_chi_fixed * np.cos(Phi_spatial + lambda_vals)
chi_imag = v_chi_fixed * np.sin(Phi_spatial + lambda_vals)

ax4.plot(lambda_vals / np.pi, chi_real, 'b-', linewidth=2, label='Re(χ)')
ax4.plot(lambda_vals / np.pi, chi_imag, 'r-', linewidth=2, label='Im(χ)')
ax4.axhline(v_chi_fixed, color='k', linestyle='--', alpha=0.5, label=f'|χ| = {v_chi_fixed:.3f}')
ax4.axhline(-v_chi_fixed, color='k', linestyle='--', alpha=0.5)

ax4.set_xlabel('Internal time λ / π', fontsize=12)
ax4.set_ylabel('χ components', fontsize=12)
ax4.set_title('Phase Evolution: χ(x, λ) = v_χ · e^{i(Φ + λ)}', fontsize=12)
ax4.legend(fontsize=10)
ax4.grid(True, alpha=0.3)

# Plot 2b: Phase in complex plane (circle traversal)
ax5 = fig2.add_subplot(132)

theta_circle = np.linspace(0, 2*np.pi, 100)
ax5.plot(v_chi_fixed * np.cos(theta_circle), 
         v_chi_fixed * np.sin(theta_circle), 
         'k-', linewidth=1, alpha=0.3)

# Show evolution along fiber
n_points = 8
lambda_samples = np.linspace(0, 2*np.pi, n_points, endpoint=False)
colors = plt.cm.viridis(np.linspace(0, 1, n_points))

for i, (lam, col) in enumerate(zip(lambda_samples, colors)):
    chi_val = v_chi_fixed * np.exp(1j * (Phi_spatial + lam))
    ax5.plot(chi_val.real, chi_val.imag, 'o', c=col, markersize=15, 
             markeredgecolor='black')
    ax5.annotate(f'λ={lam/np.pi:.1f}π', (chi_val.real, chi_val.imag),
                 textcoords="offset points", xytext=(8, 5), fontsize=8)

# Draw arrow showing direction of evolution
ax5.annotate('', xy=(v_chi_fixed*0.7, v_chi_fixed*0.7),
             xytext=(v_chi_fixed*0.8, v_chi_fixed*0.5),
             arrowprops=dict(arrowstyle='->', color='green', lw=2))
ax5.text(v_chi_fixed*0.9, v_chi_fixed*0.6, 'λ→', fontsize=12, color='green')

ax5.set_xlabel('Re(χ)', fontsize=12)
ax5.set_ylabel('Im(χ)', fontsize=12)
ax5.set_title('Fiber S¹: Phase Circle at Fixed x', fontsize=12)
ax5.set_aspect('equal')
ax5.grid(True, alpha=0.3)

# Plot 2c: Phase rate dφ/dλ = 1
ax6 = fig2.add_subplot(133)

# Numerical differentiation of phase
d_lambda = 0.01
phase_derivative = []
lambda_test = np.linspace(0, 4*np.pi, 400)

for lam in lambda_test:
    phase_at_lam = Phi_spatial + lam
    phase_at_lam_plus = Phi_spatial + lam + d_lambda
    d_phase = (phase_at_lam_plus - phase_at_lam) / d_lambda
    phase_derivative.append(d_phase)

ax6.plot(lambda_test / np.pi, phase_derivative, 'b-', linewidth=2)
ax6.axhline(1.0, color='r', linestyle='--', linewidth=2, label='dφ/dλ = 1 (expected)')

ax6.set_xlabel('Internal time λ / π', fontsize=12)
ax6.set_ylabel('dφ/dλ', fontsize=12)
ax6.set_title('Angular Velocity: Constant Rotation Rate', fontsize=12)
ax6.legend(fontsize=10)
ax6.grid(True, alpha=0.3)
ax6.set_ylim(0.5, 1.5)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_3_0_3_phase_fiber.png',
            dpi=150, bbox_inches='tight')
print("Saved: theorem_3_0_3_phase_fiber.png")

# ============================================================================
# FIGURE 3: Temporal Fiber Bundle Diagram
# ============================================================================

fig3 = plt.figure(figsize=(16, 10))

# Plot 3a: 3D visualization of fiber bundle
ax7 = fig3.add_subplot(221, projection='3d')

# Create a tube around the W-axis to represent the bundle
# Base circle perpendicular to W at various points along W
theta = np.linspace(0, 2*np.pi, 50)
for t in np.linspace(-1.5, 1.5, 7):
    # Point on W-axis
    center = t * W_direction
    
    # Circle perpendicular to W
    radius = 0.3
    circle_points = []
    for th in theta:
        point = center + radius * (np.cos(th) * e1 + np.sin(th) * e2)
        circle_points.append(point)
    circle_points = np.array(circle_points)
    
    # Color by VEV
    vev_on_circle = [compute_vev(p) for p in circle_points]
    
    ax7.plot(circle_points[:, 0], circle_points[:, 1], circle_points[:, 2], 
             'b-', alpha=0.3, linewidth=1)

# Draw W-axis
ax7.plot(W_line[:, 0], W_line[:, 1], W_line[:, 2], 
         'r-', linewidth=3, label='W-axis (degeneracy locus)')

# Draw fibers at selected points
fiber_points = [
    np.array([0.5, 0.5, -0.3]),
    np.array([0.3, -0.5, 0.1]),
    np.array([-0.4, 0.2, 0.5]),
]

for fp in fiber_points:
    vev = compute_vev(fp)
    ax7.scatter(*fp, c='green', s=100, marker='o')
    
    # Draw fiber circle (small circle at this point)
    fiber_radius = 0.15
    # Fiber is S¹ - draw as a small circle
    for th in theta:
        # Fiber parameterized by phase
        pass  # Just show the base point

ax7.set_xlabel('x', fontsize=10)
ax7.set_ylabel('y', fontsize=10)
ax7.set_zlabel('z', fontsize=10)
ax7.set_title('Fiber Bundle E = (ℝ³ \\ W-axis) × S¹', fontsize=12)
ax7.legend()

# Plot 3b: Schematic of fiber bundle
ax8 = fig3.add_subplot(222)

# Draw schematic
ax8.text(0.5, 0.95, 'FIBER BUNDLE STRUCTURE', fontsize=14, fontweight='bold',
         ha='center', transform=ax8.transAxes)

ax8.text(0.5, 0.85, 'Total Space: E = (ℝ³ \\ W-axis) × S¹', fontsize=11,
         ha='center', transform=ax8.transAxes, style='italic')

# Draw base space
rect_base = plt.Rectangle((0.1, 0.3), 0.35, 0.4, fill=False, edgecolor='blue', linewidth=2)
ax8.add_patch(rect_base)
ax8.text(0.275, 0.35, 'Base B = ℝ³ \\ W-axis', fontsize=10, ha='center')

# Draw fibers
for x_pos in [0.15, 0.25, 0.35]:
    # Fiber as small circle above base point
    circle = plt.Circle((x_pos, 0.6), 0.03, fill=False, edgecolor='green', linewidth=2)
    ax8.add_patch(circle)
    # Projection line
    ax8.plot([x_pos, x_pos], [0.57, 0.4], 'k--', alpha=0.5)

ax8.text(0.25, 0.68, 'Fiber F = S¹', fontsize=10, ha='center', color='green')

# Draw projection arrow
ax8.annotate('', xy=(0.6, 0.45), xytext=(0.6, 0.65),
             arrowprops=dict(arrowstyle='->', color='red', lw=2))
ax8.text(0.7, 0.55, 'π: E → B', fontsize=11, color='red')

# W-axis note
ax8.text(0.275, 0.25, 'W-axis removed\n(VEV = 0, phase undefined)', 
         fontsize=9, ha='center', style='italic', color='gray')

# Bundle triviality note
ax8.text(0.5, 0.12, 'H²(B; ℤ) = 0 ⟹ Bundle is trivial (product)', 
         fontsize=10, ha='center', bbox=dict(boxstyle='round', facecolor='lightyellow'))

ax8.set_xlim(0, 1)
ax8.set_ylim(0, 1)
ax8.axis('off')

# Plot 3c: W-axis as temporal origin
ax9 = fig3.add_subplot(223)

# Radial plot of VEV from W-axis
r_from_w = np.linspace(0, 2, 200)

# Various angles in the plane perpendicular to W
angles = [0, np.pi/4, np.pi/2, 3*np.pi/4, np.pi]
labels = ['θ=0', 'θ=π/4', 'θ=π/2', 'θ=3π/4', 'θ=π']
colors_angle = ['red', 'orange', 'green', 'blue', 'purple']

for angle, label, color in zip(angles, labels, colors_angle):
    direction = np.cos(angle) * e1 + np.sin(angle) * e2
    vev_r = [compute_vev(r * direction) for r in r_from_w]
    ax9.plot(r_from_w, vev_r, c=color, linewidth=2, label=label)

ax9.axvline(0, color='k', linestyle='--', alpha=0.5)
ax9.text(0.05, ax9.get_ylim()[1]*0.9, 'W-axis\n(r=0)', fontsize=10, va='top')

ax9.set_xlabel('Distance from W-axis', fontsize=12)
ax9.set_ylabel('VEV v_χ', fontsize=12)
ax9.set_title('VEV vs Distance from W-axis (Temporal Origin)', fontsize=12)
ax9.legend(fontsize=9, loc='upper right')
ax9.grid(True, alpha=0.3)

# Plot 3d: Phase degeneracy at W-axis
ax10 = fig3.add_subplot(224)

# Show that phase becomes undefined as we approach W-axis
distances = [0.001, 0.01, 0.05, 0.1, 0.5, 1.0]
lambda_range = np.linspace(0, 2*np.pi, 100)

for d in distances:
    x_point = d * e1  # Point at distance d from W-axis
    v_chi = compute_vev(x_point)
    
    if v_chi > 1e-6:
        chi_vals = v_chi * np.exp(1j * lambda_range)
        ax10.plot(chi_vals.real, chi_vals.imag, linewidth=2, 
                  label=f'd={d:.3f}, v_χ={v_chi:.3f}')
    else:
        ax10.plot(0, 0, 'ko', markersize=10)

ax10.plot(0, 0, 'r*', markersize=15, label='W-axis (phase degenerate)')
ax10.set_xlabel('Re(χ)', fontsize=12)
ax10.set_ylabel('Im(χ)', fontsize=12)
ax10.set_title('Phase Circle Shrinks to Point on W-axis', fontsize=12)
ax10.legend(fontsize=8, loc='upper right')
ax10.set_aspect('equal')
ax10.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_3_0_3_fiber_bundle_structure.png',
            dpi=150, bbox_inches='tight')
print("Saved: theorem_3_0_3_fiber_bundle_structure.png")

# ============================================================================
# FIGURE 4: Physical Interpretation Summary
# ============================================================================

fig4 = plt.figure(figsize=(14, 10))

# Create a comprehensive summary figure
ax11 = fig4.add_subplot(111)
ax11.axis('off')

# Title
ax11.text(0.5, 0.98, 'THEOREM 3.0.3: TEMPORAL FIBER STRUCTURE', 
          fontsize=18, fontweight='bold', ha='center', transform=ax11.transAxes)

ax11.text(0.5, 0.93, 'The W-axis as Temporal Direction and Origin of Time', 
          fontsize=14, ha='center', transform=ax11.transAxes, style='italic')

# Main diagram box
summary_text = """
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         THE 4D-TO-TIME BRIDGE                                    │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   24-cell (4D)            Theorem 0.3.1              Theorem 3.0.3              │
│   w-coordinate    ─────────────────────►   W-axis   ─────────────────►   λ     │
│   (4th dimension)        (geometric)     (nodal line)    (dynamical)   (time)  │
│                                                                                  │
│   Key Properties:                                                                │
│                                                                                  │
│   • W-direction = (1,1,1)/√3                                                    │
│   • Equidistant from R, G, B vertices                                           │
│   • Color singlet: P_R = P_G = P_B on W-axis                                    │
│   • VEV = 0 on W-axis (phase undefined)                                         │
│   • VEV > 0 off W-axis (phase evolves via ∂_λχ = iχ)                           │
│                                                                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   FIBER BUNDLE STRUCTURE:                                                        │
│                                                                                  │
│   E = (ℝ³ \\ W-axis) × S¹   (Total space)                                        │
│   B = ℝ³ \\ W-axis          (Base space)                                         │
│   F = S¹                    (Fiber = phase circle)                              │
│                                                                                  │
│   H²(B; ℤ) = 0  ⟹  Bundle is trivial (product)                                 │
│                                                                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   PHYSICAL INTERPRETATION:                                                       │
│                                                                                  │
│   ON W-axis:  χ = 0, phase undefined → "temporal degeneracy"                    │
│   OFF W-axis: χ ≠ 0, phase evolves  → "observable time"                         │
│                                                                                  │
│   Time "begins" when moving off the W-axis!                                      │
│                                                                                  │
│   Result: D = N + 1 = 3 + 1 = 4                                                 │
│           ├── N = 3: R-G-B color space (spatial dimensions)                     │
│           └── +1: W-axis/temporal fiber (time dimension)                        │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
"""

ax11.text(0.5, 0.45, summary_text, fontsize=10, ha='center', va='center',
          transform=ax11.transAxes, family='monospace',
          bbox=dict(boxstyle='round', facecolor='white', edgecolor='black'))

plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_3_0_3_summary_diagram.png',
            dpi=150, bbox_inches='tight')
print("Saved: theorem_3_0_3_summary_diagram.png")

# ============================================================================
# SUMMARY
# ============================================================================

print("\n" + "=" * 80)
print("VISUALIZATION COMPLETE")
print("=" * 80)
print("""
Generated plots:
1. theorem_3_0_3_geometry_overview.png
   - Stella octangula with W-axis
   - VEV in perpendicular plane
   - VEV along various directions

2. theorem_3_0_3_phase_fiber.png
   - Phase evolution vs λ
   - Phase circle traversal
   - Constant angular velocity

3. theorem_3_0_3_fiber_bundle_structure.png
   - 3D fiber bundle visualization
   - Schematic diagram
   - VEV from W-axis
   - Phase degeneracy at W-axis

4. theorem_3_0_3_summary_diagram.png
   - Physical interpretation summary

All plots saved to: verification/plots/
""")

plt.show()
