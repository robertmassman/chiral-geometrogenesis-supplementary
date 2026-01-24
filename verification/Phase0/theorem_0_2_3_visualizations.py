#!/usr/bin/env python3
"""
Visualization Module: Theorem 0.2.3 - Stable Convergence Point

Creates comprehensive visualizations for Theorem 0.2.3 claims:
1. Pressure equality at the stella octangula center
2. Field cancellation vs energy persistence
3. Phase-lock stability and Lyapunov decay
4. Single-hadron anisotropy vs ensemble isotropy
5. Alpha coefficient stability region
6. 3D stella octangula structure with observation region

The stella octangula is the compound of two interlocked tetrahedra, 
forming an 8-pointed star polyhedron that serves as the pre-geometric
boundary structure in Chiral Geometrogenesis.

Reference: docs/proofs/Phase0/Theorem-0.2.3-Stable-Convergence-Point.md

Author: Verification Suite  
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.colors import LinearSegmentedColormap
import matplotlib.patheffects as pe
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
from pathlib import Path
from scipy.integrate import solve_ivp
import warnings
warnings.filterwarnings('ignore')

# Import verification functions
from theorem_0_2_3_verification import (
    PARAMS, X_R, X_G, X_B, X_Y, VERTICES_RGB, VERTICES_ALL, VERTICES_ANTI,
    pressure_function, total_field_magnitude_squared, energy_density,
    alpha_coefficient, compute_matrix_M, dynamical_jacobian,
    simulate_phase_decay, so3_average_matrix
)

# ============================================================================
# CONFIGURATION
# ============================================================================

# Plot style settings
plt.rcParams.update({
    'figure.facecolor': 'white',
    'axes.facecolor': 'white',
    'axes.grid': True,
    'grid.alpha': 0.3,
    'font.size': 11,
    'axes.titlesize': 13,
    'axes.labelsize': 11,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'legend.fontsize': 10,
    'figure.dpi': 150,
})

# Color scheme
COLORS = {
    'R': '#E53935',  # Red
    'G': '#43A047',  # Green  
    'B': '#1E88E5',  # Blue
    'center': '#FFD700',  # Gold
    'stable': '#4CAF50',  # Green
    'unstable': '#F44336',  # Red
    'neutral': '#9E9E9E',  # Gray
}


# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def get_output_dir() -> Path:
    """Get output directory for plots."""
    output_dir = Path(__file__).parent.parent / 'plots'
    output_dir.mkdir(exist_ok=True)
    return output_dir


def draw_tetrahedron_edges(ax, vertices, color='black', alpha=0.5, 
                          linewidth=1, linestyle='-'):
    """Draw edges of a tetrahedron given its vertices."""
    edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
    for i, j in edges:
        ax.plot(
            [vertices[i, 0], vertices[j, 0]],
            [vertices[i, 1], vertices[j, 1]],
            [vertices[i, 2], vertices[j, 2]],
            color=color, alpha=alpha, linewidth=linewidth, linestyle=linestyle
        )


def add_sphere_wireframe(ax, radius=1.0, alpha=0.1, color='gray'):
    """Add wireframe sphere to 3D axes."""
    u = np.linspace(0, 2*np.pi, 20)
    v = np.linspace(0, np.pi, 15)
    x = radius * np.outer(np.cos(u), np.sin(v))
    y = radius * np.outer(np.sin(u), np.sin(v))
    z = radius * np.outer(np.ones_like(u), np.cos(v))
    ax.plot_wireframe(x, y, z, alpha=alpha, color=color, linewidth=0.5)


# ============================================================================
# VISUALIZATION FUNCTIONS
# ============================================================================

def plot_stella_octangula_3d(output_dir: Path) -> str:
    """
    Create 3D visualization of the stella octangula showing:
    - Two interlocked tetrahedra
    - Color vertices (R, G, B, Y)
    - Central convergence point O
    - Observation region sphere
    """
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # First tetrahedron (R, G, B, Y vertices)
    T1_colors = ['red', 'green', 'blue', 'purple']
    T1_labels = ['R', 'G', 'B', 'Y']
    
    for i, (v, c, l) in enumerate(zip(VERTICES_ALL, T1_colors, T1_labels)):
        ax.scatter(*v, color=c, s=150, edgecolors='black', linewidths=1.5, zorder=5)
        offset = 1.15
        ax.text(v[0]*offset, v[1]*offset, v[2]*offset, l, 
               fontsize=14, fontweight='bold', color=c,
               ha='center', va='center')
    
    # Draw first tetrahedron edges
    draw_tetrahedron_edges(ax, VERTICES_ALL, color='black', alpha=0.6, linewidth=1.5)
    
    # Second tetrahedron (anti-vertices)
    for v in VERTICES_ANTI:
        ax.scatter(*v, color='gray', s=100, alpha=0.6, 
                  edgecolors='black', linewidths=1)
    draw_tetrahedron_edges(ax, VERTICES_ANTI, color='gray', alpha=0.3, 
                          linewidth=1, linestyle='--')
    
    # Central convergence point O
    ax.scatter(0, 0, 0, color=COLORS['center'], s=400, marker='*', 
              edgecolors='black', linewidths=2, zorder=10, label='Center O')
    ax.text(0.15, 0.15, 0.15, 'O', fontsize=16, fontweight='bold',
           color=COLORS['center'],
           path_effects=[pe.withStroke(linewidth=2, foreground='black')])
    
    # Draw lines from center to RGB vertices
    for v, c in zip(VERTICES_RGB, ['red', 'green', 'blue']):
        ax.plot([0, v[0]], [0, v[1]], [0, v[2]], 
               color=c, alpha=0.5, linewidth=2, linestyle=':')
    
    # Add observation region sphere (scaled for visibility)
    obs_radius = PARAMS.epsilon * 0.8  # Scaled for visualization
    u = np.linspace(0, 2*np.pi, 30)
    v = np.linspace(0, np.pi, 20)
    x = obs_radius * np.outer(np.cos(u), np.sin(v))
    y = obs_radius * np.outer(np.sin(u), np.sin(v))
    z = obs_radius * np.outer(np.ones_like(u), np.cos(v))
    ax.plot_surface(x, y, z, alpha=0.2, color='gold', linewidth=0)
    
    # Labels and formatting
    ax.set_xlabel('X', fontsize=12)
    ax.set_ylabel('Y', fontsize=12)
    ax.set_zlabel('Z', fontsize=12)
    ax.set_title('Stella Octangula: Two Interlocked Tetrahedra\n'
                'Center O is the Stable Convergence Point', fontsize=14)
    
    ax.set_xlim([-1.2, 1.2])
    ax.set_ylim([-1.2, 1.2])
    ax.set_zlim([-1.2, 1.2])
    
    # Add legend
    ax.legend(loc='upper left', fontsize=10)
    
    # Add text annotation
    textstr = f'ε = {PARAMS.epsilon}\n$R_{{obs}}$ = ε×$R_{{stella}}$'
    fig.text(0.02, 0.02, textstr, fontsize=10, 
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_stella_octangula_3d.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_pressure_equality(output_dir: Path) -> str:
    """
    Visualize pressure functions along principal axis.
    Shows P_R = P_G = P_B at center.
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Left: Pressure along x-axis
    x_range = np.linspace(-1.5, 1.5, 300)
    
    P_R_vals = [pressure_function(np.array([x, 0, 0]), X_R) for x in x_range]
    P_G_vals = [pressure_function(np.array([x, 0, 0]), X_G) for x in x_range]
    P_B_vals = [pressure_function(np.array([x, 0, 0]), X_B) for x in x_range]
    
    ax1.plot(x_range, P_R_vals, color=COLORS['R'], linewidth=2.5, label='$P_R$')
    ax1.plot(x_range, P_G_vals, color=COLORS['G'], linewidth=2.5, label='$P_G$')
    ax1.plot(x_range, P_B_vals, color=COLORS['B'], linewidth=2.5, label='$P_B$')
    
    # Mark center point
    P_0 = 1 / (1 + PARAMS.epsilon**2)
    ax1.axvline(x=0, color='black', linestyle='--', alpha=0.5)
    ax1.scatter([0, 0, 0], [P_0, P_0, P_0], color=COLORS['center'], 
               s=100, zorder=5, marker='o', edgecolors='black')
    ax1.axhline(y=P_0, color='gold', linestyle=':', alpha=0.7, 
               label=f'$P_0$ = {P_0:.3f}')
    
    ax1.set_xlabel('x coordinate', fontsize=12)
    ax1.set_ylabel('Pressure P(x, 0, 0)', fontsize=12)
    ax1.set_title(f'Pressure Functions Along x-axis\n'
                 f'$P_R(0) = P_G(0) = P_B(0) = P_0 = 1/(1+ε²)$', fontsize=13)
    ax1.legend(loc='best')
    ax1.set_ylim([0, max(P_R_vals) * 1.1])
    
    # Right: Pressure contours in x-y plane
    x_grid = np.linspace(-1.2, 1.2, 100)
    y_grid = np.linspace(-1.2, 1.2, 100)
    X, Y = np.meshgrid(x_grid, y_grid)
    
    # Total pressure
    P_total = np.zeros_like(X)
    for i in range(len(x_grid)):
        for j in range(len(y_grid)):
            point = np.array([X[i,j], Y[i,j], 0])
            P_total[i,j] = sum(pressure_function(point, v) for v in VERTICES_RGB)
    
    contour = ax2.contourf(X, Y, P_total, levels=30, cmap='viridis')
    plt.colorbar(contour, ax=ax2, label='$Σ_c P_c(x)$')
    
    # Mark vertices (projected to z=0)
    for v, c, l in zip(VERTICES_RGB, ['red', 'green', 'blue'], ['R', 'G', 'B']):
        ax2.scatter(v[0], v[1], color=c, s=100, edgecolors='white', linewidths=2)
        ax2.text(v[0]+0.1, v[1]+0.1, l, fontsize=11, color='white', fontweight='bold')
    
    # Mark center
    ax2.scatter(0, 0, color=COLORS['center'], s=200, marker='*', 
               edgecolors='black', linewidths=2, zorder=5)
    
    ax2.set_xlabel('x', fontsize=12)
    ax2.set_ylabel('y', fontsize=12)
    ax2.set_title('Total Pressure (z=0 slice)\nMaximum at Center', fontsize=13)
    ax2.set_aspect('equal')
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_pressure_equality_detailed.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_field_vs_energy(output_dir: Path) -> str:
    """
    Compare coherent field |χ|² (vanishes at center) 
    vs incoherent energy ρ (persists at center).
    """
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))
    
    x_range = np.linspace(-1.0, 1.0, 100)
    y_range = np.linspace(-1.0, 1.0, 100)
    X, Y = np.meshgrid(x_range, y_range)
    
    chi_squared = np.zeros_like(X)
    rho = np.zeros_like(X)
    
    for i in range(len(x_range)):
        for j in range(len(y_range)):
            point = np.array([X[i,j], Y[i,j], 0])
            chi_squared[i,j] = total_field_magnitude_squared(point)
            rho[i,j] = energy_density(point)
    
    # Panel 1: Coherent field |χ|²
    im1 = axes[0].contourf(X, Y, chi_squared, levels=50, cmap='viridis')
    plt.colorbar(im1, ax=axes[0], label='$|χ_{total}|²$')
    axes[0].contour(X, Y, chi_squared, levels=[1e-6], colors='white', linewidths=2)
    axes[0].scatter(0, 0, color='white', s=150, marker='*', edgecolors='black')
    axes[0].set_title('Coherent Field $|χ_{total}|²$\n(Vanishes at center)', fontsize=12)
    axes[0].set_xlabel('x')
    axes[0].set_ylabel('y')
    
    # Panel 2: Incoherent energy ρ
    im2 = axes[1].contourf(X, Y, rho, levels=50, cmap='plasma')
    plt.colorbar(im2, ax=axes[1], label='$ρ(x)$')
    axes[1].scatter(0, 0, color='white', s=150, marker='*', edgecolors='black')
    axes[1].set_title('Energy Density $ρ(x)$\n(Non-zero at center)', fontsize=12)
    axes[1].set_xlabel('x')
    axes[1].set_ylabel('y')
    
    # Panel 3: Radial profiles
    r_vals = np.linspace(0, 1.2, 100)
    chi_radial = [total_field_magnitude_squared(np.array([r, 0, 0])) for r in r_vals]
    rho_radial = [energy_density(np.array([r, 0, 0])) for r in r_vals]
    
    # Normalize for comparison
    chi_max = max(chi_radial)
    rho_max = max(rho_radial)
    
    axes[2].plot(r_vals, np.array(chi_radial)/chi_max, 'b-', linewidth=2, 
                label='$|χ|²$ (normalized)')
    axes[2].plot(r_vals, np.array(rho_radial)/rho_max, 'r-', linewidth=2, 
                label='$ρ$ (normalized)')
    axes[2].axvline(x=0, color='gold', linestyle='--', alpha=0.7, label='Center')
    
    # Mark the key point
    rho_0 = energy_density(np.zeros(3)) / rho_max
    axes[2].scatter([0], [0], color='blue', s=100, zorder=5, marker='o')
    axes[2].scatter([0], [rho_0], color='red', s=100, zorder=5, marker='o')
    
    axes[2].annotate('$|χ|² = 0$', xy=(0, 0), xytext=(0.2, 0.15),
                    fontsize=11, color='blue',
                    arrowprops=dict(arrowstyle='->', color='blue'))
    axes[2].annotate('$ρ ≠ 0$', xy=(0, rho_0), xytext=(0.2, rho_0 + 0.1),
                    fontsize=11, color='red',
                    arrowprops=dict(arrowstyle='->', color='red'))
    
    axes[2].set_xlabel('Radial distance r', fontsize=12)
    axes[2].set_ylabel('Normalized value', fontsize=12)
    axes[2].set_title('Radial Profiles\n(Field vanishes, energy persists)', fontsize=12)
    axes[2].legend(loc='best')
    axes[2].set_xlim([0, 1.2])
    axes[2].set_ylim([0, 1.1])
    
    for ax in axes[:2]:
        ax.set_aspect('equal')
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_field_vs_energy_detailed.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_phase_stability(output_dir: Path) -> str:
    """
    Visualize phase-lock stability:
    - 120° phase configuration
    - Hessian eigenvalues (energy stability)
    - Jacobian eigenvalues (dynamical stability)
    - Lyapunov decay of perturbations
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    # Panel 1: Phase configuration (polar plot)
    ax1 = fig.add_subplot(221, polar=True)
    
    phases = [0, 2*np.pi/3, 4*np.pi/3]
    colors = [COLORS['R'], COLORS['G'], COLORS['B']]
    labels = ['$φ_R = 0°$', '$φ_G = 120°$', '$φ_B = 240°$']
    
    for phi, c, lbl in zip(phases, colors, labels):
        ax1.annotate('', xy=(phi, 1), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=c, lw=3))
        ax1.scatter(phi, 1, color=c, s=200, zorder=5, edgecolors='black', linewidths=2)
        ax1.text(phi, 1.25, lbl, fontsize=11, ha='center', fontweight='bold', color=c)
    
    # Sum to zero at center
    ax1.scatter(0, 0, color=COLORS['center'], s=300, marker='*', zorder=10,
               edgecolors='black', linewidths=2)
    ax1.text(0.5, 0.3, '$Σe^{iφ_c} = 0$', fontsize=12, fontweight='bold',
            color=COLORS['center'])
    
    ax1.set_title('120° Phase Configuration\n(Color phases sum to zero)', fontsize=13)
    ax1.set_ylim([0, 1.5])
    
    # Panel 2: Eigenvalue spectrum
    ax2 = axes[0, 1]
    
    K = PARAMS.K
    hess_eigs = [3*K/4, 9*K/4]
    jac_eigs = [-3*K/2, -3*K/2]
    
    x_positions = [0, 1, 3, 4]
    eigenvalues = hess_eigs + jac_eigs
    colors_eig = [COLORS['stable'], COLORS['stable'], 
                  COLORS['stable'], COLORS['stable']]
    labels_eig = ['$λ_1^{H}$', '$λ_2^{H}$', '$λ_1^{J}$', '$λ_2^{J}$']
    
    bars = ax2.bar(x_positions, eigenvalues, color=colors_eig, edgecolor='black',
                  width=0.6)
    
    ax2.axhline(y=0, color='black', linestyle='-', linewidth=1)
    ax2.set_xticks(x_positions)
    ax2.set_xticklabels(labels_eig, fontsize=11)
    
    # Add values on bars
    for bar, val in zip(bars, eigenvalues):
        height = bar.get_height()
        ax2.text(bar.get_x() + bar.get_width()/2., height + 0.05 * np.sign(height),
                f'{val:.2f}', ha='center', va='bottom' if height > 0 else 'top',
                fontsize=10, fontweight='bold')
    
    ax2.set_ylabel('Eigenvalue', fontsize=12)
    ax2.set_title('Stability Eigenvalues\n(Hessian > 0 → minimum; Jacobian < 0 → stable)', 
                 fontsize=12)
    
    # Add regions
    ax2.axhspan(0, 3, alpha=0.1, color='green', label='Stable region')
    ax2.axhspan(-2, 0, alpha=0.1, color='red')
    ax2.text(0.5, 2.5, 'Energy\nminimum', fontsize=10, ha='center')
    ax2.text(3.5, -1.0, 'Asymptotically\nstable', fontsize=10, ha='center')
    
    # Panel 3: Phase perturbation decay
    ax3 = axes[1, 0]
    
    psi_0 = np.array([0.3, -0.2])
    t, deviation = simulate_phase_decay(psi_0, t_max=15, n_points=300)
    
    ax3.semilogy(t, deviation, 'b-', linewidth=2, label='Numerical simulation')
    
    # Theoretical decay
    decay_rate = 3 * K / 2
    theoretical = np.linalg.norm(psi_0) * np.exp(-decay_rate * t)
    ax3.semilogy(t, theoretical, 'r--', linewidth=2, 
                label=f'$e^{{-3K/2 · t}}$ (rate = {decay_rate:.2f})')
    
    ax3.set_xlabel('Time t', fontsize=12)
    ax3.set_ylabel('Perturbation |δψ|', fontsize=12)
    ax3.set_title('Lyapunov Stability: Phase Perturbation Decay', fontsize=12)
    ax3.legend(loc='best')
    
    ax3.annotate(f'Initial: ψ₀ = ({psi_0[0]:.1f}, {psi_0[1]:.1f})',
                xy=(0.05, 0.95), xycoords='axes fraction', fontsize=10)
    
    # Panel 4: Stability diagram in (ε, α) space
    ax4 = axes[1, 1]
    
    eps_range = np.linspace(0.01, 0.7, 100)
    alpha_vals = [alpha_coefficient(PARAMS.a0, e) for e in eps_range]
    eps_crit = 1/np.sqrt(3)
    
    ax4.plot(eps_range, alpha_vals, 'k-', linewidth=2)
    ax4.axhline(y=0, color='gray', linestyle='-', linewidth=1)
    ax4.axvline(x=eps_crit, color='red', linestyle='--', linewidth=1.5,
               label=f'$ε_{{crit}} = 1/√3 ≈ {eps_crit:.3f}$')
    ax4.axvline(x=PARAMS.epsilon, color='green', linestyle='-', linewidth=2,
               label=f'Physical ε = {PARAMS.epsilon}')
    
    # Fill stable/unstable regions
    ax4.fill_between(eps_range, alpha_vals, where=np.array(alpha_vals) > 0,
                    alpha=0.3, color='green', label='Stable (α > 0)')
    ax4.fill_between(eps_range, alpha_vals, where=np.array(alpha_vals) < 0,
                    alpha=0.3, color='red', label='Unstable (α < 0)')
    
    ax4.set_xlabel('Regularization parameter ε', fontsize=12)
    ax4.set_ylabel('Energy coefficient α', fontsize=12)
    ax4.set_title('Stability Region in (ε, α) Space\n'
                 '$α = 2a₀²(1-3ε²)/(1+ε²)⁴$', fontsize=12)
    ax4.legend(loc='best', fontsize=9)
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_phase_stability.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_anisotropy_averaging(output_dir: Path) -> str:
    """
    Visualize single-hadron anisotropy vs ensemble isotropy:
    - Matrix M eigenvalues {1/3, 4/3, 4/3}
    - SO(3) averaging to identity
    """
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))
    
    # Panel 1: Single-hadron anisotropy (vertex geometry)
    ax1 = fig.add_subplot(131, projection='3d')
    
    # Plot RGB vertices
    for v, c, l in zip(VERTICES_RGB, ['red', 'green', 'blue'], ['R', 'G', 'B']):
        ax1.scatter(*v, color=c, s=150, edgecolors='black', linewidths=2)
        ax1.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, l, fontsize=12, color=c, fontweight='bold')
    
    # Draw edges
    edges = [(0,1), (0,2), (1,2)]
    for i, j in edges:
        ax1.plot([VERTICES_RGB[i,0], VERTICES_RGB[j,0]],
                [VERTICES_RGB[i,1], VERTICES_RGB[j,1]],
                [VERTICES_RGB[i,2], VERTICES_RGB[j,2]],
                'k-', alpha=0.5, linewidth=1.5)
    
    # Center
    ax1.scatter(0, 0, 0, color=COLORS['center'], s=200, marker='*', 
               edgecolors='black', linewidths=2)
    
    # Anisotropy direction: Σx_c = (1,1,-1)/√3
    sum_dir = (X_R + X_G + X_B)
    sum_dir_norm = sum_dir / np.linalg.norm(sum_dir)
    scale = 0.8
    ax1.quiver(0, 0, 0, sum_dir_norm[0]*scale, sum_dir_norm[1]*scale, sum_dir_norm[2]*scale,
              color='purple', arrow_length_ratio=0.15, linewidth=2)
    ax1.text(sum_dir_norm[0]*scale*1.2, sum_dir_norm[1]*scale*1.2, sum_dir_norm[2]*scale*1.2,
            'Anisotropy\naxis', fontsize=10, color='purple')
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Single-Hadron Geometry\n(Has preferred direction)', fontsize=12)
    ax1.set_xlim([-1, 1])
    ax1.set_ylim([-1, 1])
    ax1.set_zlim([-1, 1])
    
    # Panel 2: Matrix M eigenvalues
    ax2 = axes[1]
    
    M = compute_matrix_M()
    eigenvalues = np.sort(np.linalg.eigvalsh(M))
    expected = [1/3, 4/3, 4/3]
    
    x_pos = np.arange(3)
    bars = ax2.bar(x_pos - 0.15, eigenvalues, width=0.3, color='blue', 
                  edgecolor='black', label='Computed')
    ax2.bar(x_pos + 0.15, expected, width=0.3, color='orange', alpha=0.7,
           edgecolor='black', label='Expected')
    
    ax2.axhline(y=1.0, color='gray', linestyle='--', linewidth=1.5,
               label='Isotropic value')
    
    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(['$λ_1 = 1/3$', '$λ_2 = 4/3$', '$λ_3 = 4/3$'])
    ax2.set_ylabel('Eigenvalue', fontsize=12)
    ax2.set_title('Matrix M Eigenvalues\n$M_{ij} = Σ_c (x_c)_i (x_c)_j$', fontsize=12)
    ax2.legend(loc='best')
    
    # Add annotation
    ax2.annotate('Anisotropic:\neigenvalues ≠ 1', xy=(0, 1/3), xytext=(0.5, 0.6),
                fontsize=10, arrowprops=dict(arrowstyle='->', color='blue'))
    
    # Panel 3: SO(3) averaging result
    ax3 = axes[2]
    
    # Compute averaged matrix (small sample for speed)
    print("Computing SO(3) average (may take a moment)...")
    M_avg, _ = so3_average_matrix(M, n_samples=2000)
    avg_eigenvalues = np.sort(np.linalg.eigvalsh(M_avg))
    
    x_pos = np.arange(3)
    ax3.bar(x_pos - 0.15, avg_eigenvalues, width=0.3, color='green',
           edgecolor='black', label='⟨M⟩ eigenvalues')
    ax3.bar(x_pos + 0.15, [1, 1, 1], width=0.3, color='gold', alpha=0.7,
           edgecolor='black', label='Expected (identity)')
    
    ax3.axhline(y=1.0, color='gray', linestyle='--', linewidth=1.5)
    
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels(['$λ_1$', '$λ_2$', '$λ_3$'])
    ax3.set_ylabel('Eigenvalue', fontsize=12)
    ax3.set_title('After SO(3) Averaging\n$⟨M⟩_{SO(3)} = I$ (Isotropic)', fontsize=12)
    ax3.legend(loc='best')
    ax3.set_ylim([0.9, 1.1])
    
    ax3.annotate('Isotropic:\nall eigenvalues ≈ 1', xy=(1, 1.0), xytext=(0.3, 1.05),
                fontsize=10, arrowprops=dict(arrowstyle='->', color='green'))
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_anisotropy_averaging.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_observation_region(output_dir: Path) -> str:
    """
    Visualize the observation region R_obs = ε × R_stella
    and its physical interpretation.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Panel 1: Observation region in energy landscape
    ax1 = axes[0]
    
    x_range = np.linspace(-1.2, 1.2, 100)
    y_range = np.linspace(-1.2, 1.2, 100)
    X, Y = np.meshgrid(x_range, y_range)
    
    rho = np.zeros_like(X)
    for i in range(len(x_range)):
        for j in range(len(y_range)):
            rho[i,j] = energy_density(np.array([X[i,j], Y[i,j], 0]))
    
    contour = ax1.contourf(X, Y, rho, levels=50, cmap='plasma')
    plt.colorbar(contour, ax=ax1, label='Energy density ρ(x)')
    
    # Draw observation region circle
    R_obs = PARAMS.epsilon
    circle = plt.Circle((0, 0), R_obs, fill=False, color='white', 
                        linewidth=3, linestyle='--', label=f'$R_{{obs}}$ = {R_obs:.2f}')
    ax1.add_patch(circle)
    
    # Mark center
    ax1.scatter(0, 0, color=COLORS['center'], s=200, marker='*',
               edgecolors='black', linewidths=2, zorder=5)
    
    # Mark vertices
    for v, c in zip(VERTICES_RGB, ['red', 'green', 'blue']):
        ax1.scatter(v[0], v[1], color=c, s=100, edgecolors='white', linewidths=2)
    
    ax1.set_xlabel('x', fontsize=12)
    ax1.set_ylabel('y', fontsize=12)
    ax1.set_title('Observation Region (z=0 slice)\n'
                 f'$R_{{obs}} = ε × R_{{stella}} = {PARAMS.epsilon} × {PARAMS.R_stella_fm:.3f}$ fm',
                 fontsize=12)
    ax1.set_aspect('equal')
    ax1.legend(loc='upper right')
    
    # Panel 2: Physical scales comparison
    ax2 = axes[1]
    
    scales = {
        '$R_{stella}$': PARAMS.R_stella_fm,
        '$R_{obs}$': PARAMS.R_obs_fm,
        '$λ_{penetration}$': 0.22,
        '$\\bar{λ}_π/(2π)$': 1.41 / (2*np.pi),
    }
    
    names = list(scales.keys())
    values = list(scales.values())
    colors = ['blue', 'gold', 'green', 'purple']
    
    bars = ax2.barh(names, values, color=colors, edgecolor='black', alpha=0.8)
    
    # Add values on bars
    for bar, val in zip(bars, values):
        ax2.text(val + 0.02, bar.get_y() + bar.get_height()/2,
                f'{val:.3f} fm', va='center', fontsize=11)
    
    ax2.set_xlabel('Length (fm)', fontsize=12)
    ax2.set_title('Physical Length Scales\n'
                 '(Observation radius matches QCD scales)', fontsize=12)
    ax2.set_xlim([0, max(values) * 1.4])
    
    # Add annotation
    ax2.annotate('$R_{obs} ≈ λ_{penetration}$\n(QCD flux tube scale)',
                xy=(0.22, 1), xytext=(0.35, 1.5),
                fontsize=10, arrowprops=dict(arrowstyle='->', color='green'))
    
    plt.tight_layout()
    
    plot_path = output_dir / 'theorem_0_2_3_observation_region.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


def plot_summary_diagram(output_dir: Path) -> str:
    """
    Create comprehensive summary diagram of Theorem 0.2.3.
    """
    fig = plt.figure(figsize=(16, 12))
    
    # Main title
    fig.suptitle('Theorem 0.2.3: Stable Convergence Point\n'
                'The Center of the Stella Octangula', fontsize=16, fontweight='bold')
    
    # Panel 1: 3D structure
    ax1 = fig.add_subplot(231, projection='3d')
    
    for i, (v, c) in enumerate(zip(VERTICES_ALL, ['red', 'green', 'blue', 'purple'])):
        ax1.scatter(*v, color=c, s=100, edgecolors='black')
    draw_tetrahedron_edges(ax1, VERTICES_ALL, alpha=0.4)
    ax1.scatter(0, 0, 0, color='gold', s=200, marker='*', edgecolors='black')
    ax1.set_title('Stella Octangula\nGeometry', fontsize=11)
    ax1.set_xlim([-1, 1])
    ax1.set_ylim([-1, 1])
    ax1.set_zlim([-1, 1])
    
    # Panel 2: Phase configuration
    ax2 = fig.add_subplot(232, polar=True)
    for phi, c in zip([0, 2*np.pi/3, 4*np.pi/3], ['red', 'green', 'blue']):
        ax2.arrow(0, 0, phi, 0.9, head_width=0.1, color=c, linewidth=2)
        ax2.scatter(phi, 1, color=c, s=100, zorder=5)
    ax2.scatter(0, 0, color='gold', s=150, marker='*')
    ax2.set_title('120° Phase Lock\n$Σe^{iφ_c} = 0$', fontsize=11)
    
    # Panel 3: Energy profile
    ax3 = fig.add_subplot(233)
    r = np.linspace(-1, 1, 100)
    chi = [total_field_magnitude_squared(np.array([x, 0, 0])) for x in r]
    rho = [energy_density(np.array([x, 0, 0])) for x in r]
    ax3.plot(r, chi, 'b-', linewidth=2, label='$|χ|²$ (vanishes)')
    ax3.plot(r, rho, 'r-', linewidth=2, label='$ρ$ (persists)')
    ax3.axvline(0, color='gold', linestyle='--', alpha=0.7)
    ax3.scatter([0], [0], color='blue', s=80)
    ax3.scatter([0], [rho[50]], color='red', s=80)
    ax3.set_xlabel('x')
    ax3.legend(fontsize=9)
    ax3.set_title('Field vs Energy\nat Center', fontsize=11)
    
    # Panel 4: Stability eigenvalues
    ax4 = fig.add_subplot(234)
    K = PARAMS.K
    eigs = [3*K/4, 9*K/4, -3*K/2, -3*K/2]
    labels = ['$H^{red}_1$', '$H^{red}_2$', '$J^{red}_1$', '$J^{red}_2$']
    colors = ['green', 'green', 'blue', 'blue']
    ax4.bar(range(4), eigs, color=colors, edgecolor='black')
    ax4.axhline(0, color='black', linewidth=1)
    ax4.set_xticks(range(4))
    ax4.set_xticklabels(labels)
    ax4.set_ylabel('Eigenvalue')
    ax4.set_title('Stability Analysis\n(H>0, J<0 → Stable)', fontsize=11)
    
    # Panel 5: α vs ε
    ax5 = fig.add_subplot(235)
    eps = np.linspace(0.01, 0.65, 100)
    alpha = [alpha_coefficient(1, e) for e in eps]
    ax5.plot(eps, alpha, 'k-', linewidth=2)
    ax5.axhline(0, color='gray')
    ax5.axvline(1/np.sqrt(3), color='red', linestyle='--', label='$ε_{crit}$')
    ax5.axvline(PARAMS.epsilon, color='green', linewidth=2, label='Physical ε')
    ax5.fill_between(eps, alpha, where=np.array(alpha)>0, alpha=0.3, color='green')
    ax5.set_xlabel('ε')
    ax5.set_ylabel('α')
    ax5.legend(fontsize=9)
    ax5.set_title('Stability Regime\n$α > 0$ for ε < 0.577', fontsize=11)
    
    # Panel 6: Summary box
    ax6 = fig.add_subplot(236)
    ax6.axis('off')
    
    summary_text = """
KEY RESULTS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Equal Pressure at Center
   P_R(0) = P_G(0) = P_B(0) = P₀

2. Field Vanishes, Energy Persists
   |χ_total(0)|² = 0, but ρ(0) ≠ 0

3. Phase-Lock Stability
   H^red eigenvalues: {3K/4, 9K/4} > 0
   J^red eigenvalues: {-3K/2, -3K/2} < 0

4. Macroscopic Isotropy
   ⟨M⟩_{SO(3)} = I (ensemble average)

5. Observation Radius
   R_obs = ε × R_stella ≈ 0.22 fm

6. Uniqueness
   Center is the UNIQUE stable point
━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Physical Meaning:
The center is where observers can exist -
flat spacetime emerges from the dynamics.
"""
    ax6.text(0.05, 0.95, summary_text, transform=ax6.transAxes,
            fontsize=10, family='monospace', va='top',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
    
    plt.tight_layout(rect=[0, 0, 1, 0.95])
    
    plot_path = output_dir / 'theorem_0_2_3_summary.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    
    return str(plot_path)


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def create_all_visualizations() -> list:
    """Generate all visualization plots."""
    output_dir = get_output_dir()
    
    print("=" * 60)
    print("THEOREM 0.2.3 VISUALIZATIONS")
    print("=" * 60)
    
    plots = []
    
    viz_functions = [
        ('Stella Octangula 3D', plot_stella_octangula_3d),
        ('Pressure Equality', plot_pressure_equality),
        ('Field vs Energy', plot_field_vs_energy),
        ('Phase Stability', plot_phase_stability),
        ('Anisotropy Averaging', plot_anisotropy_averaging),
        ('Observation Region', plot_observation_region),
        ('Summary Diagram', plot_summary_diagram),
    ]
    
    for name, func in viz_functions:
        print(f"\nGenerating: {name}...", end=' ')
        try:
            path = func(output_dir)
            plots.append(path)
            print("✓")
        except Exception as e:
            print(f"✗ Error: {e}")
    
    print("\n" + "=" * 60)
    print(f"Generated {len(plots)} plots in: {output_dir}")
    print("=" * 60)
    
    return plots


if __name__ == '__main__':
    plots = create_all_visualizations()
    print("\nPlots created:")
    for p in plots:
        print(f"  - {p}")
