#!/usr/bin/env python3
"""
Visualization Suite for Theorem 0.2.2 - Internal Time Parameter Emergence

This script generates visualizations demonstrating the key concepts in 
Theorem 0.2.2 (Internal Time Emergence).

Visualizations:
1. Phase evolution trajectory Φ(λ) = ωλ + Φ₀
2. Configuration space (Cartan torus T²)
3. Energy landscape showing flat phase direction
4. Time emergence: λ → t mapping
5. Hamiltonian phase space (Φ, Π_Φ)
6. Oscillation cycle R→G→B→R
7. Quantum uncertainty at Planck scale
8. Bootstrap resolution diagram

Note: The "stella octangula" refers to two interlocked tetrahedra.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Line3DCollection
import matplotlib.patches as mpatches
from matplotlib.colors import LinearSegmentedColormap
import os
import warnings

warnings.filterwarnings('ignore')

# Set plot style
plt.style.use('default')
plt.rcParams['figure.figsize'] = (10, 8)
plt.rcParams['font.size'] = 11
plt.rcParams['axes.labelsize'] = 12
plt.rcParams['axes.titlesize'] = 14
plt.rcParams['legend.fontsize'] = 10


# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

# Color phases
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Stella octangula vertices
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Colors for RGB
COLORS = {'R': '#FF0000', 'G': '#00AA00', 'B': '#0000FF'}

# Physical constants
LAMBDA_QCD_MEV = 200.0
OMEGA_CANONICAL = np.sqrt(2)


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def pressure_function(x, x_c, epsilon=EPSILON):
    dist_squared = np.sum((x - x_c)**2)
    return 1.0 / (dist_squared + epsilon**2)


def energy_density(x, a0=A0, epsilon=EPSILON):
    rho = 0.0
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
        rho += P_c**2
    return a0**2 * rho


def total_chiral_field(x, Phi=0.0, a0=A0, epsilon=EPSILON):
    total = 0.0 + 0.0j
    for c in ['R', 'G', 'B']:
        amplitude = a0 * pressure_function(x, VERTICES_PLUS[c], epsilon)
        phase = PHASES[c] + Phi
        total += amplitude * np.exp(1j * phase)
    return total


# =============================================================================
# VISUALIZATION 1: Phase Evolution
# =============================================================================

def plot_phase_evolution(output_dir):
    """Plot Φ(λ) = ωλ + Φ₀ showing uniform phase evolution."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    omega = OMEGA_CANONICAL
    lambda_vals = np.linspace(0, 4 * np.pi, 500)
    
    # (a) Phase vs lambda
    ax = axes[0, 0]
    Phi = omega * lambda_vals
    ax.plot(lambda_vals, Phi, 'b-', linewidth=2, label=f'Φ(λ) = ωλ, ω = √2')
    ax.axhline(y=2*np.pi, color='gray', linestyle='--', alpha=0.5, label='2π')
    ax.axhline(y=4*np.pi, color='gray', linestyle='--', alpha=0.5)
    ax.set_xlabel('λ (internal parameter)')
    ax.set_ylabel('Φ (overall phase)')
    ax.set_title('(a) Phase Evolution: Φ(λ) = ωλ')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # (b) dΦ/dλ = ω (constant)
    ax = axes[0, 1]
    dPhi_dlambda = omega * np.ones_like(lambda_vals)
    ax.plot(lambda_vals, dPhi_dlambda, 'r-', linewidth=2)
    ax.axhline(y=omega, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('λ (internal time)')
    ax.set_ylabel('dΦ/dλ')
    ax.set_title(f'(b) Constant Frequency: dΦ/dλ = ω = {omega:.4f}')
    ax.set_ylim([0, 2])
    ax.grid(True, alpha=0.3)
    ax.text(6, omega + 0.1, f'ω = √2 ≈ {omega:.4f}', fontsize=12)
    
    # (c) Phase in complex plane
    ax = axes[1, 0]
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(np.cos(theta), np.sin(theta), 'k-', alpha=0.3, linewidth=1)
    
    # Show phase point rotating
    n_points = 20
    for i, lam in enumerate(np.linspace(0, 2*np.pi/omega, n_points)):
        phi = omega * lam
        alpha = 0.3 + 0.7 * i / n_points
        color = plt.cm.viridis(i / n_points)
        ax.plot(np.cos(phi), np.sin(phi), 'o', color=color, markersize=8, alpha=alpha)
    
    # Arrow showing direction
    ax.annotate('', xy=(np.cos(0.5), np.sin(0.5)), xytext=(np.cos(0), np.sin(0)),
                arrowprops=dict(arrowstyle='->', color='blue', lw=2))
    ax.set_xlabel('cos(Φ)')
    ax.set_ylabel('sin(Φ)')
    ax.set_title('(c) Phase Rotation in Complex Plane')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.set_xlim([-1.3, 1.3])
    ax.set_ylim([-1.3, 1.3])
    
    # (d) Physical time emergence
    ax = axes[1, 1]
    t_vals = lambda_vals / omega
    ax.plot(lambda_vals, t_vals, 'g-', linewidth=2, label='t = λ/ω')
    
    # Mark one period
    T = 2 * np.pi / omega
    ax.axvline(x=2*np.pi/omega * omega, color='orange', linestyle='--', alpha=0.7)
    ax.axhline(y=T, color='orange', linestyle='--', alpha=0.7)
    ax.plot([2*np.pi], [T], 'ro', markersize=10, label=f'T = 2π/ω = {T:.3f}')
    
    ax.set_xlabel('λ (internal time)')
    ax.set_ylabel('t (physical time)')
    ax.set_title('(d) Physical Time: t = λ/ω')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_phase_evolution.png'), 
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_phase_evolution.png")


# =============================================================================
# VISUALIZATION 2: Color Phase Cycling R→G→B→R
# =============================================================================

def plot_color_cycling(output_dir):
    """Show how colors cycle R→G→B→R as λ increases."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    omega = OMEGA_CANONICAL
    n_frames = 8
    
    # (a) Individual color phases
    ax = axes[0, 0]
    lambda_vals = np.linspace(0, 3 * 2*np.pi/omega, 500)
    
    for c, color_hex in COLORS.items():
        phase_c = PHASES[c] + omega * lambda_vals
        ax.plot(lambda_vals, np.mod(phase_c, 2*np.pi), '-', color=color_hex, 
                linewidth=2, label=f'φ_{c}(λ)')
    
    ax.set_xlabel('λ')
    ax.set_ylabel('Phase (mod 2π)')
    ax.set_title('(a) Individual Color Phases (cycling)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # (b) Relative phases (constant)
    ax = axes[0, 1]
    delta_GR = 2*np.pi/3 * np.ones_like(lambda_vals)
    delta_BR = 4*np.pi/3 * np.ones_like(lambda_vals)
    
    ax.plot(lambda_vals, delta_GR, 'g-', linewidth=2, label='Δφ_GR = 2π/3')
    ax.plot(lambda_vals, delta_BR, 'b-', linewidth=2, label='Δφ_BR = 4π/3')
    ax.axhline(y=2*np.pi/3, color='green', linestyle='--', alpha=0.5)
    ax.axhline(y=4*np.pi/3, color='blue', linestyle='--', alpha=0.5)
    
    ax.set_xlabel('λ')
    ax.set_ylabel('Relative Phase')
    ax.set_title('(b) Relative Phases (constant)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_ylim([0, 5])
    
    # (c) Color wheel rotation
    ax = axes[1, 0]
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(np.cos(theta), np.sin(theta), 'k-', alpha=0.3, linewidth=1)
    
    # Show R, G, B positions at different times
    times = [0, np.pi/(3*omega), 2*np.pi/(3*omega)]
    markers = ['o', 's', '^']
    
    for t_idx, t in enumerate(times):
        Phi = omega * t
        for c, color_hex in COLORS.items():
            phase = PHASES[c] + Phi
            x = 0.8 * np.cos(phase)
            y = 0.8 * np.sin(phase)
            ax.plot(x, y, markers[t_idx], color=color_hex, markersize=12,
                   label=f'{c} at t={t_idx}' if t_idx == 0 else '')
    
    # Draw arrows showing rotation direction
    for angle in [0, 2*np.pi/3, 4*np.pi/3]:
        ax.annotate('', xy=(0.9*np.cos(angle+0.3), 0.9*np.sin(angle+0.3)),
                   xytext=(0.9*np.cos(angle), 0.9*np.sin(angle)),
                   arrowprops=dict(arrowstyle='->', color='gray', lw=1.5))
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('(c) Color Wheel: R→G→B→R Cycling')
    ax.set_aspect('equal')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)
    ax.set_xlim([-1.2, 1.2])
    ax.set_ylim([-1.2, 1.2])
    
    # Add labels
    for c, color_hex in COLORS.items():
        angle = PHASES[c]
        ax.text(1.05*np.cos(angle), 1.05*np.sin(angle), c, fontsize=14,
               color=color_hex, ha='center', va='center', fontweight='bold')
    
    # (d) Field magnitude at center
    ax = axes[1, 1]
    x_center = np.array([0.0, 0.0, 0.0])
    
    chi_real = []
    chi_imag = []
    chi_mag = []
    
    for lam in lambda_vals:
        chi = total_chiral_field(x_center, Phi=omega*lam)
        chi_real.append(chi.real)
        chi_imag.append(chi.imag)
        chi_mag.append(np.abs(chi))
    
    ax.plot(lambda_vals, chi_real, 'b-', linewidth=1.5, label='Re[χ]', alpha=0.7)
    ax.plot(lambda_vals, chi_imag, 'r-', linewidth=1.5, label='Im[χ]', alpha=0.7)
    ax.plot(lambda_vals, chi_mag, 'k-', linewidth=2, label='|χ|')
    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    
    ax.set_xlabel('λ')
    ax.set_ylabel('χ_total at center')
    ax.set_title('(d) Total Field at Center (χ=0 due to phase cancellation)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_color_cycling.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_color_cycling.png")


# =============================================================================
# VISUALIZATION 3: Hamiltonian Phase Space
# =============================================================================

def plot_hamiltonian_phase_space(output_dir):
    """Visualize the phase space (Φ, Π_Φ) and Hamiltonian flow."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    I = 1.0  # Normalized moment of inertia
    omega = OMEGA_CANONICAL
    
    # (a) Phase space trajectories
    ax = axes[0, 0]
    Phi_range = np.linspace(0, 2*np.pi, 100)
    Pi_range = np.linspace(-3, 3, 50)
    
    # Plot constant energy curves H = Π²/(2I)
    for H in [0.5, 1.0, 1.5, 2.0]:
        Pi_plus = np.sqrt(2 * I * H) * np.ones_like(Phi_range)
        Pi_minus = -np.sqrt(2 * I * H) * np.ones_like(Phi_range)
        ax.plot(Phi_range, Pi_plus, 'b-', alpha=0.6)
        ax.plot(Phi_range, Pi_minus, 'b-', alpha=0.6)
    
    # Mark the actual trajectory
    Pi_Phi = I * omega
    ax.axhline(y=Pi_Phi, color='red', linewidth=2, label=f'Π_Φ = Iω = {Pi_Phi:.3f}')
    ax.axhline(y=-Pi_Phi, color='red', linewidth=2, alpha=0.5)
    
    ax.set_xlabel('Φ')
    ax.set_ylabel('Π_Φ')
    ax.set_title('(a) Phase Space: H = Π_Φ²/(2I)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # (b) Energy landscape (flat in Φ)
    ax = axes[0, 1]
    Phi_2d, Pi_2d = np.meshgrid(Phi_range, Pi_range)
    H_2d = Pi_2d**2 / (2 * I)
    
    contour = ax.contourf(Phi_2d, Pi_2d, H_2d, levels=20, cmap='viridis')
    plt.colorbar(contour, ax=ax, label='H')
    ax.set_xlabel('Φ')
    ax.set_ylabel('Π_Φ')
    ax.set_title('(b) Hamiltonian H = Π_Φ²/(2I) (flat in Φ)')
    
    # (c) Trajectory in time
    ax = axes[1, 0]
    lambda_vals = np.linspace(0, 4 * np.pi / omega, 500)
    Phi_traj = (omega * lambda_vals) % (2 * np.pi)
    Pi_traj = Pi_Phi * np.ones_like(lambda_vals)
    
    # Color by time
    points = np.array([Phi_traj, Pi_traj]).T.reshape(-1, 1, 2)
    segments = np.concatenate([points[:-1], points[1:]], axis=1)
    
    ax.scatter(Phi_traj, Pi_traj, c=lambda_vals, cmap='plasma', s=5)
    ax.set_xlabel('Φ (mod 2π)')
    ax.set_ylabel('Π_Φ')
    ax.set_title('(c) Trajectory: Φ cycles, Π_Φ constant')
    ax.set_xlim([0, 2*np.pi])
    ax.grid(True, alpha=0.3)
    
    # Add colorbar
    sm = plt.cm.ScalarMappable(cmap='plasma', 
                               norm=plt.Normalize(vmin=0, vmax=lambda_vals[-1]))
    sm.set_array([])
    cbar = plt.colorbar(sm, ax=ax)
    cbar.set_label('λ')
    
    # (d) Energy conservation
    ax = axes[1, 1]
    H_vals = Pi_Phi**2 / (2 * I) * np.ones_like(lambda_vals)
    ax.plot(lambda_vals, H_vals, 'g-', linewidth=2)
    ax.axhline(y=Pi_Phi**2/(2*I), color='k', linestyle='--', alpha=0.5)
    
    ax.set_xlabel('λ')
    ax.set_ylabel('H')
    ax.set_title(f'(d) Energy Conservation: H = {Pi_Phi**2/(2*I):.3f} = const')
    ax.set_ylim([0, 2])
    ax.grid(True, alpha=0.3)
    ax.text(2, Pi_Phi**2/(2*I) + 0.1, f'H = Iω²/2 = {Pi_Phi**2/(2*I):.3f}', fontsize=11)
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_hamiltonian.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_hamiltonian.png")


# =============================================================================
# VISUALIZATION 4: Bootstrap Resolution
# =============================================================================

def plot_bootstrap_resolution(output_dir):
    """Diagram showing how the bootstrap circularity is broken."""
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))
    
    # (a) Old circular dependency
    ax = axes[0]
    ax.set_xlim(-1, 5)
    ax.set_ylim(-1, 5)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('(a) OLD: Circular Bootstrap', fontsize=14, fontweight='bold', color='red')
    
    # Boxes for the circularity
    boxes_old = [
        (2, 4, 'Emergent\nMetric g_μν'),
        (4, 2, 'Define ∂_t'),
        (2, 0, 'Time-dependent\nVEV χ(t)'),
        (0, 2, 'Compute T_μν')
    ]
    
    for x, y, text in boxes_old:
        box = mpatches.FancyBboxPatch((x-0.6, y-0.4), 1.2, 0.8,
                                       boxstyle="round,pad=0.05",
                                       facecolor='lightcoral', edgecolor='red', linewidth=2)
        ax.add_patch(box)
        ax.text(x, y, text, ha='center', va='center', fontsize=10)
    
    # Arrows forming circle
    arrow_props = dict(arrowstyle='->', color='red', lw=2,
                       connectionstyle='arc3,rad=0.2')
    ax.annotate('', xy=(3.5, 2.3), xytext=(2.5, 3.6), arrowprops=arrow_props)
    ax.annotate('', xy=(2.5, 0.4), xytext=(3.5, 1.7), arrowprops=arrow_props)
    ax.annotate('', xy=(0.5, 1.7), xytext=(1.5, 0.4), arrowprops=arrow_props)
    ax.annotate('', xy=(1.5, 3.6), xytext=(0.5, 2.3), arrowprops=arrow_props)
    
    # Big X
    ax.text(2, 2, '✗', fontsize=60, ha='center', va='center', color='darkred', alpha=0.3)
    ax.text(2, -0.8, 'CIRCULAR!', fontsize=14, ha='center', color='red', fontweight='bold')
    
    # (b) New non-circular resolution
    ax = axes[1]
    ax.set_xlim(-0.5, 5.5)
    ax.set_ylim(-0.5, 5)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('(b) NEW: Bootstrap Resolved', fontsize=14, fontweight='bold', color='green')
    
    # Vertical flow
    boxes_new = [
        (2.5, 4.5, 'Internal λ\n(no external time)', 'lightgreen'),
        (2.5, 3.2, 'Phase evolution\n∂_λχ = iχ', 'lightgreen'),
        (2.5, 1.9, 'χ(λ) well-defined\nT_μν computable', 'lightgreen'),
        (2.5, 0.6, 'Metric emerges\nt = λ/ω', 'lightblue')
    ]
    
    for x, y, text, color in boxes_new:
        box = mpatches.FancyBboxPatch((x-0.8, y-0.4), 1.6, 0.7,
                                       boxstyle="round,pad=0.05",
                                       facecolor=color, edgecolor='darkgreen', linewidth=2)
        ax.add_patch(box)
        ax.text(x, y, text, ha='center', va='center', fontsize=9)
    
    # Arrows (downward flow)
    for i in range(3):
        y_start = boxes_new[i][1] - 0.4
        y_end = boxes_new[i+1][1] + 0.4
        ax.annotate('', xy=(2.5, y_end), xytext=(2.5, y_start),
                   arrowprops=dict(arrowstyle='->', color='green', lw=2))
    
    # Checkmark
    ax.text(4.5, 2.5, '✓', fontsize=50, ha='center', va='center', color='darkgreen', alpha=0.5)
    ax.text(2.5, -0.3, 'NO CIRCULARITY', fontsize=14, ha='center', color='green', fontweight='bold')
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_bootstrap.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_bootstrap.png")


# =============================================================================
# VISUALIZATION 5: Time Derivative Verification
# =============================================================================

def plot_time_derivative(output_dir):
    """Visualize ∂_λχ = iχ relationship."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    omega = OMEGA_CANONICAL
    test_point = np.array([0.3, 0.2, 0.1])
    
    # (a) χ(λ) in complex plane
    ax = axes[0, 0]
    lambda_vals = np.linspace(0, 2*np.pi, 200)
    
    chi_real = []
    chi_imag = []
    for lam in lambda_vals:
        chi = total_chiral_field(test_point, Phi=lam)
        chi_real.append(chi.real)
        chi_imag.append(chi.imag)
    
    chi_real = np.array(chi_real)
    chi_imag = np.array(chi_imag)
    
    # Color by λ
    sc = ax.scatter(chi_real, chi_imag, c=lambda_vals, cmap='viridis', s=10)
    plt.colorbar(sc, ax=ax, label='λ')
    
    ax.set_xlabel('Re[χ]')
    ax.set_ylabel('Im[χ]')
    ax.set_title(f'(a) χ(λ) at x = {test_point.tolist()}')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    
    # (b) Real and Imaginary parts vs λ
    ax = axes[0, 1]
    ax.plot(lambda_vals, chi_real, 'b-', linewidth=2, label='Re[χ]')
    ax.plot(lambda_vals, chi_imag, 'r-', linewidth=2, label='Im[χ]')
    ax.set_xlabel('λ')
    ax.set_ylabel('χ components')
    ax.set_title('(b) χ Components vs λ')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # (c) Verify ∂_λχ = iχ
    ax = axes[1, 0]
    
    # Numerical derivative
    dchi_dlambda = np.gradient(chi_real + 1j*chi_imag, lambda_vals)
    
    # Expected: iχ
    chi_complex = chi_real + 1j*chi_imag
    expected = 1j * chi_complex
    
    ax.plot(lambda_vals, np.real(dchi_dlambda), 'b-', linewidth=2, label='Re[∂_λχ] (numerical)')
    ax.plot(lambda_vals, np.real(expected), 'b--', linewidth=1.5, label='Re[iχ] (expected)')
    ax.plot(lambda_vals, np.imag(dchi_dlambda), 'r-', linewidth=2, label='Im[∂_λχ] (numerical)')
    ax.plot(lambda_vals, np.imag(expected), 'r--', linewidth=1.5, label='Im[iχ] (expected)')
    
    ax.set_xlabel('λ')
    ax.set_ylabel('Derivative')
    ax.set_title('(c) Verification: ∂_λχ = iχ')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # (d) Error
    ax = axes[1, 1]
    error = np.abs(dchi_dlambda - expected)
    ax.semilogy(lambda_vals, error, 'k-', linewidth=2)
    ax.set_xlabel('λ')
    ax.set_ylabel('|∂_λχ - iχ|')
    ax.set_title('(d) Numerical Error (should be small)')
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_derivative.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_derivative.png")


# =============================================================================
# VISUALIZATION 6: Summary Diagram
# =============================================================================

def plot_summary(output_dir):
    """Create a summary diagram of Theorem 0.2.2."""
    fig = plt.figure(figsize=(16, 12))
    
    # Main title
    fig.suptitle('Theorem 0.2.2: Internal Time Parameter Emergence\n'
                 'Time Emerges from Phase Evolution Without External Clock',
                 fontsize=16, fontweight='bold', y=0.98)
    
    # Create grid of subplots
    gs = fig.add_gridspec(3, 4, hspace=0.35, wspace=0.3)
    
    omega = OMEGA_CANONICAL
    
    # (a) Phase evolution
    ax1 = fig.add_subplot(gs[0, 0:2])
    lambda_vals = np.linspace(0, 4*np.pi, 200)
    ax1.plot(lambda_vals, omega * lambda_vals, 'b-', linewidth=2)
    ax1.set_xlabel('λ (internal parameter)')
    ax1.set_ylabel('Φ (phase)')
    ax1.set_title('Phase Evolution: Φ(λ) = ωλ')
    ax1.grid(True, alpha=0.3)
    
    # (b) Frequency derivation
    ax2 = fig.add_subplot(gs[0, 2:4])
    ax2.text(0.5, 0.7, r'$\omega = \sqrt{\frac{2H}{I}}$', fontsize=20, 
            ha='center', transform=ax2.transAxes)
    ax2.text(0.5, 0.4, f'For I = E_total: ω = √2 ≈ {omega:.4f}', fontsize=12,
            ha='center', transform=ax2.transAxes)
    ax2.text(0.5, 0.15, 'Mechanism: DERIVED\nScale: INPUT from QCD', fontsize=10,
            ha='center', transform=ax2.transAxes)
    ax2.set_title('Frequency from Hamiltonian')
    ax2.axis('off')
    
    # (c) Color cycling
    ax3 = fig.add_subplot(gs[1, 0])
    theta = np.linspace(0, 2*np.pi, 100)
    ax3.plot(np.cos(theta), np.sin(theta), 'k-', alpha=0.3)
    for c, color in COLORS.items():
        angle = PHASES[c]
        ax3.plot(0.8*np.cos(angle), 0.8*np.sin(angle), 'o', color=color, markersize=15)
        ax3.text(1.1*np.cos(angle), 1.1*np.sin(angle), c, fontsize=12,
                ha='center', va='center', fontweight='bold', color=color)
    # Arrow
    ax3.annotate('', xy=(0.7*np.cos(0.3), 0.7*np.sin(0.3)),
                xytext=(0.7*np.cos(0), 0.7*np.sin(0)),
                arrowprops=dict(arrowstyle='->', lw=2))
    ax3.set_aspect('equal')
    ax3.set_xlim([-1.4, 1.4])
    ax3.set_ylim([-1.4, 1.4])
    ax3.set_title('R→G→B Cycling')
    ax3.axis('off')
    
    # (d) Time emergence
    ax4 = fig.add_subplot(gs[1, 1:3])
    ax4.text(0.5, 0.8, 'Physical Time Emergence', fontsize=14, fontweight='bold',
            ha='center', transform=ax4.transAxes)
    ax4.text(0.5, 0.55, r'$t = \frac{\lambda}{\omega}$', fontsize=18,
            ha='center', transform=ax4.transAxes)
    ax4.text(0.5, 0.3, r'Period: $T = \frac{2\pi}{\omega}$', fontsize=14,
            ha='center', transform=ax4.transAxes)
    ax4.text(0.5, 0.1, 'Time from counting oscillations', fontsize=11,
            ha='center', transform=ax4.transAxes, style='italic')
    ax4.axis('off')
    
    # (e) Diffeomorphism
    ax5 = fig.add_subplot(gs[1, 3])
    ax5.text(0.5, 0.85, 't is a diffeomorphism:', fontsize=11, fontweight='bold',
            ha='center', transform=ax5.transAxes)
    ax5.text(0.1, 0.65, '✓ Smooth (C∞)', fontsize=10, transform=ax5.transAxes)
    ax5.text(0.1, 0.50, '✓ Injective (dt/dλ > 0)', fontsize=10, transform=ax5.transAxes)
    ax5.text(0.1, 0.35, '✓ Surjective (t ∈ ℝ)', fontsize=10, transform=ax5.transAxes)
    ax5.text(0.1, 0.20, '✓ Continuous inverse', fontsize=10, transform=ax5.transAxes)
    ax5.set_title('Coordinate Properties')
    ax5.axis('off')
    
    # (f) Hamilton's equations
    ax6 = fig.add_subplot(gs[2, 0:2])
    ax6.text(0.5, 0.85, "Hamilton's Equations", fontsize=12, fontweight='bold',
            ha='center', transform=ax6.transAxes)
    ax6.text(0.5, 0.65, r'$H = \frac{\Pi_\Phi^2}{2I}$', fontsize=14,
            ha='center', transform=ax6.transAxes)
    ax6.text(0.3, 0.4, r'$\dot{\Phi} = \frac{\partial H}{\partial \Pi_\Phi} = \omega$', 
            fontsize=12, transform=ax6.transAxes)
    ax6.text(0.3, 0.2, r'$\dot{\Pi}_\Phi = -\frac{\partial H}{\partial \Phi} = 0$',
            fontsize=12, transform=ax6.transAxes)
    ax6.text(0.5, 0.02, 'Solution: Φ(λ) = ωλ + Φ₀', fontsize=11,
            ha='center', transform=ax6.transAxes, style='italic')
    ax6.axis('off')
    
    # (g) Key results box
    ax7 = fig.add_subplot(gs[2, 2:4])
    ax7.set_xlim(0, 1)
    ax7.set_ylim(0, 1)
    
    # Box
    box = mpatches.FancyBboxPatch((0.05, 0.05), 0.9, 0.9,
                                   boxstyle="round,pad=0.02",
                                   facecolor='lightyellow', edgecolor='orange', linewidth=2)
    ax7.add_patch(box)
    
    ax7.text(0.5, 0.92, 'KEY RESULTS', fontsize=12, fontweight='bold',
            ha='center', transform=ax7.transAxes)
    
    results = [
        '• λ emerges internally (no external time)',
        '• I = E_total (moment of inertia = energy)',
        '• ω = √2 (canonical frequency)',
        '• t = λ/ω is a diffeomorphism',
        '• ∂_λχ = iχ (enables mass generation)',
        '• Bootstrap circularity BROKEN'
    ]
    
    for i, r in enumerate(results):
        ax7.text(0.08, 0.78 - i*0.12, r, fontsize=10, transform=ax7.transAxes)
    
    ax7.axis('off')
    
    plt.savefig(os.path.join(output_dir, 'theorem_0_2_2_summary.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: theorem_0_2_2_summary.png")


# =============================================================================
# MAIN
# =============================================================================

def generate_all_visualizations(output_dir=None):
    """Generate all visualizations for Theorem 0.2.2."""
    
    if output_dir is None:
        output_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 
                                  '..', 'plots')
    
    os.makedirs(output_dir, exist_ok=True)
    
    print("\n" + "="*70)
    print("THEOREM 0.2.2: VISUALIZATION SUITE")
    print("="*70)
    print(f"\nOutput directory: {output_dir}\n")
    
    print("Generating visualizations:")
    plot_phase_evolution(output_dir)
    plot_color_cycling(output_dir)
    plot_hamiltonian_phase_space(output_dir)
    plot_bootstrap_resolution(output_dir)
    plot_time_derivative(output_dir)
    plot_summary(output_dir)
    
    print("\n" + "="*70)
    print("All visualizations generated successfully!")
    print("="*70)


if __name__ == '__main__':
    generate_all_visualizations()
