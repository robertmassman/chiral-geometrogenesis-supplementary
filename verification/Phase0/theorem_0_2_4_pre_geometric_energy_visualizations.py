#!/usr/bin/env python3
"""
Visualizations for Theorem 0.2.4: Pre-Lorentzian Energy Functional

This module generates plots to visualize the key aspects of Theorem 0.2.4:
1. Phase cancellation at the symmetric configuration
2. Mexican hat potential with phase constraints
3. Energy landscape in configuration space
4. Spatial variation of |χ_total|² and energy density
5. Level 1 ↔ Level 2 correspondence
6. Gradient term structure

Reference: docs/proofs/Phase0/Theorem-0.2.4-Pre-Geometric-Energy-Functional.md

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.colors import Normalize
from mpl_toolkits.mplot3d import Axes3D
from pathlib import Path
import warnings

# Import from verification module
from theorem_0_2_4_pre_geometric_energy_verification import (
    PARAMS, X_R, X_G, X_B, VERTICES_RGB,
    pressure_function, compute_chi_total_squared,
    energy_functional_level1, energy_at_symmetric_point,
    chi_total_at_position, gradient_chi_total,
    energy_density_incoherent, gradient_energy_density
)

# Output directory for plots
PLOT_DIR = Path(__file__).parent.parent / 'plots'
PLOT_DIR.mkdir(exist_ok=True)


def set_plot_style():
    """Set consistent plot style."""
    plt.rcParams.update({
        'font.size': 12,
        'axes.titlesize': 14,
        'axes.labelsize': 12,
        'xtick.labelsize': 10,
        'ytick.labelsize': 10,
        'legend.fontsize': 10,
        'figure.figsize': (10, 8),
        'figure.dpi': 150,
        'savefig.dpi': 150,
        'savefig.bbox': 'tight'
    })


def plot_phase_cancellation():
    """
    Plot demonstrating phase cancellation at the symmetric configuration.
    
    Shows: 1 + e^{i2π/3} + e^{i4π/3} = 0
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Plot 1: Complex plane with three unit vectors
    ax1 = axes[0]
    
    phases = [0, 2*np.pi/3, 4*np.pi/3]
    colors = ['red', 'green', 'blue']
    labels = ['R: e^{i0}', 'G: e^{i2π/3}', 'B: e^{i4π/3}']
    
    # Plot unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, label='Unit circle')
    
    # Plot phase vectors
    for phi, color, label in zip(phases, colors, labels):
        ax1.arrow(0, 0, np.cos(phi), np.sin(phi), 
                  head_width=0.08, head_length=0.05, fc=color, ec=color,
                  label=label, linewidth=2)
    
    # Sum of vectors
    total = sum(np.exp(1j * phi) for phi in phases)
    ax1.plot([0], [0], 'ko', markersize=10, label=f'Sum = {np.abs(total):.2e}')
    
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.axhline(y=0, color='k', linewidth=0.5)
    ax1.axvline(x=0, color='k', linewidth=0.5)
    ax1.grid(True, alpha=0.3)
    ax1.legend(loc='upper right')
    ax1.set_xlabel('Real')
    ax1.set_ylabel('Imaginary')
    ax1.set_title('Phase Cancellation: 1 + e^{i2π/3} + e^{i4π/3} = 0')
    
    # Plot 2: |χ_total|² vs amplitude asymmetry
    ax2 = axes[1]
    
    # Fix a_R = a_B = 1, vary a_G
    a_G_values = np.linspace(0.5, 2.0, 100)
    chi_sq_values = []
    
    for a_G in a_G_values:
        amps = np.array([1.0, a_G, 1.0])
        chi_sq = compute_chi_total_squared(amps)
        chi_sq_values.append(chi_sq)
    
    ax2.plot(a_G_values, chi_sq_values, 'b-', linewidth=2)
    ax2.axvline(x=1.0, color='r', linestyle='--', label='Symmetric (a_G = 1)')
    ax2.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    
    # Mark minimum
    min_idx = np.argmin(chi_sq_values)
    ax2.plot(a_G_values[min_idx], chi_sq_values[min_idx], 'ro', 
             markersize=10, label=f'Min at a_G = {a_G_values[min_idx]:.2f}')
    
    ax2.set_xlabel('a_G (with a_R = a_B = 1)')
    ax2.set_ylabel('|χ_total|²')
    ax2.set_title('|χ_total|² vs. Amplitude Asymmetry')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_phase_cancellation.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_phase_cancellation.png'}")


def plot_mexican_hat_potential():
    """
    Plot the Mexican hat potential V(χ) = λ(|χ|² - v₀²)².
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    v0 = PARAMS.v0
    lambda_chi = PARAMS.lambda_chi
    
    # Plot 1: 2D Mexican hat potential
    ax1 = axes[0]
    
    chi_sq = np.linspace(0, 2.5 * v0**2, 200)
    V = lambda_chi * (chi_sq - v0**2)**2
    
    ax1.plot(chi_sq, V, 'b-', linewidth=2)
    ax1.axvline(x=v0**2, color='g', linestyle='--', label=f'VEV: |χ|² = v₀² = {v0**2}')
    ax1.axvline(x=0, color='r', linestyle='--', label='Symmetric: |χ|² = 0')
    
    ax1.scatter([0], [lambda_chi * v0**4], color='r', s=100, zorder=5,
                label=f'V(0) = λv₀⁴ = {lambda_chi * v0**4:.2f}')
    ax1.scatter([v0**2], [0], color='g', s=100, zorder=5,
                label='V(v₀²) = 0')
    
    ax1.set_xlabel('|χ|²')
    ax1.set_ylabel('V(χ)')
    ax1.set_title('Mexican Hat Potential: V = λ(|χ|² - v₀²)²')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: 3D visualization
    ax2 = fig.add_subplot(122, projection='3d')
    
    # Create radial grid in complex χ plane
    r = np.linspace(0, 1.8, 50)
    theta = np.linspace(0, 2*np.pi, 50)
    R, Theta = np.meshgrid(r, theta)
    X = R * np.cos(Theta)
    Y = R * np.sin(Theta)
    
    # Potential as function of |χ|² = r²
    V_3d = lambda_chi * (R**2 - v0**2)**2
    
    surf = ax2.plot_surface(X, Y, V_3d, cmap=cm.coolwarm, alpha=0.8)
    
    # Mark the VEV circle
    theta_vev = np.linspace(0, 2*np.pi, 100)
    x_vev = v0 * np.cos(theta_vev)
    y_vev = v0 * np.sin(theta_vev)
    z_vev = np.zeros_like(theta_vev)
    ax2.plot(x_vev, y_vev, z_vev, 'g-', linewidth=3, label='VEV circle')
    
    ax2.set_xlabel('Re(χ)')
    ax2.set_ylabel('Im(χ)')
    ax2.set_zlabel('V(χ)')
    ax2.set_title('Mexican Hat Potential in 3D')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_mexican_hat.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_mexican_hat.png'}")


def plot_energy_landscape():
    """
    Plot the energy landscape in amplitude configuration space.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    lambda_chi = PARAMS.lambda_chi
    v0 = PARAMS.v0
    
    # Plot 1: Energy vs symmetric amplitude
    ax1 = axes[0, 0]
    
    a_values = np.linspace(0, 3, 100)
    E_values = [energy_functional_level1(np.array([a, a, a])) for a in a_values]
    
    ax1.plot(a_values, E_values, 'b-', linewidth=2)
    ax1.axhline(y=lambda_chi * v0**4, color='r', linestyle='--', 
                label=f'λv₀⁴ = {lambda_chi * v0**4:.2f}')
    
    # Mark symmetric point at a=1
    E_sym = energy_at_symmetric_point()
    ax1.scatter([1.0], [E_sym], color='r', s=100, zorder=5,
                label=f'E_sym = {E_sym:.2f}')
    
    ax1.set_xlabel('Symmetric amplitude a (a_R = a_G = a_B = a)')
    ax1.set_ylabel('Energy E[χ]')
    ax1.set_title('Energy at Symmetric Configuration')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Energy contour in (a_R, a_G) space with a_B = 1
    ax2 = axes[0, 1]
    
    a_range = np.linspace(0.1, 2.5, 80)
    A_R, A_G = np.meshgrid(a_range, a_range)
    E_grid = np.zeros_like(A_R)
    
    for i in range(A_R.shape[0]):
        for j in range(A_R.shape[1]):
            amps = np.array([A_R[i, j], A_G[i, j], 1.0])
            E_grid[i, j] = energy_functional_level1(amps)
    
    contour = ax2.contourf(A_R, A_G, E_grid, levels=30, cmap='viridis')
    plt.colorbar(contour, ax=ax2, label='Energy')
    
    # Mark symmetric point
    ax2.scatter([1.0], [1.0], color='r', s=100, marker='*', 
                label='Symmetric point')
    
    ax2.set_xlabel('a_R')
    ax2.set_ylabel('a_G')
    ax2.set_title('Energy Landscape (a_B = 1 fixed)')
    ax2.legend()
    
    # Plot 3: |χ_total|² contour
    ax3 = axes[1, 0]
    
    chi_sq_grid = np.zeros_like(A_R)
    for i in range(A_R.shape[0]):
        for j in range(A_R.shape[1]):
            amps = np.array([A_R[i, j], A_G[i, j], 1.0])
            chi_sq_grid[i, j] = compute_chi_total_squared(amps)
    
    contour3 = ax3.contourf(A_R, A_G, chi_sq_grid, levels=30, cmap='plasma')
    plt.colorbar(contour3, ax=ax3, label='|χ_total|²')
    
    # Mark where |χ|² = 0
    ax3.contour(A_R, A_G, chi_sq_grid, levels=[0.01], colors='white', linewidths=2)
    ax3.scatter([1.0], [1.0], color='white', s=100, marker='*',
                label='|χ|² = 0')
    
    ax3.set_xlabel('a_R')
    ax3.set_ylabel('a_G')
    ax3.set_title('|χ_total|² Landscape (a_B = 1 fixed)')
    ax3.legend()
    
    # Plot 4: Potential energy contour
    ax4 = axes[1, 1]
    
    V_grid = lambda_chi * (chi_sq_grid - v0**2)**2
    
    contour4 = ax4.contourf(A_R, A_G, V_grid, levels=30, cmap='hot')
    plt.colorbar(contour4, ax=ax4, label='Potential V')
    
    # Mark maximum (symmetric) and minimum (VEV)
    ax4.scatter([1.0], [1.0], color='cyan', s=100, marker='*',
                label='Symmetric (V = max)')
    
    ax4.set_xlabel('a_R')
    ax4.set_ylabel('a_G')
    ax4.set_title('Potential V = λ(|χ|² - v₀²)² (a_B = 1 fixed)')
    ax4.legend()
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_energy_landscape.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_energy_landscape.png'}")


def plot_spatial_variation():
    """
    Plot spatial variation of fields and energy density.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    a0 = PARAMS.a0
    epsilon = PARAMS.epsilon
    
    # Plot 1: |χ_total|² along different directions
    ax1 = axes[0, 0]
    
    directions = {
        'x-axis': np.array([1, 0, 0]),
        'y-axis': np.array([0, 1, 0]),
        'z-axis': np.array([0, 0, 1]),
        'diagonal (111)': np.array([1, 1, 1]) / np.sqrt(3),
        'toward R vertex': X_R
    }
    
    distances = np.linspace(-2, 2, 200)
    
    for name, direction in directions.items():
        chi_sq_profile = []
        for d in distances:
            pos = d * direction
            chi = chi_total_at_position(pos, a0, epsilon)
            chi_sq_profile.append(np.abs(chi)**2)
        ax1.plot(distances, chi_sq_profile, label=name, linewidth=1.5)
    
    ax1.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    ax1.axvline(x=0, color='k', linestyle='--', alpha=0.5, label='Center')
    
    ax1.set_xlabel('Distance from center')
    ax1.set_ylabel('|χ_total|²')
    ax1.set_title('|χ_total|² Radial Profiles')
    ax1.legend(loc='upper right', fontsize=8)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Energy density ρ(x) along same directions
    ax2 = axes[0, 1]
    
    for name, direction in directions.items():
        rho_profile = []
        for d in distances:
            pos = d * direction
            rho = energy_density_incoherent(pos, a0, epsilon)
            rho_profile.append(rho)
        ax2.plot(distances, rho_profile, label=name, linewidth=1.5)
    
    ax2.axvline(x=0, color='k', linestyle='--', alpha=0.5)
    
    ax2.set_xlabel('Distance from center')
    ax2.set_ylabel('ρ(x) = a₀²Σ P_c²')
    ax2.set_title('Energy Density Radial Profiles')
    ax2.legend(loc='upper right', fontsize=8)
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: 2D slice through z=0 plane - |χ_total|²
    ax3 = axes[1, 0]
    
    x_range = np.linspace(-2, 2, 100)
    y_range = np.linspace(-2, 2, 100)
    X, Y = np.meshgrid(x_range, y_range)
    chi_sq_2d = np.zeros_like(X)
    
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            pos = np.array([X[i, j], Y[i, j], 0])
            chi = chi_total_at_position(pos, a0, epsilon)
            chi_sq_2d[i, j] = np.abs(chi)**2
    
    contour3 = ax3.contourf(X, Y, chi_sq_2d, levels=30, cmap='coolwarm')
    plt.colorbar(contour3, ax=ax3, label='|χ_total|²')
    
    # Mark vertex projections
    for x_c, color, name in zip(VERTICES_RGB, ['r', 'g', 'b'], ['R', 'G', 'B']):
        ax3.scatter([x_c[0]], [x_c[1]], color=color, s=100, marker='^',
                    edgecolors='white', linewidths=2, label=name)
    
    ax3.scatter([0], [0], color='black', s=100, marker='o', label='Center')
    ax3.set_xlabel('x')
    ax3.set_ylabel('y')
    ax3.set_title('|χ_total|² in z=0 Plane')
    ax3.legend(loc='upper right')
    ax3.set_aspect('equal')
    
    # Plot 4: 2D slice - Energy density
    ax4 = axes[1, 1]
    
    rho_2d = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            pos = np.array([X[i, j], Y[i, j], 0])
            rho_2d[i, j] = energy_density_incoherent(pos, a0, epsilon)
    
    contour4 = ax4.contourf(X, Y, rho_2d, levels=30, cmap='hot')
    plt.colorbar(contour4, ax=ax4, label='ρ(x)')
    
    for x_c, color, name in zip(VERTICES_RGB, ['r', 'g', 'b'], ['R', 'G', 'B']):
        ax4.scatter([x_c[0]], [x_c[1]], color=color, s=100, marker='^',
                    edgecolors='white', linewidths=2)
    
    ax4.scatter([0], [0], color='cyan', s=100, marker='o', label='Center')
    ax4.set_xlabel('x')
    ax4.set_ylabel('y')
    ax4.set_title('Energy Density ρ(x) in z=0 Plane')
    ax4.set_aspect('equal')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_spatial_variation.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_spatial_variation.png'}")


def plot_gradient_term():
    """
    Plot the gradient term |∇χ_total|² structure.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    a0 = PARAMS.a0
    epsilon = PARAMS.epsilon
    
    # Plot 1: |∇χ|² radial profiles
    ax1 = axes[0, 0]
    
    directions = {
        'x-axis': np.array([1, 0, 0]),
        'y-axis': np.array([0, 1, 0]),
        'diagonal': np.array([1, 1, 1]) / np.sqrt(3),
        'toward R': X_R
    }
    
    distances = np.linspace(0, 2.5, 100)
    
    for name, direction in directions.items():
        grad_sq_profile = []
        for d in distances:
            pos = d * direction
            grad_sq = gradient_energy_density(pos, a0, epsilon)
            grad_sq_profile.append(grad_sq)
        ax1.plot(distances, grad_sq_profile, label=name, linewidth=1.5)
    
    # Mark center value
    grad_center = gradient_energy_density(np.zeros(3), a0, epsilon)
    ax1.scatter([0], [grad_center], color='k', s=100, zorder=5,
                label=f'Center: {grad_center:.3f}')
    
    ax1.set_xlabel('Distance from center')
    ax1.set_ylabel('|∇χ_total|²')
    ax1.set_title('Gradient Energy Density |∇χ|²')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: 2D slice of |∇χ|²
    ax2 = axes[0, 1]
    
    x_range = np.linspace(-2, 2, 80)
    y_range = np.linspace(-2, 2, 80)
    X, Y = np.meshgrid(x_range, y_range)
    grad_sq_2d = np.zeros_like(X)
    
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            pos = np.array([X[i, j], Y[i, j], 0])
            grad_sq_2d[i, j] = gradient_energy_density(pos, a0, epsilon)
    
    contour = ax2.contourf(X, Y, grad_sq_2d, levels=30, cmap='viridis')
    plt.colorbar(contour, ax=ax2, label='|∇χ|²')
    
    for x_c, color in zip(VERTICES_RGB, ['r', 'g', 'b']):
        ax2.scatter([x_c[0]], [x_c[1]], color=color, s=80, marker='^',
                    edgecolors='white', linewidths=1.5)
    
    ax2.scatter([0], [0], color='cyan', s=100, marker='o')
    ax2.set_xlabel('x')
    ax2.set_ylabel('y')
    ax2.set_title('|∇χ|² in z=0 Plane')
    ax2.set_aspect('equal')
    
    # Plot 3: Gradient vector field
    ax3 = axes[1, 0]
    
    # Coarser grid for vector field
    x_vec = np.linspace(-1.5, 1.5, 15)
    y_vec = np.linspace(-1.5, 1.5, 15)
    X_vec, Y_vec = np.meshgrid(x_vec, y_vec)
    
    U = np.zeros_like(X_vec)
    V = np.zeros_like(Y_vec)
    
    for i in range(X_vec.shape[0]):
        for j in range(X_vec.shape[1]):
            pos = np.array([X_vec[i, j], Y_vec[i, j], 0])
            grad = gradient_chi_total(pos, a0, epsilon)
            # Use real part for visualization
            U[i, j] = np.real(grad[0])
            V[i, j] = np.real(grad[1])
    
    # Normalize for visualization
    mag = np.sqrt(U**2 + V**2)
    mag[mag == 0] = 1  # Avoid division by zero
    U_norm = U / mag
    V_norm = V / mag
    
    ax3.quiver(X_vec, Y_vec, U_norm, V_norm, mag, cmap='plasma', alpha=0.8)
    
    for x_c, color, name in zip(VERTICES_RGB, ['r', 'g', 'b'], ['R', 'G', 'B']):
        ax3.scatter([x_c[0]], [x_c[1]], color=color, s=100, marker='^',
                    edgecolors='black', linewidths=1)
    
    ax3.scatter([0], [0], color='cyan', s=100, marker='o', edgecolors='black')
    ax3.set_xlabel('x')
    ax3.set_ylabel('y')
    ax3.set_title('Re(∇χ) Vector Field (z=0 plane)')
    ax3.set_aspect('equal')
    ax3.set_xlim(-1.8, 1.8)
    ax3.set_ylim(-1.8, 1.8)
    
    # Plot 4: Comparison of coherent vs incoherent at center
    ax4 = axes[1, 1]
    
    r_values = np.linspace(0, 2, 100)
    chi_sq_values = []
    rho_values = []
    grad_values = []
    
    for r in r_values:
        pos = r * np.array([1, 1, 1]) / np.sqrt(3)
        chi = chi_total_at_position(pos, a0, epsilon)
        chi_sq_values.append(np.abs(chi)**2)
        rho_values.append(energy_density_incoherent(pos, a0, epsilon))
        grad_values.append(gradient_energy_density(pos, a0, epsilon))
    
    # Normalize for comparison
    rho_max = max(rho_values)
    chi_sq_max = max(chi_sq_values) if max(chi_sq_values) > 0 else 1
    grad_max = max(grad_values) if max(grad_values) > 0 else 1
    
    ax4.plot(r_values, np.array(rho_values)/rho_max, 'r-', linewidth=2,
             label='ρ (incoherent, normalized)')
    ax4.plot(r_values, np.array(chi_sq_values)/chi_sq_max, 'b-', linewidth=2,
             label='|χ|² (coherent, normalized)')
    ax4.plot(r_values, np.array(grad_values)/grad_max, 'g-', linewidth=2,
             label='|∇χ|² (normalized)')
    
    ax4.axvline(x=0, color='k', linestyle='--', alpha=0.5)
    ax4.set_xlabel('Distance along (1,1,1) direction')
    ax4.set_ylabel('Normalized value')
    ax4.set_title('Coherent vs Incoherent: Key Insight')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    # Add text annotation
    ax4.annotate('At center:\n|χ|² = 0 (coherent)\nρ > 0 (incoherent)',
                 xy=(0.1, 0.5), fontsize=10,
                 bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_gradient_term.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_gradient_term.png'}")


def plot_stability_analysis():
    """
    Plot stability analysis for λ > 0 requirement.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    v0 = PARAMS.v0
    
    # Plot 1: Energy vs amplitude for different λ
    ax1 = axes[0, 0]
    
    a_values = np.linspace(0, 5, 200)
    lambdas = [-0.5, 0, 0.5, 1.0]
    colors = ['red', 'orange', 'blue', 'green']
    
    for lam, color in zip(lambdas, colors):
        E_values = []
        for a in a_values:
            amps = np.array([a, a, a])
            E = energy_functional_level1(amps, lam, v0)
            E_values.append(E)
        ax1.plot(a_values, E_values, color=color, linewidth=2,
                 label=f'λ = {lam}')
    
    ax1.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    ax1.set_xlabel('Symmetric amplitude a')
    ax1.set_ylabel('Energy E')
    ax1.set_title('Energy vs. Amplitude for Different λ')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim(-10, 30)
    
    # Plot 2: Energy for asymmetric case (shows unbounded for λ < 0)
    ax2 = axes[0, 1]
    
    # Vary one amplitude while keeping others fixed
    a_R_values = np.linspace(0.1, 10, 200)
    
    for lam, color in zip(lambdas, colors):
        E_values = []
        for a_R in a_R_values:
            amps = np.array([a_R, 0.5, 0.5])
            E = energy_functional_level1(amps, lam, v0)
            E_values.append(E)
        ax2.plot(a_R_values, E_values, color=color, linewidth=2,
                 label=f'λ = {lam}')
    
    ax2.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    ax2.set_xlabel('a_R (with a_G = a_B = 0.5)')
    ax2.set_ylabel('Energy E')
    ax2.set_title('Energy with Asymmetric Amplitudes')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim(-50, 150)
    
    # Plot 3: Potential landscape for λ > 0
    ax3 = axes[1, 0]
    
    lam_pos = 1.0
    a_range = np.linspace(0.1, 2.5, 80)
    A_R, A_G = np.meshgrid(a_range, a_range)
    E_grid_pos = np.zeros_like(A_R)
    
    for i in range(A_R.shape[0]):
        for j in range(A_R.shape[1]):
            amps = np.array([A_R[i, j], A_G[i, j], 1.0])
            E_grid_pos[i, j] = energy_functional_level1(amps, lam_pos, v0)
    
    contour = ax3.contourf(A_R, A_G, E_grid_pos, levels=30, cmap='viridis')
    plt.colorbar(contour, ax=ax3, label='Energy')
    ax3.scatter([1.0], [1.0], color='red', s=100, marker='*')
    ax3.set_xlabel('a_R')
    ax3.set_ylabel('a_G')
    ax3.set_title(f'Energy Landscape (λ = {lam_pos} > 0, STABLE)')
    
    # Plot 4: Potential landscape for λ < 0
    ax4 = axes[1, 1]
    
    lam_neg = -0.3
    E_grid_neg = np.zeros_like(A_R)
    
    for i in range(A_R.shape[0]):
        for j in range(A_R.shape[1]):
            amps = np.array([A_R[i, j], A_G[i, j], 1.0])
            E_grid_neg[i, j] = energy_functional_level1(amps, lam_neg, v0)
    
    # Clip for visualization
    E_grid_clipped = np.clip(E_grid_neg, -20, 20)
    
    contour2 = ax4.contourf(A_R, A_G, E_grid_clipped, levels=30, cmap='RdBu')
    plt.colorbar(contour2, ax=ax4, label='Energy (clipped)')
    ax4.scatter([1.0], [1.0], color='cyan', s=100, marker='*')
    ax4.set_xlabel('a_R')
    ax4.set_ylabel('a_G')
    ax4.set_title(f'Energy Landscape (λ = {lam_neg} < 0, UNSTABLE)')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_stability.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_stability.png'}")


def plot_noether_comparison():
    """
    Plot comparison between pre-Lorentzian and Noether energy definitions.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    a0 = PARAMS.a0
    epsilon = PARAMS.epsilon
    v0 = PARAMS.v0
    lambda_chi = PARAMS.lambda_chi
    
    # Plot 1: Components of energy density at various positions
    ax1 = axes[0, 0]
    
    r_values = np.linspace(0, 2, 100)
    direction = np.array([1, 1, 1]) / np.sqrt(3)
    
    kinetic_vals = []  # Pre-Lorentzian "kinetic" = Σ|a_c|²
    gradient_vals = []  # Gradient term |∇χ|²
    potential_vals = []  # Potential V(χ)
    chi_sq_vals = []  # |χ|²
    
    for r in r_values:
        pos = r * direction
        
        # Pre-Lorentzian incoherent sum
        kinetic = sum(a0**2 * pressure_function(pos, x_c, epsilon)**2 
                      for x_c in VERTICES_RGB)
        kinetic_vals.append(kinetic)
        
        # Gradient
        grad_sq = gradient_energy_density(pos, a0, epsilon)
        gradient_vals.append(grad_sq)
        
        # Coherent field and potential
        chi = chi_total_at_position(pos, a0, epsilon)
        chi_sq = np.abs(chi)**2
        chi_sq_vals.append(chi_sq)
        potential_vals.append(lambda_chi * (chi_sq - v0**2)**2)
    
    ax1.plot(r_values, kinetic_vals, 'b-', linewidth=2, label='Σ|a_c|² (kinetic-like)')
    ax1.plot(r_values, gradient_vals, 'g-', linewidth=2, label='|∇χ|² (gradient)')
    ax1.plot(r_values, potential_vals, 'r-', linewidth=2, label='V(χ) (potential)')
    
    ax1.set_xlabel('Distance from center (along diagonal)')
    ax1.set_ylabel('Energy density component')
    ax1.set_title('Energy Density Components')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Pre-Lorentzian vs Noether T^00
    ax2 = axes[0, 1]
    
    # Pre-Lorentzian: ρ = Σ|a_c(x)|² + V
    rho_pre = np.array(kinetic_vals) + np.array(potential_vals)
    
    # Noether (post-emergence): T^00 = |∂_t χ|² + |∇χ|² + V
    # With ω=1: |∂_t χ|² ≈ |χ|²
    T00_noether = np.array(chi_sq_vals) + np.array(gradient_vals) + np.array(potential_vals)
    
    ax2.plot(r_values, rho_pre, 'b-', linewidth=2, label='ρ (pre-Lorentzian)')
    ax2.plot(r_values, T00_noether, 'r--', linewidth=2, label='T⁰⁰ (Noether)')
    
    ax2.set_xlabel('Distance from center')
    ax2.set_ylabel('Energy density')
    ax2.set_title('Pre-Lorentzian ρ vs. Noether T⁰⁰')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Circularity diagram (schematic)
    ax3 = axes[1, 0]
    ax3.axis('off')
    
    # Create text-based diagram
    diagram_text = """
    OLD APPROACH (CIRCULAR):
    ┌─────────────────────────────────────────────┐
    │  Energy ← Noether ← Spacetime ← Metric      │
    │                      ↑            ↓          │
    │                      └── T_μν ←──┘          │
    │              (Stress-energy needs metric)    │
    └─────────────────────────────────────────────┘
    
    NEW APPROACH (NON-CIRCULAR):
    ┌─────────────────────────────────────────────┐
    │  E = Σ|a_c|² + V(χ)  [Algebraic, no Noether]│
    │           ↓                                  │
    │  Time emerges (Theorem 0.2.2)               │
    │           ↓                                  │
    │  Lorentzian spacetime emerges               │
    │           ↓                                  │
    │  Noether becomes CONSISTENCY CHECK          │
    └─────────────────────────────────────────────┘
    """
    ax3.text(0.5, 0.5, diagram_text, transform=ax3.transAxes,
             fontsize=10, fontfamily='monospace',
             verticalalignment='center', horizontalalignment='center',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))
    ax3.set_title('Resolution of Noether Circularity', fontsize=14)
    
    # Plot 4: Phase 0 → Emergence timeline
    ax4 = axes[1, 1]
    ax4.axis('off')
    
    timeline_text = """
    PHASE 0: Pre-Lorentzian
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    ✓ Euclidean ℝ³ (from SU(3), Phase -1)
    ✓ Stella octangula topology
    ✓ Three color fields with 120° phases
    ✓ Energy E = Σ|a_c|² + V(χ_total)
    ✗ No Lorentzian spacetime
    ✗ No time coordinate t
    ✗ No Noether theorem available
    
                         ↓
    EMERGENCE (Theorem 0.2.2)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    Internal parameter λ → Physical time t = λ/ω
    
                         ↓
    POST-EMERGENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    ✓ Lorentzian (3+1)D spacetime exists
    ✓ Time coordinate t available
    ✓ Noether theorem can be applied
    ✓ T⁰⁰_Noether = ρ_Phase0 (consistency check)
    """
    ax4.text(0.5, 0.5, timeline_text, transform=ax4.transAxes,
             fontsize=9, fontfamily='monospace',
             verticalalignment='center', horizontalalignment='center',
             bbox=dict(boxstyle='round', facecolor='lightcyan', alpha=0.8))
    ax4.set_title('Emergence Timeline', fontsize=14)
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_noether_comparison.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_noether_comparison.png'}")


def plot_stella_octangula_3d():
    """
    Plot the stella octangula (two interlocked tetrahedra) with field visualization.
    """
    fig = plt.figure(figsize=(14, 6))
    
    # Plot 1: Stella octangula geometry
    ax1 = fig.add_subplot(121, projection='3d')
    
    # Tetrahedron 1 vertices (RGB + Y)
    tet1 = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ]) / np.sqrt(3)
    
    # Tetrahedron 2 vertices (anti-tetrahedron)
    tet2 = -tet1
    
    # Draw tetrahedra edges
    def draw_tetrahedron(ax, verts, color, alpha=0.3):
        # Faces
        faces = [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]]
        ]
        for face in faces:
            tri = np.array(face + [face[0]])
            ax.plot(tri[:, 0], tri[:, 1], tri[:, 2], color=color, linewidth=1.5)
    
    draw_tetrahedron(ax1, tet1, 'blue', 0.3)
    draw_tetrahedron(ax1, tet2, 'red', 0.3)
    
    # Mark RGB vertices
    colors_rgb = ['red', 'green', 'blue']
    labels = ['R', 'G', 'B']
    for v, c, l in zip(VERTICES_RGB, colors_rgb, labels):
        ax1.scatter([v[0]], [v[1]], [v[2]], color=c, s=200, edgecolors='black')
        ax1.text(v[0]*1.2, v[1]*1.2, v[2]*1.2, l, fontsize=12, fontweight='bold')
    
    # Mark center
    ax1.scatter([0], [0], [0], color='black', s=100, marker='o')
    ax1.text(0.1, 0.1, 0.1, 'O', fontsize=12)
    
    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_zlabel('z')
    ax1.set_title('Stella Octangula\n(Two Interlocked Tetrahedra)')
    
    # Plot 2: Energy density isosurface (simplified 2D projection)
    ax2 = fig.add_subplot(122)
    
    x = np.linspace(-1.5, 1.5, 100)
    y = np.linspace(-1.5, 1.5, 100)
    X, Y = np.meshgrid(x, y)
    
    # Compute energy density in z=0 plane
    rho = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            pos = np.array([X[i, j], Y[i, j], 0])
            rho[i, j] = energy_density_incoherent(pos, PARAMS.a0, PARAMS.epsilon)
    
    contour = ax2.contourf(X, Y, np.log10(rho + 1e-10), levels=30, cmap='inferno')
    plt.colorbar(contour, ax=ax2, label='log₁₀(ρ)')
    
    # Mark vertices
    for v, c in zip(VERTICES_RGB, colors_rgb):
        ax2.scatter([v[0]], [v[1]], color=c, s=150, edgecolors='white', 
                    linewidths=2, marker='^')
    
    ax2.scatter([0], [0], color='cyan', s=100, marker='o', edgecolors='black')
    ax2.set_xlabel('x')
    ax2.set_ylabel('y')
    ax2.set_title('Energy Density in z=0 Plane')
    ax2.set_aspect('equal')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_2_4_stella_octangula.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_2_4_stella_octangula.png'}")


def generate_all_plots():
    """Generate all visualization plots."""
    set_plot_style()
    
    print("=" * 70)
    print("GENERATING THEOREM 0.2.4 VISUALIZATIONS")
    print("=" * 70)
    
    print("\n1. Phase cancellation...")
    plot_phase_cancellation()
    
    print("\n2. Mexican hat potential...")
    plot_mexican_hat_potential()
    
    print("\n3. Energy landscape...")
    plot_energy_landscape()
    
    print("\n4. Spatial variation...")
    plot_spatial_variation()
    
    print("\n5. Gradient term...")
    plot_gradient_term()
    
    print("\n6. Stability analysis...")
    plot_stability_analysis()
    
    print("\n7. Noether comparison...")
    plot_noether_comparison()
    
    print("\n8. Stella octangula 3D...")
    plot_stella_octangula_3d()
    
    print("\n" + "=" * 70)
    print(f"All plots saved to: {PLOT_DIR}")
    print("=" * 70)


if __name__ == '__main__':
    generate_all_plots()
