#!/usr/bin/env python3
"""
Visualizations for Theorem 0.2.1: Total Field from Superposition

This script generates visualization plots for:
1. Total chiral field χ_total in cross-sections
2. Energy density ρ(x) distribution
3. Comparison of coherent |χ_total|² vs incoherent ρ
4. Gradient field visualization
5. Energy integral convergence
6. Summary visualization

Note: The "stella octangula" refers to two interlocked tetrahedra forming an 8-vertex
structure with 6 color vertices and 2 singlet vertices.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os
from typing import Dict, List, Tuple, Optional
from matplotlib import cm
from matplotlib.colors import LinearSegmentedColormap, Normalize
from scipy.integrate import quad

# Set up plotting style
plt.style.use('seaborn-v0_8-whitegrid')
plt.rcParams['figure.figsize'] = (12, 10)
plt.rcParams['font.size'] = 12
plt.rcParams['axes.labelsize'] = 14
plt.rcParams['axes.titlesize'] = 16

# =============================================================================
# CONSTANTS
# =============================================================================

# Regularization parameter
EPSILON = 0.05

# Normalization constant
A0 = 1.0

# Color phases
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Phase exponentials
EXP_PHASES = {
    'R': np.exp(1j * PHASES['R']),
    'G': np.exp(1j * PHASES['G']),
    'B': np.exp(1j * PHASES['B']),
}

# Color RGB values for plotting
COLORS = {
    'R': '#FF0000',
    'G': '#00AA00',
    'B': '#0000FF',
    'W': '#808080',
}

# Stella octangula vertices - Tetrahedron T+ (quark colors R, G, B + singlet W)
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Tetrahedron T- (anti-quark colors)
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}

# Output directory
PLOTS_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'plots')


# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def pressure_function(x: np.ndarray, x_c: np.ndarray, epsilon: float = EPSILON) -> float:
    """Compute pressure function P_c(x) = 1 / (|x - x_c|² + ε²)"""
    dist_squared = np.sum((x - x_c)**2)
    return 1.0 / (dist_squared + epsilon**2)


def pressure_function_grid(X: np.ndarray, Y: np.ndarray, Z: np.ndarray, 
                           x_c: np.ndarray, epsilon: float = EPSILON) -> np.ndarray:
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field(x: np.ndarray, a0: float = A0, epsilon: float = EPSILON) -> complex:
    """Compute total chiral field χ_total(x) = Σ_c a_c(x) e^(iφ_c)"""
    total = 0.0 + 0.0j
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def total_chiral_field_grid(X: np.ndarray, Y: np.ndarray, Z: np.ndarray,
                            a0: float = A0, epsilon: float = EPSILON) -> np.ndarray:
    """Vectorized total chiral field for grids."""
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def energy_density(x: np.ndarray, a0: float = A0, epsilon: float = EPSILON) -> float:
    """Compute energy density ρ(x) = a_0² Σ_c P_c(x)²"""
    total = 0.0
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
        total += P_c**2
    return a0**2 * total


def energy_density_grid(X: np.ndarray, Y: np.ndarray, Z: np.ndarray,
                        a0: float = A0, epsilon: float = EPSILON) -> np.ndarray:
    """Vectorized energy density for grids."""
    total = np.zeros_like(X)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += P_c**2
    return a0**2 * total


def field_gradient(x: np.ndarray, a0: float = A0, epsilon: float = EPSILON) -> np.ndarray:
    """Compute gradient ∇χ_total at point x."""
    gradient = np.zeros(3, dtype=complex)
    for c in ['R', 'G', 'B']:
        x_c = VERTICES_PLUS[c]
        diff = x - x_c
        dist_sq = np.sum(diff**2)
        grad_P = -2 * diff / (dist_sq + epsilon**2)**2
        gradient += a0 * EXP_PHASES[c] * grad_P
    return gradient


# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def plot_total_field_cross_sections():
    """
    Plot the total chiral field χ_total in different cross-sections.
    Shows real part, imaginary part, and magnitude.
    """
    fig, axes = plt.subplots(3, 3, figsize=(15, 15))
    fig.suptitle('Total Chiral Field χ_total Cross-Sections\n(Theorem 0.2.1, Section 2)', fontsize=16)
    
    # Grid setup
    n_points = 100
    extent = 0.8
    x = np.linspace(-extent, extent, n_points)
    y = np.linspace(-extent, extent, n_points)
    
    planes = [
        ('z = 0 plane', 0.0, 2),
        ('y = 0 plane', 0.0, 1),
        ('x = 0 plane', 0.0, 0),
    ]
    
    for col, (plane_name, plane_val, plane_axis) in enumerate(planes):
        X, Y = np.meshgrid(x, y)
        
        # Create Z based on plane
        if plane_axis == 2:  # z = const
            Z = np.full_like(X, plane_val)
            xlabel, ylabel = 'x', 'y'
        elif plane_axis == 1:  # y = const
            Z = Y.copy()
            Y_grid = np.full_like(X, plane_val)
            Z = Y.copy()
            Y = Y_grid
            xlabel, ylabel = 'x', 'z'
        else:  # x = const
            Z = Y.copy()
            X_grid = np.full_like(X, plane_val)
            Y_plot = X.copy()
            X = X_grid
            Y = Y_plot
            xlabel, ylabel = 'y', 'z'
        
        # Compute field
        chi = total_chiral_field_grid(X, Y, Z, A0, EPSILON)
        
        # Plot real part
        im0 = axes[0, col].pcolormesh(x, y, chi.real, cmap='RdBu_r', shading='auto')
        axes[0, col].set_title(f'Re[χ_total], {plane_name}')
        axes[0, col].set_xlabel(xlabel)
        axes[0, col].set_ylabel(ylabel)
        axes[0, col].set_aspect('equal')
        plt.colorbar(im0, ax=axes[0, col])
        
        # Plot imaginary part
        im1 = axes[1, col].pcolormesh(x, y, chi.imag, cmap='RdBu_r', shading='auto')
        axes[1, col].set_title(f'Im[χ_total], {plane_name}')
        axes[1, col].set_xlabel(xlabel)
        axes[1, col].set_ylabel(ylabel)
        axes[1, col].set_aspect('equal')
        plt.colorbar(im1, ax=axes[1, col])
        
        # Plot magnitude
        im2 = axes[2, col].pcolormesh(x, y, np.abs(chi), cmap='viridis', shading='auto')
        axes[2, col].set_title(f'|χ_total|, {plane_name}')
        axes[2, col].set_xlabel(xlabel)
        axes[2, col].set_ylabel(ylabel)
        axes[2, col].set_aspect('equal')
        plt.colorbar(im2, ax=axes[2, col])
        
        # Mark the center
        for ax in [axes[0, col], axes[1, col], axes[2, col]]:
            ax.plot(0, 0, 'ko', markersize=8, markerfacecolor='none', markeredgewidth=2)
    
    plt.tight_layout()
    return fig


def plot_energy_density_distribution():
    """
    Plot the energy density ρ(x) = a_0² Σ_c P_c(x)²
    Shows that ρ(0) ≠ 0 even though χ_total(0) = 0.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.suptitle('Energy Density ρ(x) = a₀² Σ_c P_c(x)²\n(Theorem 0.2.1, Section 3)', fontsize=16)
    
    # Grid setup
    n_points = 100
    extent = 0.8
    x = np.linspace(-extent, extent, n_points)
    y = np.linspace(-extent, extent, n_points)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    # Compute energy density
    rho = energy_density_grid(X, Y, Z, A0, EPSILON)
    
    # Plot energy density in z=0 plane
    im0 = axes[0, 0].pcolormesh(x, y, rho, cmap='hot', shading='auto')
    axes[0, 0].set_title('Energy Density ρ(x), z=0 plane')
    axes[0, 0].set_xlabel('x')
    axes[0, 0].set_ylabel('y')
    axes[0, 0].set_aspect('equal')
    plt.colorbar(im0, ax=axes[0, 0], label='ρ(x)')
    axes[0, 0].plot(0, 0, 'w+', markersize=15, markeredgewidth=2)
    
    # Mark vertices (projected)
    for c, color in [('R', 'red'), ('G', 'green'), ('B', 'blue')]:
        v = VERTICES_PLUS[c]
        axes[0, 0].plot(v[0], v[1], 'o', color=color, markersize=10, markeredgecolor='white')
    
    # Plot log energy density
    log_rho = np.log10(rho + 1e-10)
    im1 = axes[0, 1].pcolormesh(x, y, log_rho, cmap='hot', shading='auto')
    axes[0, 1].set_title('log₁₀(ρ), z=0 plane')
    axes[0, 1].set_xlabel('x')
    axes[0, 1].set_ylabel('y')
    axes[0, 1].set_aspect('equal')
    plt.colorbar(im1, ax=axes[0, 1], label='log₁₀(ρ)')
    axes[0, 1].plot(0, 0, 'w+', markersize=15, markeredgewidth=2)
    
    # 1D profile along diagonal
    t = np.linspace(-1, 1, 200)
    diagonal = t / np.sqrt(3) * np.array([1, 1, 1]).reshape(3, 1)  # toward R vertex
    
    rho_diag = []
    chi_sq_diag = []
    for i in range(len(t)):
        pt = diagonal[:, i]
        rho_diag.append(energy_density(pt, A0, EPSILON))
        chi = total_chiral_field(pt, A0, EPSILON)
        chi_sq_diag.append(np.abs(chi)**2)
    
    axes[1, 0].semilogy(t, rho_diag, 'b-', linewidth=2, label='ρ(x) = Σ|a_c|² (energy)')
    axes[1, 0].semilogy(t, chi_sq_diag, 'r--', linewidth=2, label='|χ_total|² (coherent)')
    axes[1, 0].axvline(0, color='gray', linestyle=':', alpha=0.5)
    axes[1, 0].axvline(1, color='red', linestyle=':', alpha=0.5, label='R vertex')
    axes[1, 0].set_xlabel('t (along diagonal toward R)')
    axes[1, 0].set_ylabel('Field/Energy value')
    axes[1, 0].set_title('ρ vs |χ_total|² along diagonal')
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    # Show center values
    origin = np.array([0.0, 0.0, 0.0])
    rho_center = energy_density(origin, A0, EPSILON)
    chi_center = total_chiral_field(origin, A0, EPSILON)
    
    text_str = (
        f"At Center (x = 0):\n"
        f"  ρ(0) = {rho_center:.4f} ≠ 0\n"
        f"  |χ_total(0)|² = {np.abs(chi_center)**2:.2e} ≈ 0\n"
        f"\nKey: Energy is non-zero\n"
        f"even where field cancels!"
    )
    axes[1, 1].text(0.1, 0.5, text_str, fontsize=14, transform=axes[1, 1].transAxes,
                    verticalalignment='center', fontfamily='monospace',
                    bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    axes[1, 1].set_xlim(0, 1)
    axes[1, 1].set_ylim(0, 1)
    axes[1, 1].axis('off')
    axes[1, 1].set_title('Critical Result: ρ(0) ≠ 0')
    
    plt.tight_layout()
    return fig


def plot_coherent_vs_incoherent():
    """
    Compare coherent |χ_total|² vs incoherent ρ = Σ|a_c|².
    The difference highlights the interference effects.
    """
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Coherent vs Incoherent: |χ_total|² vs ρ = Σ|a_c|²\n(Theorem 0.2.1, Section 3.0)', fontsize=16)
    
    # Grid setup
    n_points = 100
    extent = 0.8
    x = np.linspace(-extent, extent, n_points)
    y = np.linspace(-extent, extent, n_points)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    # Compute fields
    chi = total_chiral_field_grid(X, Y, Z, A0, EPSILON)
    chi_sq = np.abs(chi)**2  # Coherent
    rho = energy_density_grid(X, Y, Z, A0, EPSILON)  # Incoherent
    
    # Interference term
    interference = rho - chi_sq
    
    # Plot coherent |χ_total|²
    im0 = axes[0, 0].pcolormesh(x, y, chi_sq, cmap='viridis', shading='auto')
    axes[0, 0].set_title('|χ_total|² (Coherent)')
    axes[0, 0].set_xlabel('x')
    axes[0, 0].set_ylabel('y')
    axes[0, 0].set_aspect('equal')
    plt.colorbar(im0, ax=axes[0, 0])
    axes[0, 0].plot(0, 0, 'w+', markersize=12, markeredgewidth=2)
    
    # Plot incoherent ρ
    im1 = axes[0, 1].pcolormesh(x, y, rho, cmap='viridis', shading='auto')
    axes[0, 1].set_title('ρ = Σ|a_c|² (Incoherent)')
    axes[0, 1].set_xlabel('x')
    axes[0, 1].set_ylabel('y')
    axes[0, 1].set_aspect('equal')
    plt.colorbar(im1, ax=axes[0, 1])
    axes[0, 1].plot(0, 0, 'w+', markersize=12, markeredgewidth=2)
    
    # Plot interference = ρ - |χ_total|²
    im2 = axes[0, 2].pcolormesh(x, y, interference, cmap='RdBu_r', shading='auto')
    axes[0, 2].set_title('Interference = ρ - |χ_total|²')
    axes[0, 2].set_xlabel('x')
    axes[0, 2].set_ylabel('y')
    axes[0, 2].set_aspect('equal')
    plt.colorbar(im2, ax=axes[0, 2])
    axes[0, 2].plot(0, 0, 'k+', markersize=12, markeredgewidth=2)
    
    # 1D profiles
    y_idx = n_points // 2  # y=0 slice
    
    axes[1, 0].plot(x, chi_sq[y_idx, :], 'b-', linewidth=2, label='|χ_total|²')
    axes[1, 0].plot(x, rho[y_idx, :], 'r--', linewidth=2, label='ρ')
    axes[1, 0].axvline(0, color='gray', linestyle=':', alpha=0.5)
    axes[1, 0].set_xlabel('x (y=0, z=0)')
    axes[1, 0].set_ylabel('Value')
    axes[1, 0].set_title('Profile along x-axis')
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    # Log scale profile
    axes[1, 1].semilogy(x, chi_sq[y_idx, :] + 1e-10, 'b-', linewidth=2, label='|χ_total|²')
    axes[1, 1].semilogy(x, rho[y_idx, :], 'r--', linewidth=2, label='ρ')
    axes[1, 1].axvline(0, color='gray', linestyle=':', alpha=0.5)
    axes[1, 1].set_xlabel('x (y=0, z=0)')
    axes[1, 1].set_ylabel('Value (log scale)')
    axes[1, 1].set_title('Profile (log scale)')
    axes[1, 1].legend()
    axes[1, 1].grid(True, alpha=0.3)
    
    # Ratio at different points
    ratios = []
    positions = []
    for xi in np.linspace(-0.6, 0.6, 25):
        pt = np.array([xi, 0, 0])
        chi_val = total_chiral_field(pt, A0, EPSILON)
        chi_sq_val = np.abs(chi_val)**2
        rho_val = energy_density(pt, A0, EPSILON)
        if chi_sq_val > 1e-10:
            ratios.append(rho_val / chi_sq_val)
        else:
            ratios.append(np.inf)
        positions.append(xi)
    
    axes[1, 2].plot(positions, ratios, 'g-', linewidth=2)
    axes[1, 2].set_xlabel('x (y=0, z=0)')
    axes[1, 2].set_ylabel('ρ / |χ_total|²')
    axes[1, 2].set_title('Ratio ρ/|χ_total|²')
    axes[1, 2].set_ylim(0, 5)
    axes[1, 2].axhline(1, color='gray', linestyle=':', alpha=0.5)
    axes[1, 2].grid(True, alpha=0.3)
    
    plt.tight_layout()
    return fig


def plot_gradient_field():
    """
    Plot the gradient of the total field ∇χ_total.
    Shows that ∇χ_total|₀ ≠ 0 even though χ_total(0) = 0.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.suptitle('Gradient Field ∇χ_total\n(Theorem 0.2.1, Section 5)', fontsize=16)
    
    # Grid for gradient evaluation
    n_points = 15
    extent = 0.5
    x = np.linspace(-extent, extent, n_points)
    y = np.linspace(-extent, extent, n_points)
    X, Y = np.meshgrid(x, y)
    
    # Compute gradients in z=0 plane
    grad_real_x = np.zeros_like(X)
    grad_real_y = np.zeros_like(Y)
    grad_imag_x = np.zeros_like(X)
    grad_imag_y = np.zeros_like(Y)
    grad_mag = np.zeros_like(X)
    
    for i in range(n_points):
        for j in range(n_points):
            pt = np.array([X[i, j], Y[i, j], 0.0])
            grad = field_gradient(pt, A0, EPSILON)
            grad_real_x[i, j] = grad[0].real
            grad_real_y[i, j] = grad[1].real
            grad_imag_x[i, j] = grad[0].imag
            grad_imag_y[i, j] = grad[1].imag
            grad_mag[i, j] = np.sqrt(np.sum(np.abs(grad)**2))
    
    # Background: energy density
    n_bg = 100
    x_bg = np.linspace(-extent, extent, n_bg)
    y_bg = np.linspace(-extent, extent, n_bg)
    X_bg, Y_bg = np.meshgrid(x_bg, y_bg)
    Z_bg = np.zeros_like(X_bg)
    rho = energy_density_grid(X_bg, Y_bg, Z_bg, A0, EPSILON)
    
    # Plot real part of gradient
    axes[0, 0].pcolormesh(x_bg, y_bg, rho, cmap='gray_r', shading='auto', alpha=0.3)
    axes[0, 0].quiver(X, Y, grad_real_x, grad_real_y, color='blue', scale=5000)
    axes[0, 0].set_title('Re[∇χ_total], z=0 plane')
    axes[0, 0].set_xlabel('x')
    axes[0, 0].set_ylabel('y')
    axes[0, 0].set_aspect('equal')
    axes[0, 0].plot(0, 0, 'ro', markersize=10)
    
    # Plot imaginary part of gradient
    axes[0, 1].pcolormesh(x_bg, y_bg, rho, cmap='gray_r', shading='auto', alpha=0.3)
    axes[0, 1].quiver(X, Y, grad_imag_x, grad_imag_y, color='red', scale=5000)
    axes[0, 1].set_title('Im[∇χ_total], z=0 plane')
    axes[0, 1].set_xlabel('x')
    axes[0, 1].set_ylabel('y')
    axes[0, 1].set_aspect('equal')
    axes[0, 1].plot(0, 0, 'ro', markersize=10)
    
    # Plot gradient magnitude
    im2 = axes[1, 0].pcolormesh(x_bg, y_bg, np.sqrt(
        np.interp(X_bg.flatten(), x, grad_mag[n_points//2, :]).reshape(X_bg.shape)**2 +
        np.interp(Y_bg.flatten(), y, grad_mag[:, n_points//2]).reshape(Y_bg.shape)**2
    )/2, cmap='hot', shading='auto')
    # Actually compute properly
    grad_mag_bg = np.zeros_like(X_bg)
    for i in range(n_bg):
        for j in range(n_bg):
            pt = np.array([X_bg[i, j], Y_bg[i, j], 0.0])
            grad = field_gradient(pt, A0, EPSILON)
            grad_mag_bg[i, j] = np.sqrt(np.sum(np.abs(grad)**2))
    
    axes[1, 0].clear()
    im2 = axes[1, 0].pcolormesh(x_bg, y_bg, grad_mag_bg, cmap='hot', shading='auto')
    axes[1, 0].set_title('|∇χ_total|, z=0 plane')
    axes[1, 0].set_xlabel('x')
    axes[1, 0].set_ylabel('y')
    axes[1, 0].set_aspect('equal')
    plt.colorbar(im2, ax=axes[1, 0])
    axes[1, 0].plot(0, 0, 'w+', markersize=15, markeredgewidth=2)
    
    # Gradient at center analysis
    origin = np.array([0.0, 0.0, 0.0])
    grad_center = field_gradient(origin, A0, EPSILON)
    chi_center = total_chiral_field(origin, A0, EPSILON)
    
    text_str = (
        f"At Center (x = 0):\n"
        f"  χ_total(0) = {chi_center:.2e}\n"
        f"  |∇χ_total|₀:\n"
        f"    x: {grad_center[0]:.4f}\n"
        f"    y: {grad_center[1]:.4f}\n"
        f"    z: {grad_center[2]:.4f}\n"
        f"  |∇χ_total|₀| = {np.sqrt(np.sum(np.abs(grad_center)**2)):.4f}\n"
        f"\nKey: Gradient is non-zero\n"
        f"even where field vanishes!\n"
        f"→ Enables phase-gradient\n"
        f"   mass generation (Thm 3.1.1)"
    )
    axes[1, 1].text(0.1, 0.5, text_str, fontsize=12, transform=axes[1, 1].transAxes,
                    verticalalignment='center', fontfamily='monospace',
                    bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))
    axes[1, 1].axis('off')
    axes[1, 1].set_title('Gradient at Center')
    
    plt.tight_layout()
    return fig


def plot_energy_integral_convergence():
    """
    Plot the convergence of the total energy integral.
    E_total = ∫ d³x ρ(x) < ∞
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Energy Integral Convergence\n(Theorem 0.2.1, Section 8)', fontsize=16)
    
    # Integrand for single source: 4πr² / (r² + ε²)²
    def integrand(r, eps):
        return 4 * np.pi * r**2 / (r**2 + eps**2)**2
    
    # Plot integrand for different epsilon
    r = np.linspace(0, 2, 200)
    
    for eps in [0.02, 0.05, 0.1, 0.2]:
        I = integrand(r, eps)
        axes[0, 0].plot(r, I, label=f'ε = {eps}')
    
    axes[0, 0].set_xlabel('r')
    axes[0, 0].set_ylabel('4πr² / (r² + ε²)²')
    axes[0, 0].set_title('Integrand for Single Source')
    axes[0, 0].legend()
    axes[0, 0].grid(True, alpha=0.3)
    
    # Cumulative integral
    R_vals = np.linspace(0.01, 10, 100)
    
    for eps in [0.02, 0.05, 0.1, 0.2]:
        cumulative = []
        for R in R_vals:
            val, _ = quad(integrand, 0, R, args=(eps,))
            cumulative.append(val)
        
        # Expected limit: π²/ε
        limit = np.pi**2 / eps
        
        axes[0, 1].plot(R_vals, cumulative, label=f'ε = {eps}, limit = {limit:.2f}')
        axes[0, 1].axhline(limit, linestyle=':', alpha=0.3)
    
    axes[0, 1].set_xlabel('R (integration limit)')
    axes[0, 1].set_ylabel('∫₀^R 4πr²/(r²+ε²)² dr')
    axes[0, 1].set_title('Cumulative Integral vs R')
    axes[0, 1].legend()
    axes[0, 1].grid(True, alpha=0.3)
    
    # Scaling with epsilon
    eps_vals = np.linspace(0.02, 0.5, 50)
    E_vals = []
    
    for eps in eps_vals:
        val, _ = quad(integrand, 0, 50, args=(eps,))
        E_vals.append(val)
    
    axes[1, 0].loglog(eps_vals, E_vals, 'b-', linewidth=2, label='Numerical')
    axes[1, 0].loglog(eps_vals, np.pi**2 / eps_vals, 'r--', linewidth=2, label='π²/ε')
    axes[1, 0].set_xlabel('ε (regularization)')
    axes[1, 0].set_ylabel('Total energy (single source)')
    axes[1, 0].set_title('Energy Scaling: E ∝ 1/ε')
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    # Summary
    text_str = (
        f"Energy Integral Convergence:\n"
        f"─────────────────────────────\n"
        f"Single source integral:\n"
        f"  ∫ d³x P_c(x)² = ∫ 4πr² dr / (r² + ε²)²\n"
        f"\n"
        f"As R → ∞:\n"
        f"  → π²/ε (finite!)\n"
        f"\n"
        f"Physical interpretation:\n"
        f"• Smaller ε → sharper peaks\n"
        f"• Sharper peaks → more energy\n"
        f"• E_total ~ a₀²/ε\n"
        f"\n"
        f"Regularization ε sets the\n"
        f"'resolution' of the geometry."
    )
    axes[1, 1].text(0.1, 0.5, text_str, fontsize=12, transform=axes[1, 1].transAxes,
                    verticalalignment='center', fontfamily='monospace',
                    bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))
    axes[1, 1].axis('off')
    axes[1, 1].set_title('Section 8.3: Scaling with ε')
    
    plt.tight_layout()
    return fig


def plot_summary():
    """
    Create a summary visualization of Theorem 0.2.1.
    """
    fig = plt.figure(figsize=(16, 12))
    
    # Layout: 3x3 grid
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)
    
    # Title
    fig.suptitle('Theorem 0.2.1: Total Field from Superposition - Summary', fontsize=18, fontweight='bold')
    
    # 1. Cube roots of unity
    ax1 = fig.add_subplot(gs[0, 0])
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k-', alpha=0.3)
    
    for c, color in [('R', 'red'), ('G', 'green'), ('B', 'blue')]:
        phase = PHASES[c]
        ax1.plot([0, np.cos(phase)], [0, np.sin(phase)], '-', color=color, linewidth=3)
        ax1.plot(np.cos(phase), np.sin(phase), 'o', color=color, markersize=12)
    
    ax1.plot(0, 0, 'ko', markersize=8)
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.set_title('Phase Structure\n$1 + ω + ω² = 0$')
    ax1.grid(True, alpha=0.3)
    
    # 2. Total field vanishes at center
    ax2 = fig.add_subplot(gs[0, 1])
    t = np.linspace(-1, 1, 100)
    
    chi_vals = []
    for ti in t:
        pt = np.array([ti * 0.5, 0, 0])
        chi = total_chiral_field(pt, A0, EPSILON)
        chi_vals.append(np.abs(chi))
    
    ax2.plot(t, chi_vals, 'b-', linewidth=2)
    ax2.axvline(0, color='red', linestyle=':', alpha=0.5)
    ax2.set_xlabel('x')
    ax2.set_ylabel('|χ_total|')
    ax2.set_title('Field Vanishes at Center\n$χ_{total}(0) = 0$')
    ax2.grid(True, alpha=0.3)
    
    # 3. Energy non-zero at center
    ax3 = fig.add_subplot(gs[0, 2])
    
    rho_vals = []
    for ti in t:
        pt = np.array([ti * 0.5, 0, 0])
        rho_vals.append(energy_density(pt, A0, EPSILON))
    
    ax3.plot(t, rho_vals, 'r-', linewidth=2)
    ax3.axvline(0, color='blue', linestyle=':', alpha=0.5)
    ax3.axhline(energy_density(np.array([0,0,0]), A0, EPSILON), color='green', linestyle='--', alpha=0.5)
    ax3.set_xlabel('x')
    ax3.set_ylabel('ρ(x)')
    ax3.set_title('Energy Non-Zero!\n$ρ(0) ≠ 0$')
    ax3.grid(True, alpha=0.3)
    
    # 4. Energy density heatmap
    ax4 = fig.add_subplot(gs[1, 0])
    n = 80
    x = np.linspace(-0.7, 0.7, n)
    y = np.linspace(-0.7, 0.7, n)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    rho = energy_density_grid(X, Y, Z, A0, EPSILON)
    
    im = ax4.pcolormesh(x, y, rho, cmap='hot', shading='auto')
    ax4.set_xlabel('x')
    ax4.set_ylabel('y')
    ax4.set_title('Energy Density ρ(x)')
    ax4.set_aspect('equal')
    plt.colorbar(im, ax=ax4)
    ax4.plot(0, 0, 'w+', markersize=10, markeredgewidth=2)
    
    # 5. |χ_total|² heatmap
    ax5 = fig.add_subplot(gs[1, 1])
    chi = total_chiral_field_grid(X, Y, Z, A0, EPSILON)
    chi_sq = np.abs(chi)**2
    
    im = ax5.pcolormesh(x, y, chi_sq, cmap='viridis', shading='auto')
    ax5.set_xlabel('x')
    ax5.set_ylabel('y')
    ax5.set_title('Coherent |χ_total|²')
    ax5.set_aspect('equal')
    plt.colorbar(im, ax=ax5)
    ax5.plot(0, 0, 'w+', markersize=10, markeredgewidth=2)
    
    # 6. Gradient magnitude
    ax6 = fig.add_subplot(gs[1, 2])
    grad_mag = np.zeros_like(X)
    for i in range(n):
        for j in range(n):
            pt = np.array([X[i,j], Y[i,j], 0])
            grad = field_gradient(pt, A0, EPSILON)
            grad_mag[i,j] = np.sqrt(np.sum(np.abs(grad)**2))
    
    im = ax6.pcolormesh(x, y, grad_mag, cmap='plasma', shading='auto')
    ax6.set_xlabel('x')
    ax6.set_ylabel('y')
    ax6.set_title('Gradient |∇χ_total|')
    ax6.set_aspect('equal')
    plt.colorbar(im, ax=ax6)
    ax6.plot(0, 0, 'w+', markersize=10, markeredgewidth=2)
    
    # 7-9. Summary text
    ax_text = fig.add_subplot(gs[2, :])
    ax_text.axis('off')
    
    summary_text = (
        "KEY RESULTS OF THEOREM 0.2.1:\n"
        "═══════════════════════════════════════════════════════════════════════════════════════════════════════\n\n"
        "1. SUPERPOSITION FORMULA:     χ_total(x) = Σ_c a_c(x) e^(iφ_c)     where φ_R=0, φ_G=2π/3, φ_B=4π/3\n\n"
        "2. ENERGY DENSITY:            ρ(x) = a₀² Σ_c P_c(x)² > 0          (incoherent sum, positive definite)\n\n"
        "3. CENTER IS A NODE:          χ_total(0) = 0                       BUT ρ(0) ≠ 0 (energy redistributed)\n\n"
        "4. NON-ZERO GRADIENT:         ∇χ_total|₀ ≠ 0                       (enables phase-gradient mass generation)\n\n"
        "5. FINITE TOTAL ENERGY:       E_total = ∫ ρ(x) d³x ~ a₀²/ε < ∞   (converges due to regularization)\n\n"
        "6. NO EXTERNAL TIME:          All quantities defined pre-geometrically (no background metric needed)"
    )
    
    ax_text.text(0.5, 0.5, summary_text, fontsize=11, transform=ax_text.transAxes,
                 verticalalignment='center', horizontalalignment='center',
                 fontfamily='monospace',
                 bbox=dict(boxstyle='round', facecolor='lightgray', alpha=0.3))
    
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    return fig


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def generate_all_plots():
    """Generate all visualization plots and save them."""
    
    # Ensure output directory exists
    os.makedirs(PLOTS_DIR, exist_ok=True)
    
    plots = [
        ('theorem_0_2_1_total_field_cross_sections.png', plot_total_field_cross_sections),
        ('theorem_0_2_1_energy_density.png', plot_energy_density_distribution),
        ('theorem_0_2_1_coherent_vs_incoherent.png', plot_coherent_vs_incoherent),
        ('theorem_0_2_1_gradient_field.png', plot_gradient_field),
        ('theorem_0_2_1_energy_convergence.png', plot_energy_integral_convergence),
        ('theorem_0_2_1_summary.png', plot_summary),
    ]
    
    for filename, plot_func in plots:
        print(f"Generating {filename}...")
        fig = plot_func()
        filepath = os.path.join(PLOTS_DIR, filename)
        fig.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.close(fig)
        print(f"  Saved to {filepath}")
    
    print(f"\nAll plots saved to {PLOTS_DIR}")


def main():
    """Main entry point."""
    print("=" * 70)
    print("Theorem 0.2.1: Total Field from Superposition - Visualizations")
    print("=" * 70)
    print()
    
    generate_all_plots()
    
    print()
    print("=" * 70)
    print("Visualization generation complete!")
    print("=" * 70)


if __name__ == "__main__":
    main()
