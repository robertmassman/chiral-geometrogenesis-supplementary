#!/usr/bin/env python3
"""
Diagonal Slice (x=y plane) - Basic Recreation
==============================================

Recreates the third panel of theorem_5_1_1_energy_distribution.png
to understand exactly what it's showing.

The slice: position(x, z) = (x, x, z)
- Horizontal axis: x (and y=x)
- Vertical axis: z

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# =============================================================================
# Physical Constants - Same as theorem_5_1_1
# =============================================================================

EPSILON = 0.5
A0 = 1.0
R_STELLA = 1.0
OMEGA_0 = 200.0
LAMBDA_CHI = 0.1
V0 = 1.0

# Stella octangula vertices (same as theorem_5_1_1)
VERTICES = {
    'R': np.array([1, 1, 1]) / np.sqrt(3) * R_STELLA,
    'G': np.array([1, -1, -1]) / np.sqrt(3) * R_STELLA,
    'B': np.array([-1, 1, -1]) / np.sqrt(3) * R_STELLA,
    'W': np.array([-1, -1, 1]) / np.sqrt(3) * R_STELLA
}

PHASES = {
    'R': 0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3
}

# =============================================================================
# Field Functions - Same as theorem_5_1_1
# =============================================================================

def pressure_function(x, vertex):
    r_sq = np.sum((x - vertex)**2)
    return 1.0 / (r_sq + EPSILON**2)

def chi_total(x):
    result = 0j
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, VERTICES[c])
        a_c = A0 * P_c
        result += a_c * np.exp(1j * PHASES[c])
    return result

def v_chi(x):
    return np.abs(chi_total(x))

def mexican_hat_potential(x):
    v = v_chi(x)
    return LAMBDA_CHI * (v**2 - V0**2)**2

def gradient_chi_numerical(x, h=1e-6):
    grad = np.zeros(3, dtype=complex)
    for i in range(3):
        x_plus = x.copy()
        x_minus = x.copy()
        x_plus[i] += h
        x_minus[i] -= h
        grad[i] = (chi_total(x_plus) - chi_total(x_minus)) / (2 * h)
    return grad

def grad_chi_squared(x):
    grad = gradient_chi_numerical(x)
    return np.sum(np.abs(grad)**2)

def energy_density(x, omega=OMEGA_0):
    v = v_chi(x)
    grad_sq = grad_chi_squared(x)
    V = mexican_hat_potential(x)
    return omega**2 * v**2 + grad_sq + V

# =============================================================================
# Main Plot
# =============================================================================

def main():
    """Create the diagonal slice plot matching theorem_5_1_1's third panel."""

    fig, ax = plt.subplots(figsize=(8, 7))

    n_points = 100
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    print("Computing energy density on diagonal slice (x=y)...")
    rho_grid = np.zeros((n_points, n_points))

    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            # Diagonal slice: position = (x, x, z)
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density(pos)

    # Log scale for better visualization (same as theorem_5_1_1)
    rho_log = np.log10(rho_grid + 1)

    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='hot')

    # Mark vertices (projected onto this slice)
    # For each vertex (vx, vy, vz), we project to (vx, vz) and mark
    for name, vertex in VERTICES.items():
        if name in ['R', 'G', 'B']:
            # Plot at (vx, vz) position
            ax.plot(vertex[0], vertex[2], 'wo', markersize=10, markeredgecolor='black')
            ax.annotate(name, (vertex[0] + 0.08, vertex[2] + 0.08), fontsize=12, color='white',
                       fontweight='bold')

    # W vertex
    ax.plot(VERTICES['W'][0], VERTICES['W'][2], 'wo', markersize=10, markeredgecolor='black')
    ax.annotate('W', (VERTICES['W'][0] + 0.08, VERTICES['W'][2] + 0.08), fontsize=12, color='white',
               fontweight='bold')

    # Mark center
    ax.plot(0, 0, 'c+', markersize=15, markeredgewidth=3)

    ax.set_xlabel('x / R_stella', fontsize=12)
    ax.set_ylabel('z / R_stella', fontsize=12)
    ax.set_title('log₁₀(T₀₀ + 1) (Diagonal (x=y))', fontsize=14)
    ax.set_aspect('equal')

    plt.colorbar(im, ax=ax, label='log₁₀(ρ + 1)')

    # Print vertex positions for understanding
    print("\nVertex positions (3D):")
    for name, v in VERTICES.items():
        on_diagonal = "YES" if abs(v[0] - v[1]) < 0.01 else "NO"
        print(f"  {name}: ({v[0]:.3f}, {v[1]:.3f}, {v[2]:.3f}) - On x=y diagonal: {on_diagonal}")

    print("\nThe dark diagonal band is where the coherent field χ_total ≈ 0")
    print("This is the 'singlet axis' region - color neutrality → vacuum state")

    plt.suptitle('Theorem 5.1.1 Third Panel Recreation\nDiagonal Slice (x=y plane)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)
    path = output_dir / "diagonal_slice_basic.png"
    fig.savefig(path, dpi=150, bbox_inches='tight')
    print(f"\nSaved: {path}")
    plt.close()

if __name__ == "__main__":
    main()
