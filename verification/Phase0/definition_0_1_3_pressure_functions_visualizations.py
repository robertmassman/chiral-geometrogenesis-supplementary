#!/usr/bin/env python3
"""
Visualizations for Definition 0.1.3: Pressure Functions from Geometric Opposition

This script generates visualization plots for:
1. Pressure function profiles from vertices
2. Total pressure field in cross-sections
3. Phase-lock at center demonstration
4. Vertex-face pressure duality
5. 3D stella octangula (two interlocked tetrahedra) with pressure coloring
6. Depression ratio visualization
7. Energy density distribution

Note: The "stella octangula" refers to two interlocked tetrahedra forming an 8-vertex
structure with 6 color vertices and 2 singlet vertices.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
import os
from typing import Dict, List, Tuple, Optional
from matplotlib import cm
from matplotlib.colors import LinearSegmentedColormap

# Set up plotting style
plt.style.use('seaborn-v0_8-whitegrid')
plt.rcParams['figure.figsize'] = (10, 8)
plt.rcParams['font.size'] = 12
plt.rcParams['axes.labelsize'] = 14
plt.rcParams['axes.titlesize'] = 16

# =============================================================================
# CONSTANTS
# =============================================================================

# Regularization parameter (visualization value)
EPSILON = 0.05

# Primitive cube root of unity
OMEGA = np.exp(2j * np.pi / 3)

# Color phases (Definition 0.1.2)
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Color RGB values for plotting
COLORS = {
    'R': '#FF0000',
    'G': '#00AA00',
    'B': '#0000FF',
    'W': '#808080',
    'R_bar': '#AA0000',
    'G_bar': '#006600',
    'B_bar': '#0000AA',
    'W_bar': '#505050',
}

# Stella octangula vertices - Tetrahedron T+ (quark colors R, G, B + singlet W)
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Tetrahedron T- (anti-quark colors R̄, Ḡ, B̄ + anti-singlet W̄)
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}


# =============================================================================
# PRESSURE FUNCTIONS
# =============================================================================

def pressure_function(x: np.ndarray, x_c: np.ndarray, epsilon: float = EPSILON) -> float:
    """
    Compute the pressure function P_c(x) = 1 / (|x - x_c|² + ε²)
    """
    dist_squared = np.sum((x - x_c)**2)
    return 1.0 / (dist_squared + epsilon**2)


def pressure_function_vectorized(X: np.ndarray, Y: np.ndarray, Z: np.ndarray, 
                                 x_c: np.ndarray, epsilon: float = EPSILON) -> np.ndarray:
    """
    Vectorized pressure function for 3D grid evaluation.
    """
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_pressure_vectorized(X: np.ndarray, Y: np.ndarray, Z: np.ndarray,
                             epsilon: float = EPSILON) -> np.ndarray:
    """
    Vectorized total pressure from R, G, B sources.
    """
    P_total = np.zeros_like(X)
    for c in ['R', 'G', 'B']:
        P_total += pressure_function_vectorized(X, Y, Z, VERTICES_PLUS[c], epsilon)
    return P_total


def chiral_field_vectorized(X: np.ndarray, Y: np.ndarray, Z: np.ndarray,
                           epsilon: float = EPSILON) -> np.ndarray:
    """
    Vectorized total chiral field magnitude |χ_total|.
    """
    chi_total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_vectorized(X, Y, Z, VERTICES_PLUS[c], epsilon)
        chi_total += P_c * np.exp(1j * PHASES[c])
    return np.abs(chi_total)


def depression_ratio_vectorized(X: np.ndarray, Y: np.ndarray, Z: np.ndarray,
                                color: str, epsilon: float = EPSILON) -> np.ndarray:
    """
    Vectorized depression ratio D_c(x) = (P_c' + P_c'') / P_c
    """
    P_c = pressure_function_vectorized(X, Y, Z, VERTICES_PLUS[color], epsilon)
    other_colors = [c for c in ['R', 'G', 'B'] if c != color]
    P_others = sum(pressure_function_vectorized(X, Y, Z, VERTICES_PLUS[c], epsilon) 
                   for c in other_colors)
    return P_others / P_c


# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def plot_pressure_profiles(save_path: Optional[str] = None) -> None:
    """
    Plot pressure function profiles along different directions.
    
    Shows:
    - P_R, P_G, P_B along the line from origin toward each vertex
    - P_total along same directions
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    epsilon = EPSILON
    
    # Along the line from R to R̄ (passing through origin)
    ax = axes[0, 0]
    t = np.linspace(-1.5, 1.5, 500)
    direction = VERTICES_PLUS['R'] / np.linalg.norm(VERTICES_PLUS['R'])
    
    for c in ['R', 'G', 'B']:
        P_values = []
        for ti in t:
            x = ti * direction
            P = pressure_function(x, VERTICES_PLUS[c], epsilon)
            P_values.append(P)
        ax.plot(t, P_values, color=COLORS[c], linewidth=2, label=f'$P_{c}$')
    
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=1, color='red', linestyle=':', alpha=0.5, label='R vertex')
    ax.axvline(x=-1, color='red', linestyle=':', alpha=0.5, label='$\\bar{{R}}$ vertex')
    ax.set_xlabel('Distance along R direction')
    ax.set_ylabel('Pressure')
    ax.set_title('Pressure along R-axis')
    ax.legend()
    ax.set_ylim(0, 50)
    ax.grid(True, alpha=0.3)
    
    # Along the line from G to Ḡ
    ax = axes[0, 1]
    direction = VERTICES_PLUS['G'] / np.linalg.norm(VERTICES_PLUS['G'])
    
    for c in ['R', 'G', 'B']:
        P_values = []
        for ti in t:
            x = ti * direction
            P = pressure_function(x, VERTICES_PLUS[c], epsilon)
            P_values.append(P)
        ax.plot(t, P_values, color=COLORS[c], linewidth=2, label=f'$P_{c}$')
    
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=1, color='green', linestyle=':', alpha=0.5, label='G vertex')
    ax.axvline(x=-1, color='green', linestyle=':', alpha=0.5, label='$\\bar{{G}}$ vertex')
    ax.set_xlabel('Distance along G direction')
    ax.set_ylabel('Pressure')
    ax.set_title('Pressure along G-axis')
    ax.legend()
    ax.set_ylim(0, 50)
    ax.grid(True, alpha=0.3)
    
    # Along the line from B to B̄
    ax = axes[1, 0]
    direction = VERTICES_PLUS['B'] / np.linalg.norm(VERTICES_PLUS['B'])
    
    for c in ['R', 'G', 'B']:
        P_values = []
        for ti in t:
            x = ti * direction
            P = pressure_function(x, VERTICES_PLUS[c], epsilon)
            P_values.append(P)
        ax.plot(t, P_values, color=COLORS[c], linewidth=2, label=f'$P_{c}$')
    
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=1, color='blue', linestyle=':', alpha=0.5, label='B vertex')
    ax.axvline(x=-1, color='blue', linestyle=':', alpha=0.5, label='$\\bar{{B}}$ vertex')
    ax.set_xlabel('Distance along B direction')
    ax.set_ylabel('Pressure')
    ax.set_title('Pressure along B-axis')
    ax.legend()
    ax.set_ylim(0, 50)
    ax.grid(True, alpha=0.3)
    
    # Total pressure along all three directions
    ax = axes[1, 1]
    
    for label, c in [('R-axis', 'R'), ('G-axis', 'G'), ('B-axis', 'B')]:
        direction = VERTICES_PLUS[c] / np.linalg.norm(VERTICES_PLUS[c])
        P_total_values = []
        for ti in t:
            x = ti * direction
            P_total = sum(pressure_function(x, VERTICES_PLUS[col], epsilon) 
                         for col in ['R', 'G', 'B'])
            P_total_values.append(P_total)
        ax.plot(t, P_total_values, color=COLORS[c], linewidth=2, label=f'Along {label}')
    
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5, label='Origin')
    ax.set_xlabel('Distance from origin')
    ax.set_ylabel('Total Pressure')
    ax.set_title('Total Pressure $P_{total} = P_R + P_G + P_B$')
    ax.legend()
    ax.set_ylim(0, 50)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_pressure_cross_sections(save_path: Optional[str] = None) -> None:
    """
    Plot pressure field cross-sections through the stella octangula.
    
    Shows 2D slices of total pressure and individual color pressures.
    """
    fig, axes = plt.subplots(2, 3, figsize=(16, 11))
    
    epsilon = EPSILON
    
    # Create grid
    N = 200
    extent = 1.3
    x = np.linspace(-extent, extent, N)
    y = np.linspace(-extent, extent, N)
    X, Y = np.meshgrid(x, y)
    
    # z = 0 plane (through origin)
    Z_plane = np.zeros_like(X)
    
    # Individual color pressures (top row)
    for idx, c in enumerate(['R', 'G', 'B']):
        ax = axes[0, idx]
        P = pressure_function_vectorized(X, Y, Z_plane, VERTICES_PLUS[c], epsilon)
        
        # Log scale for visualization
        P_log = np.log10(P + 0.1)
        
        im = ax.contourf(X, Y, P_log, levels=50, cmap='hot')
        plt.colorbar(im, ax=ax, label='log₁₀(P)')
        
        # Mark vertex projection
        v = VERTICES_PLUS[c]
        ax.scatter([v[0]], [v[1]], c=COLORS[c], s=100, marker='o', edgecolor='white', linewidth=2)
        ax.scatter([0], [0], c='white', s=50, marker='+', linewidth=2)
        
        ax.set_xlabel('x')
        ax.set_ylabel('y')
        ax.set_title(f'$P_{c}(x)$ in z=0 plane')
        ax.set_aspect('equal')
    
    # Total pressure (bottom left)
    ax = axes[1, 0]
    P_total = total_pressure_vectorized(X, Y, Z_plane, epsilon)
    P_total_log = np.log10(P_total + 0.1)
    
    im = ax.contourf(X, Y, P_total_log, levels=50, cmap='viridis')
    plt.colorbar(im, ax=ax, label='log₁₀(P)')
    
    # Mark all vertices
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax.scatter([v[0]], [v[1]], c=COLORS[c], s=100, marker='o', edgecolor='white', linewidth=2)
    ax.scatter([0], [0], c='white', s=50, marker='+', linewidth=2)
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('$P_{total}$ in z=0 plane')
    ax.set_aspect('equal')
    
    # Chiral field magnitude (bottom middle)
    ax = axes[1, 1]
    chi_mag = chiral_field_vectorized(X, Y, Z_plane, epsilon)
    
    im = ax.contourf(X, Y, chi_mag, levels=50, cmap='plasma')
    plt.colorbar(im, ax=ax, label='|χ|')
    
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax.scatter([v[0]], [v[1]], c=COLORS[c], s=100, marker='o', edgecolor='white', linewidth=2)
    ax.scatter([0], [0], c='cyan', s=100, marker='*', edgecolor='white', linewidth=2, label='Node')
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('$|\\chi_{total}|$ in z=0 plane\n(Star = phase-lock node)')
    ax.set_aspect('equal')
    
    # Radial profile of chiral field magnitude
    ax = axes[1, 2]
    
    r = np.linspace(0, 1.5, 200)
    directions = [
        ('→ R', VERTICES_PLUS['R']),
        ('→ G', VERTICES_PLUS['G']),
        ('→ B', VERTICES_PLUS['B']),
    ]
    
    for label, v in directions:
        direction = v / np.linalg.norm(v)
        chi_vals = []
        for ri in r:
            x = ri * direction
            chi_total = sum(pressure_function(x, VERTICES_PLUS[c], epsilon) * np.exp(1j * PHASES[c])
                           for c in ['R', 'G', 'B'])
            chi_vals.append(np.abs(chi_total))
        ax.plot(r, chi_vals, linewidth=2, label=label)
    
    ax.axhline(y=0, color='cyan', linestyle='--', alpha=0.7, label='Node at origin')
    ax.set_xlabel('Distance from origin')
    ax.set_ylabel('$|\\chi_{total}|$')
    ax.set_title('Chiral field magnitude vs. distance')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_phase_lock_demonstration(save_path: Optional[str] = None) -> None:
    """
    Visualize the phase-lock at center mechanism.
    
    Shows how the three phase vectors cancel at the origin.
    """
    fig = plt.figure(figsize=(14, 10))
    
    epsilon = EPSILON
    
    # Panel 1: Phase vectors at origin (perfect cancellation)
    ax1 = fig.add_subplot(2, 2, 1)
    
    P_0 = 1.0 / (1.0 + epsilon**2)
    
    # Draw the three phase vectors
    for c, color in [('R', 'red'), ('G', 'green'), ('B', 'blue')]:
        phase = PHASES[c]
        amplitude = P_0
        z = amplitude * np.exp(1j * phase)
        ax1.arrow(0, 0, z.real, z.imag, head_width=0.02, head_length=0.01,
                 fc=color, ec=color, linewidth=2)
        ax1.annotate(f'$\\chi_{c}(0)$', (z.real * 1.1, z.imag * 1.1), 
                    color=color, fontsize=12)
    
    # Draw unit circle for reference
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(P_0 * np.cos(theta), P_0 * np.sin(theta), 'k--', alpha=0.3)
    
    # Show that sum is zero
    ax1.scatter([0], [0], c='cyan', s=100, marker='*', zorder=5)
    ax1.annotate('$\\sum \\chi_c = 0$', (0.05, -0.1), fontsize=12, color='cyan')
    
    ax1.set_xlim(-1.2, 1.2)
    ax1.set_ylim(-1.2, 1.2)
    ax1.set_aspect('equal')
    ax1.axhline(y=0, color='gray', linewidth=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.5)
    ax1.set_xlabel('Re')
    ax1.set_ylabel('Im')
    ax1.set_title(f'Phase-Lock at Center\n(Equal pressures $P_c(0) = {P_0:.4f}$)')
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: Phase vectors off-center (imperfect cancellation)
    ax2 = fig.add_subplot(2, 2, 2)
    
    # Position near R vertex
    x_off = 0.3 * VERTICES_PLUS['R']
    
    vectors = []
    for c, color in [('R', 'red'), ('G', 'green'), ('B', 'blue')]:
        P_c = pressure_function(x_off, VERTICES_PLUS[c], epsilon)
        phase = PHASES[c]
        z = P_c * np.exp(1j * phase)
        vectors.append(z)
        ax2.arrow(0, 0, z.real, z.imag, head_width=0.05, head_length=0.03,
                 fc=color, ec=color, linewidth=2, alpha=0.7)
        ax2.annotate(f'$\\chi_{c}$', (z.real * 1.1, z.imag * 1.1), 
                    color=color, fontsize=12)
    
    # Show the resultant
    resultant = sum(vectors)
    ax2.arrow(0, 0, resultant.real, resultant.imag, head_width=0.08, head_length=0.05,
             fc='purple', ec='purple', linewidth=3)
    ax2.annotate(f'$\\chi_{{total}}$\n$|\\chi| = {np.abs(resultant):.3f}$', 
                (resultant.real * 1.3, resultant.imag * 1.3), 
                color='purple', fontsize=12)
    
    ax2.set_xlim(-3, 5)
    ax2.set_ylim(-3, 3)
    ax2.set_aspect('equal')
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_xlabel('Re')
    ax2.set_ylabel('Im')
    ax2.set_title('Off-Center (toward R vertex)\nIncomplete cancellation')
    ax2.grid(True, alpha=0.3)
    
    # Panel 3: Chiral field magnitude contour
    ax3 = fig.add_subplot(2, 2, 3)
    
    N = 100
    x = np.linspace(-1.2, 1.2, N)
    y = np.linspace(-1.2, 1.2, N)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    chi_mag = chiral_field_vectorized(X, Y, Z, epsilon)
    
    # Create contour plot
    levels = np.linspace(0, np.max(chi_mag) * 0.8, 20)
    contour = ax3.contourf(X, Y, chi_mag, levels=levels, cmap='plasma')
    plt.colorbar(contour, ax=ax3, label='$|\\chi_{total}|$')
    
    # Mark vertices and origin
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax3.scatter([v[0]], [v[1]], c=COLORS[c], s=100, marker='o', 
                   edgecolor='white', linewidth=2)
    ax3.scatter([0], [0], c='cyan', s=200, marker='*', edgecolor='white', 
               linewidth=2, zorder=5)
    
    ax3.set_xlabel('x')
    ax3.set_ylabel('y')
    ax3.set_title('$|\\chi_{total}|$ in z=0 plane\nCyan star = node at origin')
    ax3.set_aspect('equal')
    
    # Panel 4: Radial dependence of components
    ax4 = fig.add_subplot(2, 2, 4)
    
    r = np.linspace(0, 1.5, 200)
    direction = VERTICES_PLUS['R'] / np.linalg.norm(VERTICES_PLUS['R'])
    
    chi_total_vals = []
    chi_R_vals = []
    chi_G_vals = []
    chi_B_vals = []
    
    for ri in r:
        x = ri * direction
        for c, vals in [('R', chi_R_vals), ('G', chi_G_vals), ('B', chi_B_vals)]:
            P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
            vals.append(P_c)
        
        chi_total = sum(pressure_function(x, VERTICES_PLUS[c], epsilon) * np.exp(1j * PHASES[c])
                       for c in ['R', 'G', 'B'])
        chi_total_vals.append(np.abs(chi_total))
    
    ax4.plot(r, chi_R_vals, 'r-', linewidth=2, label='$P_R$ (amplitude)')
    ax4.plot(r, chi_G_vals, 'g-', linewidth=2, label='$P_G$ (amplitude)')
    ax4.plot(r, chi_B_vals, 'b-', linewidth=2, label='$P_B$ (amplitude)')
    ax4.plot(r, chi_total_vals, 'purple', linewidth=3, label='$|\\chi_{total}|$')
    
    ax4.axvline(x=0, color='cyan', linestyle='--', linewidth=2, alpha=0.7)
    ax4.axvline(x=1, color='red', linestyle=':', alpha=0.5)
    
    ax4.set_xlabel('Distance from origin (toward R)')
    ax4.set_ylabel('Value')
    ax4.set_title('Components along R direction\n(Equal amplitudes at origin → cancellation)')
    ax4.legend()
    ax4.set_ylim(0, 30)
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_stella_octangula_3d(save_path: Optional[str] = None) -> None:
    """
    Plot the 3D stella octangula (two interlocked tetrahedra) with pressure coloring.
    """
    fig = plt.figure(figsize=(14, 10))
    
    ax = fig.add_subplot(111, projection='3d')
    
    # Get vertices
    verts_plus = [VERTICES_PLUS[c] for c in ['R', 'G', 'B', 'W']]
    verts_minus = [VERTICES_MINUS[c] for c in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    
    # Define faces for each tetrahedron
    faces_plus = [
        [verts_plus[0], verts_plus[1], verts_plus[2]],  # RGB
        [verts_plus[0], verts_plus[1], verts_plus[3]],  # RGW
        [verts_plus[0], verts_plus[2], verts_plus[3]],  # RBW
        [verts_plus[1], verts_plus[2], verts_plus[3]],  # GBW
    ]
    
    faces_minus = [
        [verts_minus[0], verts_minus[1], verts_minus[2]],
        [verts_minus[0], verts_minus[1], verts_minus[3]],
        [verts_minus[0], verts_minus[2], verts_minus[3]],
        [verts_minus[1], verts_minus[2], verts_minus[3]],
    ]
    
    # Plot T+ tetrahedron (semi-transparent blue)
    poly_plus = Poly3DCollection(faces_plus, alpha=0.3, facecolor='blue', edgecolor='blue')
    ax.add_collection3d(poly_plus)
    
    # Plot T- tetrahedron (semi-transparent red)
    poly_minus = Poly3DCollection(faces_minus, alpha=0.3, facecolor='red', edgecolor='red')
    ax.add_collection3d(poly_minus)
    
    # Plot vertices with colors
    for name, pos in VERTICES_PLUS.items():
        ax.scatter(*pos, c=COLORS[name], s=200, marker='o', edgecolors='black', linewidth=1)
        ax.text(pos[0]*1.15, pos[1]*1.15, pos[2]*1.15, name, fontsize=12, 
               color=COLORS[name], fontweight='bold')
    
    for name, pos in VERTICES_MINUS.items():
        ax.scatter(*pos, c=COLORS[name], s=200, marker='s', edgecolors='black', linewidth=1)
        short_name = name.replace('_bar', '̄')
        ax.text(pos[0]*1.15, pos[1]*1.15, pos[2]*1.15, short_name, fontsize=10, 
               color=COLORS[name])
    
    # Plot origin (phase-lock node)
    ax.scatter([0], [0], [0], c='cyan', s=300, marker='*', edgecolors='black', 
              linewidth=1, zorder=10)
    ax.text(0.1, 0.1, 0.1, 'Node', fontsize=10, color='cyan')
    
    # Add coordinate axes
    axis_length = 1.2
    ax.quiver(0, 0, 0, axis_length, 0, 0, color='gray', arrow_length_ratio=0.1, alpha=0.5)
    ax.quiver(0, 0, 0, 0, axis_length, 0, color='gray', arrow_length_ratio=0.1, alpha=0.5)
    ax.quiver(0, 0, 0, 0, 0, axis_length, color='gray', arrow_length_ratio=0.1, alpha=0.5)
    ax.text(axis_length, 0, 0, 'x', fontsize=10)
    ax.text(0, axis_length, 0, 'y', fontsize=10)
    ax.text(0, 0, axis_length, 'z', fontsize=10)
    
    # Plot unit sphere (inscribed)
    u = np.linspace(0, 2 * np.pi, 30)
    v = np.linspace(0, np.pi, 20)
    x_sphere = 0.5 * np.outer(np.cos(u), np.sin(v))
    y_sphere = 0.5 * np.outer(np.sin(u), np.sin(v))
    z_sphere = 0.5 * np.outer(np.ones(np.size(u)), np.cos(v))
    ax.plot_wireframe(x_sphere, y_sphere, z_sphere, alpha=0.1, color='gray')
    
    ax.set_xlabel('X')
    ax.set_ylabel('Y')
    ax.set_zlabel('Z')
    ax.set_title('Stella Octangula: Two Interlocked Tetrahedra\n'
                'T+ (blue, circles): R,G,B,W | T- (red, squares): R̄,Ḡ,B̄,W̄')
    
    # Set equal aspect ratio
    ax.set_xlim(-1.2, 1.2)
    ax.set_ylim(-1.2, 1.2)
    ax.set_zlim(-1.2, 1.2)
    ax.set_box_aspect([1, 1, 1])
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_vertex_face_duality(save_path: Optional[str] = None) -> None:
    """
    Visualize the vertex-face pressure duality from Section 7.
    
    Shows:
    - Face centers opposite each vertex
    - Pressure distribution at face centers
    - Depression ratio visualization
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    epsilon = EPSILON
    
    # Panel 1: Face center positions (2D projection)
    ax = axes[0, 0]
    
    # Project vertices onto z=0 plane for visualization
    for c in ['R', 'G', 'B', 'W']:
        v = VERTICES_PLUS[c]
        ax.scatter([v[0]], [v[1]], c=COLORS[c], s=200, marker='o', 
                  edgecolors='black', linewidth=1, label=f'{c} vertex')
        
        # Face center opposite this vertex
        face_center = -v / 3
        ax.scatter([face_center[0]], [face_center[1]], c=COLORS[c], s=100, 
                  marker='^', edgecolors='black', linewidth=1, alpha=0.6)
        
        # Draw line connecting vertex to opposite face center
        ax.plot([v[0], face_center[0]], [v[1], face_center[1]], 
               color=COLORS[c], linestyle='--', alpha=0.3)
    
    ax.scatter([0], [0], c='cyan', s=100, marker='*', edgecolors='black', 
              linewidth=1, zorder=10)
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('Vertex-Face Correspondence (z=0 projection)\n'
                'Circles = vertices, Triangles = opposite face centers')
    ax.set_aspect('equal')
    ax.legend(loc='upper right', fontsize=9)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(-1.0, 1.0)
    ax.set_ylim(-1.0, 1.0)
    
    # Panel 2: Pressure distribution at face centers (bar chart)
    ax = axes[0, 1]
    
    face_data = {}
    for c in ['R', 'G', 'B']:
        x_face = -VERTICES_PLUS[c] / 3
        face_data[c] = {
            'P_R': pressure_function(x_face, VERTICES_PLUS['R'], epsilon),
            'P_G': pressure_function(x_face, VERTICES_PLUS['G'], epsilon),
            'P_B': pressure_function(x_face, VERTICES_PLUS['B'], epsilon),
        }
    
    x_positions = np.arange(3)
    width = 0.25
    
    for i, face in enumerate(['R', 'G', 'B']):
        pressures = [face_data[face]['P_R'], face_data[face]['P_G'], face_data[face]['P_B']]
        offset = (i - 1) * width
        bars = ax.bar(x_positions + offset, pressures, width, 
                     label=f'Face opposite {face}', alpha=0.8)
        # Color bars to match their pressure source
        for bar, color in zip(bars, ['R', 'G', 'B']):
            bar.set_color(COLORS[color])
    
    ax.set_xticks(x_positions)
    ax.set_xticklabels(['$P_R$', '$P_G$', '$P_B$'])
    ax.set_ylabel('Pressure')
    ax.set_title('Pressure Distribution at Face Centers\n'
                '(Suppressed color has lower pressure at its opposite face)')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')
    
    # Panel 3: Depression ratio map
    ax = axes[1, 0]
    
    N = 100
    x = np.linspace(-1.0, 1.0, N)
    y = np.linspace(-1.0, 1.0, N)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    # Choose one color to visualize
    D_R = depression_ratio_vectorized(X, Y, Z, 'R', epsilon)
    
    # Cap values for visualization
    D_R_capped = np.clip(D_R, 0, 10)
    
    im = ax.contourf(X, Y, D_R_capped, levels=30, cmap='RdYlBu_r')
    plt.colorbar(im, ax=ax, label='$D_R = (P_G + P_B) / P_R$')
    
    # Mark special points
    ax.scatter([VERTICES_PLUS['R'][0]], [VERTICES_PLUS['R'][1]], 
              c='red', s=200, marker='o', edgecolors='white', linewidth=2)
    face_R = -VERTICES_PLUS['R'] / 3
    ax.scatter([face_R[0]], [face_R[1]], c='red', s=100, marker='^', 
              edgecolors='white', linewidth=2)
    ax.scatter([0], [0], c='cyan', s=100, marker='*', edgecolors='white', linewidth=2)
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('Depression Ratio $D_R$ in z=0 plane\n'
                '$D_R > 1$ means R is suppressed (blue regions)')
    ax.set_aspect('equal')
    
    # Panel 4: Depression ratio along radial directions
    ax = axes[1, 1]
    
    r = np.linspace(0.01, 1.2, 200)
    
    for c in ['R', 'G', 'B']:
        direction = VERTICES_PLUS[c] / np.linalg.norm(VERTICES_PLUS[c])
        D_vals = []
        for ri in r:
            x = ri * direction
            P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
            other_colors = [oc for oc in ['R', 'G', 'B'] if oc != c]
            P_others = sum(pressure_function(x, VERTICES_PLUS[oc], epsilon) for oc in other_colors)
            D_vals.append(P_others / P_c)
        
        ax.plot(r, D_vals, color=COLORS[c], linewidth=2, label=f'$D_{c}$ toward {c}')
    
    ax.axhline(y=2.0, color='cyan', linestyle='--', linewidth=2, label='$D = 2$ (balanced)')
    ax.axhline(y=1.0, color='gray', linestyle=':', alpha=0.5)
    ax.axvline(x=1/3, color='gray', linestyle=':', alpha=0.5, label='Face center distance')
    ax.axvline(x=1.0, color='gray', linestyle=':', alpha=0.5)
    
    ax.set_xlabel('Distance from origin')
    ax.set_ylabel('Depression Ratio')
    ax.set_title('Depression Ratio vs. Distance\n'
                '$D_c \\to 0$ at vertex (dominance), $D_c \\to \\infty$ at anti-vertex')
    ax.legend(loc='upper right')
    ax.set_ylim(0, 10)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_energy_density(save_path: Optional[str] = None) -> None:
    """
    Visualize the energy density distribution from Section 5.
    
    ρ(x) = Σ_c |a_c(x)|² = a_0² Σ_c P_c(x)²
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    epsilon = EPSILON
    a_0 = 1.0
    
    # Panel 1: Energy density cross-section
    ax = axes[0, 0]
    
    N = 150
    x = np.linspace(-1.2, 1.2, N)
    y = np.linspace(-1.2, 1.2, N)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    rho = np.zeros_like(X)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_vectorized(X, Y, Z, VERTICES_PLUS[c], epsilon)
        rho += a_0**2 * P_c**2
    
    # Log scale for visualization
    rho_log = np.log10(rho + 1e-6)
    
    im = ax.contourf(X, Y, rho_log, levels=30, cmap='inferno')
    plt.colorbar(im, ax=ax, label='log₁₀(ρ)')
    
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax.scatter([v[0]], [v[1]], c=COLORS[c], s=100, marker='o', 
                  edgecolors='white', linewidth=2)
    
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_title('Energy Density $\\rho = \\sum_c |a_c|^2$ in z=0 plane')
    ax.set_aspect('equal')
    
    # Panel 2: Radial energy density profile
    ax = axes[0, 1]
    
    r = np.linspace(0, 1.5, 200)
    
    for label, direction in [('Toward R', VERTICES_PLUS['R']), 
                             ('Toward G', VERTICES_PLUS['G']),
                             ('Toward B', VERTICES_PLUS['B']),
                             ('Diagonal (1,1,1)', np.array([1,1,1])/np.sqrt(3))]:
        direction = direction / np.linalg.norm(direction)
        rho_vals = []
        for ri in r:
            x = ri * direction
            rho_point = sum(a_0**2 * pressure_function(x, VERTICES_PLUS[c], epsilon)**2 
                           for c in ['R', 'G', 'B'])
            rho_vals.append(rho_point)
        
        ax.plot(r, rho_vals, linewidth=2, label=label)
    
    ax.axvline(x=1.0, color='gray', linestyle=':', alpha=0.5, label='Vertex distance')
    ax.set_xlabel('Distance from origin')
    ax.set_ylabel('Energy Density $\\rho$')
    ax.set_title('Energy Density Radial Profiles')
    ax.legend()
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)
    
    # Panel 3: Integrated energy (convergence test)
    ax = axes[1, 0]
    
    R_values = np.linspace(0.1, 5.0, 50)
    E_values = []
    
    # Approximate spherical integration
    for R in R_values:
        # Use Monte Carlo integration for simplicity
        n_samples = 5000
        np.random.seed(42)
        
        # Sample uniformly in spherical coordinates
        r_samples = R * np.random.random(n_samples)**(1/3)
        theta_samples = np.arccos(2*np.random.random(n_samples) - 1)
        phi_samples = 2*np.pi*np.random.random(n_samples)
        
        x_samples = r_samples * np.sin(theta_samples) * np.cos(phi_samples)
        y_samples = r_samples * np.sin(theta_samples) * np.sin(phi_samples)
        z_samples = r_samples * np.cos(theta_samples)
        
        # Compute energy density at each point
        rho_samples = np.zeros(n_samples)
        for c in ['R', 'G', 'B']:
            v = VERTICES_PLUS[c]
            dist_sq = (x_samples - v[0])**2 + (y_samples - v[1])**2 + (z_samples - v[2])**2
            P_c = 1.0 / (dist_sq + epsilon**2)
            rho_samples += a_0**2 * P_c**2
        
        # Volume of sphere
        volume = (4/3) * np.pi * R**3
        E_approx = volume * np.mean(rho_samples)
        E_values.append(E_approx)
    
    ax.plot(R_values, E_values, 'b-', linewidth=2)
    ax.set_xlabel('Integration Radius R')
    ax.set_ylabel('Integrated Energy $E(<R)$')
    ax.set_title('Total Energy Convergence\n(Energy bounded as $R \\to \\infty$)')
    ax.grid(True, alpha=0.3)
    
    # Panel 4: Comparison of P² vs P for convergence
    ax = axes[1, 1]
    
    r = np.linspace(0.01, 5.0, 200)
    
    # Single source at origin for comparison
    P_r = 1.0 / (r**2 + epsilon**2)
    P_sq_r = P_r**2
    
    # Integrands: 4πr² × P(r) and 4πr² × P²(r)
    integrand_P = 4 * np.pi * r**2 * P_r
    integrand_P2 = 4 * np.pi * r**2 * P_sq_r
    
    ax.plot(r, integrand_P, 'b-', linewidth=2, label='$4\\pi r^2 P(r)$')
    ax.plot(r, integrand_P2, 'r-', linewidth=2, label='$4\\pi r^2 P^2(r)$')
    
    # Show decay rates
    ax.plot(r, 4 * np.pi / r**0.001, 'b--', alpha=0.3, label='$\\sim$ const (diverges)')
    ax.plot(r, 4 * np.pi / r**2, 'r--', alpha=0.3, label='$\\sim 1/r^2$ (converges)')
    
    ax.set_xlabel('Distance r')
    ax.set_ylabel('Integrand value')
    ax.set_title('Why $P^2$ Integral Converges\n'
                '$\\int r^2 P^2 dr$ converges while $\\int r^2 P dr$ diverges')
    ax.legend()
    ax.set_yscale('log')
    ax.set_xlim(0, 5)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_summary_figure(save_path: Optional[str] = None) -> None:
    """
    Create a comprehensive summary figure for Definition 0.1.3.
    """
    fig = plt.figure(figsize=(16, 12))
    
    epsilon = EPSILON
    
    # Panel 1: Pressure function definition
    ax1 = fig.add_subplot(2, 3, 1)
    
    r = np.linspace(-2, 2, 500)
    P = 1.0 / (r**2 + epsilon**2)
    
    ax1.plot(r, P, 'b-', linewidth=2)
    ax1.fill_between(r, P, alpha=0.2)
    ax1.axvline(x=0, color='red', linestyle='--', alpha=0.5)
    ax1.axhline(y=1/epsilon**2, color='gray', linestyle=':', alpha=0.5)
    
    ax1.set_xlabel('Distance $|x - x_c|$')
    ax1.set_ylabel('$P_c(x)$')
    ax1.set_title(f'Pressure Function\n$P_c(x) = 1/(|x-x_c|^2 + \\varepsilon^2)$\n$\\varepsilon = {epsilon}$')
    ax1.set_ylim(0, 500)
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: Equal pressure at center
    ax2 = fig.add_subplot(2, 3, 2)
    
    P_0 = 1.0 / (1.0 + epsilon**2)
    colors_bar = ['R', 'G', 'B']
    pressures = [P_0, P_0, P_0]
    
    bars = ax2.bar(colors_bar, pressures, color=[COLORS[c] for c in colors_bar], 
                  edgecolor='black', linewidth=2)
    ax2.axhline(y=P_0, color='gray', linestyle='--', alpha=0.7, 
               label=f'$P(0) = {P_0:.4f}$')
    
    ax2.set_ylabel('Pressure at Origin')
    ax2.set_title('Equal Pressure at Center\n$P_R(0) = P_G(0) = P_B(0)$')
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Panel 3: Phase cancellation
    ax3 = fig.add_subplot(2, 3, 3)
    
    theta = np.linspace(0, 2*np.pi, 100)
    ax3.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3)
    
    for c, color in [('R', 'red'), ('G', 'green'), ('B', 'blue')]:
        phase = PHASES[c]
        z = np.exp(1j * phase)
        ax3.arrow(0, 0, z.real*0.9, z.imag*0.9, head_width=0.08, head_length=0.05,
                 fc=color, ec=color, linewidth=2)
        ax3.annotate(f'$e^{{i\\phi_{c}}}$', (z.real*1.15, z.imag*1.15), 
                    color=color, fontsize=12, fontweight='bold')
    
    ax3.scatter([0], [0], c='cyan', s=200, marker='*', zorder=5)
    ax3.annotate('$\\sum = 0$', (0.15, 0.15), fontsize=14, color='cyan')
    
    ax3.set_xlim(-1.5, 1.5)
    ax3.set_ylim(-1.5, 1.5)
    ax3.set_aspect('equal')
    ax3.set_title('Phase-Lock: $1 + \\omega + \\omega^2 = 0$\n$\\Rightarrow \\chi_{total}(0) = 0$')
    ax3.axis('off')
    
    # Panel 4: 2D pressure field
    ax4 = fig.add_subplot(2, 3, 4)
    
    N = 100
    x = np.linspace(-1.2, 1.2, N)
    y = np.linspace(-1.2, 1.2, N)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)
    
    P_total = total_pressure_vectorized(X, Y, Z, epsilon)
    
    im = ax4.contourf(X, Y, np.log10(P_total), levels=30, cmap='viridis')
    plt.colorbar(im, ax=ax4, label='log₁₀($P_{total}$)')
    
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax4.scatter([v[0]], [v[1]], c=COLORS[c], s=150, marker='o', 
                   edgecolors='white', linewidth=2)
    ax4.scatter([0], [0], c='cyan', s=100, marker='*', edgecolors='white', linewidth=2)
    
    ax4.set_xlabel('x')
    ax4.set_ylabel('y')
    ax4.set_title('Total Pressure Field (z=0)')
    ax4.set_aspect('equal')
    
    # Panel 5: Chiral field magnitude
    ax5 = fig.add_subplot(2, 3, 5)
    
    chi_mag = chiral_field_vectorized(X, Y, Z, epsilon)
    
    im = ax5.contourf(X, Y, chi_mag, levels=30, cmap='plasma')
    plt.colorbar(im, ax=ax5, label='$|\\chi_{total}|$')
    
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        ax5.scatter([v[0]], [v[1]], c=COLORS[c], s=150, marker='o', 
                   edgecolors='white', linewidth=2)
    ax5.scatter([0], [0], c='cyan', s=200, marker='*', edgecolors='white', linewidth=2)
    
    ax5.set_xlabel('x')
    ax5.set_ylabel('y')
    ax5.set_title('Chiral Field $|\\chi_{total}|$ (z=0)\nStar = node where $|\\chi| = 0$')
    ax5.set_aspect('equal')
    
    # Panel 6: Key results summary
    ax6 = fig.add_subplot(2, 3, 6)
    ax6.axis('off')
    
    summary_text = """
    Definition 0.1.3 Summary
    ════════════════════════════
    
    Pressure Function:
    $P_c(x) = \\frac{1}{|x - x_c|^2 + \\varepsilon^2}$
    
    Key Properties:
    
    ✓ Equal at center:
      $P_R(0) = P_G(0) = P_B(0)$
    
    ✓ Phase-lock node:
      $\\chi_{total}(0) = 0$
    
    ✓ Antipodal minimum:
      $P_c(x_{\\bar{c}}) = \\min$
    
    ✓ Energy finite:
      $\\int \\rho \, d^3x < \\infty$
    
    ✓ Vertex-face duality:
      Sources at vertices,
      depression at opposite faces
    """
    
    ax6.text(0.1, 0.95, summary_text, transform=ax6.transAxes, 
            fontsize=12, verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def generate_all_visualizations(output_dir: str = None) -> None:
    """
    Generate all visualization plots and save to specified directory.
    """
    if output_dir is None:
        # Default to plots directory in verification folder
        script_dir = os.path.dirname(os.path.abspath(__file__))
        output_dir = os.path.join(script_dir, '..', 'plots')
    
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating Definition 0.1.3 Pressure Functions Visualizations...")
    print(f"Output directory: {output_dir}")
    print("-" * 60)
    
    # Generate each plot
    plot_functions = [
        ('def_0_1_3_pressure_profiles.png', plot_pressure_profiles),
        ('def_0_1_3_pressure_cross_sections.png', plot_pressure_cross_sections),
        ('def_0_1_3_phase_lock.png', plot_phase_lock_demonstration),
        ('def_0_1_3_stella_octangula_3d.png', plot_stella_octangula_3d),
        ('def_0_1_3_vertex_face_duality.png', plot_vertex_face_duality),
        ('def_0_1_3_energy_density.png', plot_energy_density),
        ('def_0_1_3_summary.png', plot_summary_figure),
    ]
    
    for filename, plot_func in plot_functions:
        save_path = os.path.join(output_dir, filename)
        try:
            plot_func(save_path)
        except Exception as e:
            print(f"Error generating {filename}: {e}")
    
    print("-" * 60)
    print("Visualization generation complete.")


if __name__ == '__main__':
    generate_all_visualizations()
