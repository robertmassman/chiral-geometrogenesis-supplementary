#!/usr/bin/env python3
"""
Vacuum Energy Density Visualization for Theorem 5.1.2

Shows the vacuum energy density ρ_vac(x) = λ_χ v_χ⁴(x) on the stella octangula,
demonstrating how phase cancellation causes ρ_vac → 0 at the center.

Key physics:
- Three color fields with phases 0, 2π/3, 4π/3 (cube roots of unity)
- At center: equal amplitudes → phases cancel → v_χ(0) = 0 → ρ_vac(0) = 0
- This suppression mechanism addresses the cosmological constant problem

Proof Document: docs/proofs/Phase5/Theorem-5.1.2-Vacuum-Energy-Density.md

Output: fig_thm_5_1_2_vacuum_energy.pdf and fig_thm_5_1_2_vacuum_energy.png

Usage:
    python fig_thm_5_1_2_vacuum_energy.py
"""

import numpy as np
import plotly.graph_objects as go
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

EXP_PHASES = {
    'R': np.exp(1j * PHASES['R']),
    'G': np.exp(1j * PHASES['G']),
    'B': np.exp(1j * PHASES['B']),
}

# Rotation matrix to align W vertex with +z axis and R with +x axis
def rotation_matrix_to_align_stella():
    """
    Compute rotation matrix that:
    1. Aligns W vertex direction with +z axis
    2. Aligns R vertex with the +x direction (in xy plane)
    """
    # Step 1: Rotate W to z-axis
    w = np.array([-1, -1, 1]) / np.sqrt(3)
    t = np.array([0, 0, 1])

    axis = np.cross(w, t)
    axis_norm = np.linalg.norm(axis)

    if axis_norm < 1e-10:
        R1 = np.eye(3)
    else:
        axis = axis / axis_norm
        cos_angle = np.dot(w, t)
        sin_angle = axis_norm
        K = np.array([
            [0, -axis[2], axis[1]],
            [axis[2], 0, -axis[0]],
            [-axis[1], axis[0], 0]
        ])
        R1 = np.eye(3) + sin_angle * K + (1 - cos_angle) * (K @ K)

    # Step 2: After R1, find where R ends up and rotate around z to align with +x
    R_orig = np.array([1, 1, 1]) / np.sqrt(3)
    R_after_R1 = R1 @ R_orig

    # Angle of R in xy plane (from x-axis)
    angle_R = np.arctan2(R_after_R1[1], R_after_R1[0])

    # Rotation around z-axis by -angle_R to align R with +x
    cos_z = np.cos(-angle_R)
    sin_z = np.sin(-angle_R)
    R2 = np.array([
        [cos_z, -sin_z, 0],
        [sin_z, cos_z, 0],
        [0, 0, 1]
    ])

    # Combined rotation
    return R2 @ R1

ROT_MATRIX = rotation_matrix_to_align_stella()

def rotate_vertex(v):
    """Apply rotation to align stella with axes."""
    return ROT_MATRIX @ v

# Stella octangula vertices (rotated so W is along +z)
VERTICES_PLUS = {
    'R': rotate_vertex(np.array([1, 1, 1]) / np.sqrt(3)),
    'G': rotate_vertex(np.array([1, -1, -1]) / np.sqrt(3)),
    'B': rotate_vertex(np.array([-1, 1, -1]) / np.sqrt(3)),
    'W': rotate_vertex(np.array([-1, -1, 1]) / np.sqrt(3)),
}

VERTICES_MINUS = {
    'R_bar': rotate_vertex(np.array([-1, -1, -1]) / np.sqrt(3)),
    'G_bar': rotate_vertex(np.array([-1, 1, 1]) / np.sqrt(3)),
    'B_bar': rotate_vertex(np.array([1, -1, 1]) / np.sqrt(3)),
    'W_bar': rotate_vertex(np.array([1, 1, -1]) / np.sqrt(3)),
}


# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_grid(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Vectorized total chiral field for grids."""
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def create_stella_traces():
    """Create Plotly traces for stella octangula wireframe."""
    traces = []

    # T+ tetrahedron (blue)
    t_plus = [VERTICES_PLUS[k] for k in ['R', 'G', 'B', 'W']]
    edges_plus = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    ]

    for i, j in edges_plus:
        traces.append(go.Scatter3d(
            x=[t_plus[i][0], t_plus[j][0]],
            y=[t_plus[i][1], t_plus[j][1]],
            z=[t_plus[i][2], t_plus[j][2]],
            mode='lines',
            line=dict(color='blue', width=3),
            showlegend=False,
            hoverinfo='skip'
        ))

    # T- tetrahedron (red)
    t_minus = [VERTICES_MINUS[k] for k in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    edges_minus = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    ]

    for i, j in edges_minus:
        traces.append(go.Scatter3d(
            x=[t_minus[i][0], t_minus[j][0]],
            y=[t_minus[i][1], t_minus[j][1]],
            z=[t_minus[i][2], t_minus[j][2]],
            mode='lines',
            line=dict(color='red', width=3),
            showlegend=False,
            hoverinfo='skip'
        ))

    # Color vertices
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}
    for name, v in VERTICES_PLUS.items():
        traces.append(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=8, color=colors_map[name],
                       line=dict(color='black', width=1)),
            name=f'{name} vertex',
            hoverinfo='name'
        ))

    # Origin marker
    traces.append(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=10, color='white',
                   line=dict(color='black', width=2)),
        name='Origin (ρ_vac=0)',
        hoverinfo='name'
    ))

    return traces


def vacuum_energy_density_grid(X, Y, Z, lambda_chi=1.0):
    """
    Compute vacuum energy density ρ_vac = λ_χ |χ_total|⁴.

    The VEV v_χ = |χ_total| vanishes at the center due to phase cancellation.
    """
    chi_total = total_chiral_field_grid(X, Y, Z)
    v_chi = np.abs(chi_total)
    rho_vac = lambda_chi * v_chi**4
    return rho_vac


def compute_vev_squared_stella(X, Y, Z, epsilon=EPSILON):
    """
    Compute v_χ²(x) using the phase cancellation formula.

    v_χ² = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]

    This vanishes when P_R = P_G = P_B (at the center).

    Also includes contributions from the anti-color vertices (R_bar, G_bar, B_bar)
    to create symmetric structure on both sides of the stella.
    """
    # Get pressure from each color vertex (T+ tetrahedron)
    P_R = pressure_function_grid(X, Y, Z, VERTICES_PLUS['R'], epsilon)
    P_G = pressure_function_grid(X, Y, Z, VERTICES_PLUS['G'], epsilon)
    P_B = pressure_function_grid(X, Y, Z, VERTICES_PLUS['B'], epsilon)

    # Get pressure from anti-color vertices (T- tetrahedron)
    P_R_bar = pressure_function_grid(X, Y, Z, VERTICES_MINUS['R_bar'], epsilon)
    P_G_bar = pressure_function_grid(X, Y, Z, VERTICES_MINUS['G_bar'], epsilon)
    P_B_bar = pressure_function_grid(X, Y, Z, VERTICES_MINUS['B_bar'], epsilon)

    # VEV squared from pressure differences (both tetrahedra)
    v_sq_plus = 0.5 * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)
    v_sq_minus = 0.5 * ((P_R_bar - P_G_bar)**2 + (P_G_bar - P_B_bar)**2 + (P_B_bar - P_R_bar)**2)

    # Combine contributions from both tetrahedra
    v_sq = v_sq_plus + v_sq_minus
    return v_sq


def vacuum_energy_from_vev(X, Y, Z, lambda_chi=1.0, epsilon=EPSILON):
    """
    Compute vacuum energy ρ_vac = λ_χ v_χ⁴.
    """
    v_sq = compute_vev_squared_stella(X, Y, Z, epsilon)
    rho_vac = lambda_chi * v_sq**2  # v⁴ = (v²)²
    return rho_vac


def create_vacuum_energy_surface_vertical_slice(n_points=80, extent=1.8,
                                                 show_colorbar=False, opacity=0.7,
                                                 y_offset=0.0):
    """
    Create a vertical rectangular slice showing ρ_vac in the xz plane.

    This slice is perpendicular to the RGB slices (which are horizontal).
    It passes through the z-axis (where W is located).

    Parameters:
    - n_points: resolution of the grid
    - extent: half-width of the slice in x and z directions
    - show_colorbar: whether to display the colorbar
    - opacity: surface transparency
    - y_offset: offset in y direction (0 = passes through z-axis)
    """
    # Create a simple grid in the xz plane
    x = np.linspace(-extent, extent, n_points)
    z = np.linspace(-extent, extent, n_points)
    X, Z = np.meshgrid(x, z)
    Y = np.full_like(X, y_offset)

    # Compute vacuum energy density
    rho_vac = vacuum_energy_from_vev(X, Y, Z)

    # Use log scale for better visualization
    log_rho = np.log10(rho_vac + 1e-10)

    # Create surface trace
    colorbar_config = dict(
        title='log₁₀(ρ_vac)',
        x=1.02,
        len=0.6
    ) if show_colorbar else None

    surface = go.Surface(
        x=X,
        y=Y,
        z=Z,
        surfacecolor=log_rho,
        colorscale='Viridis',
        showscale=show_colorbar,
        colorbar=colorbar_config,
        opacity=opacity,
        name=f'ρ_vac vertical slice (y={y_offset:.2f})',
        hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>log₁₀(ρ_vac): %{surfacecolor:.2f}<extra></extra>'
    )

    return surface


def create_vertical_slices(n_slices=10, n_points=60, extent=1.8):
    """
    Create multiple vertical slices (xz planes) to form a cube with the RGB slices.

    Uses same step size and extends to same range as RGB slices.

    Returns a list of surface traces.
    """
    surfaces = []

    # Get the same spacing as RGB slices
    R_v = VERTICES_PLUS['R']
    G_v = VERTICES_PLUS['G']
    B_v = VERTICES_PLUS['B']
    W_v = VERTICES_PLUS['W']

    rgb_center = (R_v + G_v + B_v) / 3
    dist_to_W = abs(W_v[2] - rgb_center[2])  # z distance to W (~1.333)

    # Calculate step size used by RGB slices
    rgb_step_size = (dist_to_W * 1.2) / (n_slices + 1)

    # Extend vertical slices to same range as RGB slices (symmetric around 0)
    max_y = dist_to_W * 1.2  # Same extent as z direction

    # Create y values with same step size, symmetric around 0
    y_values_positive = np.arange(0, max_y + rgb_step_size/2, rgb_step_size)
    y_values_negative = np.arange(-rgb_step_size, -max_y - rgb_step_size/2, -rgb_step_size)

    # Add slices toward +y
    for i, y in enumerate(y_values_positive):
        show_colorbar = (i == 0)
        opacity = 0.7 - 0.3 * (i / max(len(y_values_positive) - 1, 1))

        surface = create_vacuum_energy_surface_vertical_slice(
            n_points=n_points,
            extent=extent,
            show_colorbar=show_colorbar,
            opacity=opacity,
            y_offset=y
        )
        surfaces.append(surface)

    # Add slices toward -y
    for i, y in enumerate(y_values_negative):
        show_colorbar = False
        opacity = 0.65 - 0.3 * (i / max(len(y_values_negative) - 1, 1))

        surface = create_vacuum_energy_surface_vertical_slice(
            n_points=n_points,
            extent=extent,
            show_colorbar=show_colorbar,
            opacity=opacity,
            y_offset=y
        )
        surfaces.append(surface)

    return surfaces


def create_vacuum_energy_surface_rgb_plane(n_points=80, radius=1.5, t_param=0.0,
                                           show_colorbar=True, opacity=0.85,
                                           target_vertex='W', apply_mask=False):
    """
    Create a circular disk showing ρ_vac in a plane parallel to the RGB face.

    Parameters:
    - t_param: 0.0 = at RGB plane, 1.0 = at target vertex
              Controls interpolation from RGB centroid toward target
    - radius: radius of the circular disk
    - show_colorbar: whether to display the colorbar (only for one slice)
    - opacity: surface transparency
    - target_vertex: 'W' for T+ tetrahedron, 'W_bar' for T- tetrahedron
    - apply_mask: if True, mask points where x > y (cut by vertical W-aligned plane)
    """
    # Get R, G, B vertex positions
    R_v = VERTICES_PLUS['R']
    G_v = VERTICES_PLUS['G']
    B_v = VERTICES_PLUS['B']

    # Get target vertex
    if target_vertex == 'W':
        target_v = VERTICES_PLUS['W']
    else:  # W_bar
        target_v = VERTICES_MINUS['W_bar']

    # Find center of RGB triangle (centroid)
    rgb_center = (R_v + G_v + B_v) / 3

    # Interpolate center position from RGB centroid toward target
    center = rgb_center + t_param * (target_v - rgb_center)

    # Keep all slices the same size
    effective_radius = radius

    # Create axis-aligned horizontal slice (xy plane at z = center[2])
    # Use x and y axes as basis vectors for proper alignment
    x = np.linspace(-effective_radius, effective_radius, n_points)
    y = np.linspace(-effective_radius, effective_radius, n_points)
    X, Y = np.meshgrid(x, y)
    Z = np.full_like(X, center[2])  # Horizontal plane at z = center's z-coordinate

    # Apply mask if requested (cut by vertical plane x = y)
    if apply_mask:
        mask = X > Y  # Points on one side of the plane x = y
        X = np.where(mask, np.nan, X)
        Y = np.where(mask, np.nan, Y)
        Z = np.where(mask, np.nan, Z)

    # Compute vacuum energy density
    rho_vac = vacuum_energy_from_vev(X, Y, Z)

    # Use log scale for better visualization
    log_rho = np.log10(rho_vac + 1e-10)

    # Create surface trace
    colorbar_config = dict(
        title='log₁₀(ρ_vac)',
        x=1.02,
        len=0.6
    ) if show_colorbar else None

    surface = go.Surface(
        x=X,
        y=Y,
        z=Z,
        surfacecolor=log_rho,
        colorscale='Viridis',
        showscale=show_colorbar,
        colorbar=colorbar_config,
        opacity=opacity,
        name=f'ρ_vac slice (t={t_param:.1f})',
        hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>log₁₀(ρ_vac): %{surfacecolor:.2f}<extra></extra>'
    )

    return surface


def create_vacuum_energy_slices(n_slices=10, n_points=60, radius=1.6):
    """
    Create multiple parallel slices from RGB plane toward both W and W_bar vertices.
    Uses equal physical spacing in both directions.

    Returns a list of surface traces.
    """
    surfaces = []

    # Calculate actual distances from RGB centroid to each target
    R_v = VERTICES_PLUS['R']
    G_v = VERTICES_PLUS['G']
    B_v = VERTICES_PLUS['B']
    rgb_center = (R_v + G_v + B_v) / 3

    W_v = VERTICES_PLUS['W']
    W_bar_v = VERTICES_MINUS['W_bar']

    dist_to_W = np.linalg.norm(W_v - rgb_center)
    dist_to_W_bar = np.linalg.norm(W_bar_v - rgb_center)

    # Use uniform physical spacing based on the W direction
    # Calculate the step size from the W direction
    n_steps_to_W = n_slices
    step_size = (dist_to_W * 1.2) / (n_steps_to_W + 1)  # physical distance per step

    # For W direction: t=1.0 means at W, so t = physical_dist / dist_to_W
    # Slices toward W (including 6 past W - extended)
    t_values_w = np.linspace(0.0, 1.6, n_slices + 6)

    # For W_bar direction: scale t values so physical spacing matches
    # t_wbar = physical_dist / dist_to_W_bar
    # We want same physical step, so t_step_wbar = step_size / dist_to_W_bar
    t_step_wbar = step_size / dist_to_W_bar
    n_steps_wbar = n_slices  # fewer slices toward W_bar (skip t=0)
    t_values_wbar = np.array([t_step_wbar * (i + 1) for i in range(n_steps_wbar)])

    # Add slices toward W
    for i, t in enumerate(t_values_w):
        # Only show colorbar on the first slice
        show_colorbar = (i == 0)
        # Gradually reduce opacity for outer slices to see through
        opacity = 0.9 - 0.4 * (i / (len(t_values_w) - 1)) if len(t_values_w) > 1 else 0.9

        surface = create_vacuum_energy_surface_rgb_plane(
            n_points=n_points,
            radius=radius,
            t_param=t,
            show_colorbar=show_colorbar,
            opacity=opacity,
            target_vertex='W'
        )
        surfaces.append(surface)

    # Add slices toward W_bar
    for i, t in enumerate(t_values_wbar):
        # No colorbar for these (already shown on W side)
        show_colorbar = False
        # Gradually reduce opacity
        opacity = 0.85 - 0.4 * (i / (len(t_values_wbar) - 1)) if len(t_values_wbar) > 1 else 0.85

        surface = create_vacuum_energy_surface_rgb_plane(
            n_points=n_points,
            radius=radius,
            t_param=t,
            show_colorbar=show_colorbar,
            opacity=opacity,
            target_vertex='W_bar'
        )
        surfaces.append(surface)

    return surfaces


def create_isosurface_visualization(n_points=50, extent=1.8):
    """
    Create an isosurface visualization of the vacuum energy density.

    Shows surfaces of constant ρ_vac, revealing the 3D structure.

    Parameters:
    - n_points: resolution of the 3D grid
    - extent: half-width of the volume in each direction
    """
    # Create 3D grid
    x = np.linspace(-extent, extent, n_points)
    y = np.linspace(-extent, extent, n_points)
    z = np.linspace(-extent, extent, n_points)

    X, Y, Z = np.meshgrid(x, y, z, indexing='ij')

    # Compute vacuum energy density throughout the volume
    rho_vac = vacuum_energy_from_vev(X, Y, Z)

    # Use log scale
    log_rho = np.log10(rho_vac + 1e-10)

    # Create isosurface trace
    isosurface = go.Isosurface(
        x=X.flatten(),
        y=Y.flatten(),
        z=Z.flatten(),
        value=log_rho.flatten(),
        isomin=-2,
        isomax=3,
        surface_count=8,  # Number of isosurfaces
        colorscale='Viridis',
        caps=dict(x_show=False, y_show=False, z_show=False),
        opacity=0.6,
        colorbar=dict(
            title='log₁₀(ρ_vac)',
            x=1.02,
            len=0.6
        ),
    )

    return isosurface


def create_triangular_mesh_points(v0, v1, v2, resolution=30):
    """
    Create a mesh of points within a triangle using barycentric coordinates.

    Parameters:
    - v0, v1, v2: vertices of the triangle (numpy arrays)
    - resolution: number of divisions along each edge

    Returns:
    - points: array of 3D points within the triangle
    - triangles: array of triangle indices for mesh connectivity
    """
    points = []
    # Generate points using barycentric coordinates
    for i in range(resolution + 1):
        for j in range(resolution + 1 - i):
            k = resolution - i - j
            # Barycentric coordinates
            u = i / resolution
            v = j / resolution
            w = k / resolution
            # 3D position
            point = u * v0 + v * v1 + w * v2
            points.append(point)

    points = np.array(points)

    # Generate triangle connectivity
    triangles = []
    idx = 0
    for i in range(resolution):
        row_length = resolution + 1 - i
        next_row_length = resolution - i
        for j in range(row_length - 1):
            # First triangle (pointing up)
            triangles.append([idx + j, idx + j + 1, idx + row_length + j])
            # Second triangle (pointing down) - only if not at the end
            if j < next_row_length - 1:
                triangles.append([idx + j + 1, idx + row_length + j + 1, idx + row_length + j])
        idx += row_length

    triangles = np.array(triangles)
    return points, triangles


def create_soap_film_face(v0, v1, v2, resolution=30, show_colorbar=False,
                          opacity=0.85, face_name="face", inward_pull=0.4):
    """
    Create a soap-film-like surface on a triangular face.

    The vacuum energy is computed at each point, showing high intensity
    near edges (vertices) and lower toward the face center.

    The surface curves INWARD toward the stella center (origin), like a
    soap film being pulled by surface tension toward the low-energy region.

    Parameters:
    - v0, v1, v2: vertices of the triangle
    - resolution: mesh resolution
    - show_colorbar: whether to display colorbar
    - opacity: surface transparency
    - face_name: name for hover info
    - inward_pull: how much the center of each face is pulled toward origin (0-1)
    """
    # Generate mesh points within the triangle
    points, triangles = create_triangular_mesh_points(v0, v1, v2, resolution)

    # Calculate face centroid
    face_center = (v0 + v1 + v2) / 3

    # For each point, calculate how "interior" it is (0 at vertices/edges, 1 at center)
    # Use barycentric distance from edges
    for i, point in enumerate(points):
        # Vector from face center to this point
        to_point = point - face_center
        dist_from_face_center = np.linalg.norm(to_point)

        # Maximum distance is from center to a vertex
        max_dist = np.linalg.norm(v0 - face_center)

        # Interior factor: 1 at face center, 0 at vertices
        interior_factor = 1.0 - (dist_from_face_center / max_dist) if max_dist > 0 else 0
        interior_factor = max(0, interior_factor)  # Clamp to non-negative

        # Pull point toward origin (stella center) based on interior factor
        # Points at face center get pulled most, points at edges/vertices stay put
        pull_amount = inward_pull * interior_factor

        # Direction toward origin
        dist_to_origin = np.linalg.norm(point)
        if dist_to_origin > 0:
            toward_origin = -point / dist_to_origin
            points[i] = point + pull_amount * toward_origin * dist_to_origin

    # Compute vacuum energy at each point
    X = points[:, 0]
    Y = points[:, 1]
    Z = points[:, 2]

    rho_vac = vacuum_energy_from_vev(X, Y, Z)
    log_rho = np.log10(rho_vac + 1e-10)

    # Create Mesh3d trace
    mesh = go.Mesh3d(
        x=X,
        y=Y,
        z=Z,
        i=triangles[:, 0],
        j=triangles[:, 1],
        k=triangles[:, 2],
        intensity=log_rho,
        colorscale='Viridis',
        showscale=show_colorbar,
        colorbar=dict(
            title='log₁₀(ρ_vac)',
            x=1.02,
            len=0.6
        ) if show_colorbar else None,
        opacity=opacity,
        name=face_name,
        hovertemplate=f'{face_name}<br>log₁₀(ρ_vac): %{{intensity:.2f}}<extra></extra>',
        flatshading=False,  # Smooth shading
    )

    return mesh


def create_soap_film_visualization(resolution=35, opacity=0.8):
    """
    Create physically accurate soap film visualization on T+ tetrahedron.

    According to Plateau's rules, a soap film on a tetrahedral wire frame forms:
    - SIX triangular planar surfaces (one per edge)
    - Each triangle connects one edge of the tetrahedron to the CENTER point
    - All six triangles meet at the center at ~109° angles
    - Three surfaces meet along each internal edge at 120° angles

    This is the minimal surface configuration that minimizes total surface area.

    Reference: https://americanhistory.si.edu/collections/object-groups/geometric-models-minimal-surfaces-as-soap-films

    Returns a list of Mesh3d traces for the 6 soap film pieces.
    """
    traces = []

    # T+ tetrahedron vertices
    R = VERTICES_PLUS['R']
    G = VERTICES_PLUS['G']
    B = VERTICES_PLUS['B']
    W = VERTICES_PLUS['W']

    # Center of the tetrahedron (where all soap films meet)
    center = np.array([0.0, 0.0, 0.0])  # Origin is the center of stella octangula

    # The 6 edges of the tetrahedron, each gets a triangular soap film piece
    # Each triangle has: two vertices from an edge + the center point
    edges = [
        (R, G, "R-G edge film"),
        (R, B, "R-B edge film"),
        (R, W, "R-W edge film"),
        (G, B, "G-B edge film"),
        (G, W, "G-W edge film"),
        (B, W, "B-W edge film"),
    ]

    for i, (v0, v1, name) in enumerate(edges):
        # Only show colorbar on first film
        show_colorbar = (i == 0)

        # Create triangular soap film from edge to center
        mesh = create_soap_film_face(
            v0, v1, center,
            resolution=resolution,
            show_colorbar=show_colorbar,
            opacity=opacity,
            face_name=name,
            inward_pull=0.0  # Planar surfaces, no curvature needed
        )
        traces.append(mesh)

    return traces


def create_cone_mesh(apex, base_center, height, radius, n_segments=32, color='yellow'):
    """
    Create a cone mesh pointing from base_center toward apex.

    Parameters:
    - apex: tip of the cone (3D point)
    - base_center: center of the cone base (3D point)
    - height: height of the cone
    - radius: radius of the cone base
    - n_segments: number of segments around the base circle
    - color: color of the cone
    """
    # Direction from base to apex
    direction = apex - base_center
    direction = direction / np.linalg.norm(direction)

    # Create orthonormal basis perpendicular to direction
    if abs(direction[2]) < 0.9:
        perp1 = np.cross(direction, np.array([0, 0, 1]))
    else:
        perp1 = np.cross(direction, np.array([1, 0, 0]))
    perp1 = perp1 / np.linalg.norm(perp1)
    perp2 = np.cross(direction, perp1)

    # Generate base circle points
    angles = np.linspace(0, 2*np.pi, n_segments, endpoint=False)
    base_points = []
    for angle in angles:
        point = base_center + radius * (np.cos(angle) * perp1 + np.sin(angle) * perp2)
        base_points.append(point)
    base_points = np.array(base_points)

    # Apex point
    apex_point = base_center + height * direction

    # Build mesh: apex + base points
    all_points = np.vstack([apex_point, base_points])

    # Triangles: connect apex (index 0) to each pair of adjacent base points
    triangles_i = []
    triangles_j = []
    triangles_k = []
    for i in range(n_segments):
        triangles_i.append(0)  # apex
        triangles_j.append(i + 1)  # base point i
        triangles_k.append((i % n_segments) + 2 if i < n_segments - 1 else 1)  # base point i+1

    mesh = go.Mesh3d(
        x=all_points[:, 0],
        y=all_points[:, 1],
        z=all_points[:, 2],
        i=triangles_i,
        j=triangles_j,
        k=triangles_k,
        color=color,
        opacity=0.9,
        flatshading=True,
        showlegend=False,
    )

    return mesh


def create_spike_visualization(spike_height_scale=0.5, spike_radius=0.08):
    """
    Create 3D spikes at color vertices (R, G, B) showing vacuum energy peaks.

    The vacuum energy ρ_vac spikes dramatically at the color vertices where
    individual pressure functions peak. This visualization shows cones/spikes
    pointing radially outward from the center, with height proportional to
    the vacuum energy at each vertex.

    W vertex and center have zero vacuum energy (no spikes).

    Parameters:
    - spike_height_scale: scaling factor for spike heights
    - spike_radius: base radius of the cone spikes

    Returns a list of Mesh3d traces for the spikes.
    """
    traces = []

    # Color vertices have high vacuum energy
    color_vertices = {
        'R': (VERTICES_PLUS['R'], '#ff4444'),  # Red
        'G': (VERTICES_PLUS['G'], '#44ff44'),  # Green
        'B': (VERTICES_PLUS['B'], '#4444ff'),  # Blue
    }

    # Also add anti-color vertices from T-
    anticolor_vertices = {
        'R_bar': (VERTICES_MINUS['R_bar'], '#ff8888'),  # Light red
        'G_bar': (VERTICES_MINUS['G_bar'], '#88ff88'),  # Light green
        'B_bar': (VERTICES_MINUS['B_bar'], '#8888ff'),  # Light blue
    }

    center = np.array([0.0, 0.0, 0.0])

    # Compute vacuum energy at each vertex to scale spike heights
    for name, (vertex, color) in {**color_vertices, **anticolor_vertices}.items():
        rho = vacuum_energy_from_vev(
            np.array([vertex[0]]),
            np.array([vertex[1]]),
            np.array([vertex[2]])
        )[0]
        log_rho = np.log10(rho + 1e-10)

        # Scale height by log of vacuum energy (normalized)
        # log_rho is around 10 at color vertices
        height = spike_height_scale * max(0.1, (log_rho + 10) / 20)  # Normalize to 0-1 range

        # Direction: radially outward from center
        direction = vertex - center
        direction = direction / np.linalg.norm(direction)

        # Base of cone is at the vertex, spike points outward
        cone = create_cone_mesh(
            apex=vertex + height * direction,
            base_center=vertex,
            height=height,
            radius=spike_radius,
            color=color
        )
        traces.append(cone)

    return traces


def create_visualization(use_slices=True, n_slices=10, use_isosurface=False, use_soap_film=False, use_spikes=False):
    """Create the 3D visualization figure.

    Parameters:
    - use_slices: if True, show multiple slices from RGB toward W
                  if False, show single slice on RGB plane
    - n_slices: number of parallel slices to display
    - use_isosurface: if True, use isosurface visualization instead of slices
    - use_soap_film: if True, use soap-film-like surface on tetrahedra faces
    - use_spikes: if True, show 3D spikes at color vertices representing ρ_vac peaks
    """

    # Create figure
    fig = go.Figure()

    if use_spikes:
        # Use spike visualization at color vertices
        spikes = create_spike_visualization(spike_height_scale=0.6, spike_radius=0.06)
        for spike in spikes:
            fig.add_trace(spike)
    elif use_soap_film:
        # Use soap film visualization on tetrahedra faces
        soap_films = create_soap_film_visualization(resolution=40, opacity=0.85)
        for film in soap_films:
            fig.add_trace(film)
    elif use_isosurface:
        # Use isosurface visualization
        isosurface = create_isosurface_visualization(n_points=50, extent=1.8)
        fig.add_trace(isosurface)
    else:
        # Add vacuum energy density surfaces
        if use_slices:
            # Multiple slices from RGB plane toward W vertex
            surfaces = create_vacuum_energy_slices(n_slices=n_slices, n_points=60, radius=1.6)
            for surface in surfaces:
                fig.add_trace(surface)
        else:
            # Single slice on RGB plane
            surface = create_vacuum_energy_surface_rgb_plane(n_points=80, radius=1.6)
            fig.add_trace(surface)

        # Add vertical slices (xz planes) stacking toward +y and -y (toward B and G)
        vertical_slices = create_vertical_slices(n_slices=10, n_points=60, extent=1.8)
        for v_slice in vertical_slices:
            fig.add_trace(v_slice)

    # Add stella octangula wireframe
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Layout - remove axes and background to prevent clipping
    axis_config = dict(
        showbackground=False,
        showgrid=False,
        showline=False,
        showticklabels=False,
        title='',
        zeroline=False,
        showspikes=False,
    )

    fig.update_layout(
        scene=dict(
            xaxis=axis_config,
            yaxis=axis_config,
            zaxis=axis_config,
            aspectmode='data',  # Use data aspect ratio
            bgcolor='rgba(0,0,0,0)',  # Transparent background
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.8)'
        ),
        margin=dict(l=0, r=0, t=0, b=0),
        paper_bgcolor='white',
        plot_bgcolor='rgba(0,0,0,0)',
    )

    return fig


def export_two_panel_figure():
    """
    Export two static images from different camera angles and combine into a two-panel figure.
    Uses Plotly's kaleido backend for high-quality PNG export.
    """
    import tempfile

    print("Creating figure for export...")
    fig = create_visualization(use_spikes=True)

    # Define camera positions
    # View 1: W vertex toward viewer (eye at roughly elev=25, azim=225)
    camera_view1 = dict(
        eye=dict(x=-1.8, y=-1.8, z=1.5),
        up=dict(x=0, y=0, z=1)
    )

    # View 2: Profile view (eye at roughly elev=-20, azim=-136)
    camera_view2 = dict(
        eye=dict(x=-1.87, y=-1.83, z=-1.38),
        up=dict(x=0, y=0, z=1)
    )

    views = [
        (camera_view1, '(a) W vertex toward viewer'),
        (camera_view2, '(b) Profile view'),
    ]

    panel_images = []
    panel_width = 800
    panel_height = 700

    for i, (camera, title) in enumerate(views):
        # Update camera position
        fig.update_layout(
            scene_camera=camera,
            width=panel_width,
            height=panel_height
        )

        # Export to PNG
        temp_path = tempfile.mktemp(suffix=f'_panel_{i}.png')
        print(f"Exporting {title}...")
        fig.write_image(temp_path, scale=2)  # scale=2 for higher resolution
        panel_images.append(temp_path)

    # Combine into two-panel figure using PIL
    print("Combining panels...")
    img1 = Image.open(panel_images[0])
    img2 = Image.open(panel_images[1])

    # Create combined image with space for titles
    title_height = 60
    combined_width = img1.width + img2.width + 40  # 40px gap
    combined_height = max(img1.height, img2.height) + title_height + 20

    combined = Image.new('RGB', (combined_width, combined_height), 'white')

    # Paste images
    combined.paste(img1, (0, title_height + 10))
    combined.paste(img2, (img1.width + 40, title_height + 10))

    # Add titles
    draw = ImageDraw.Draw(combined)

    # Try to use a nice font, fall back to default
    try:
        subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 28)
    except (IOError, OSError):
        try:
            subtitle_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 28)
        except (IOError, OSError):
            subtitle_font = ImageFont.load_default()

    # Panel titles (no main title - LaTeX caption handles that)
    draw.text((img1.width // 2 - 150, 15), "(a) W vertex toward viewer",
              fill='black', font=subtitle_font)
    draw.text((img1.width + 40 + img2.width // 2 - 100, 15), "(b) Profile view",
              fill='black', font=subtitle_font)

    # Save combined figure as PNG
    png_path = output_dir / 'fig_thm_5_1_2_vacuum_energy.png'
    combined.save(str(png_path), dpi=(300, 300))
    print(f"Saved PNG to {png_path}")

    # Convert to PDF for LaTeX
    pdf_path = output_dir / 'fig_thm_5_1_2_vacuum_energy.pdf'
    # Use RGB mode for PDF
    combined_rgb = combined.convert('RGB')
    combined_rgb.save(str(pdf_path), 'PDF', resolution=300)
    print(f"Saved PDF to {pdf_path}")

    # Clean up temp files
    import os
    for path in panel_images:
        os.remove(path)

    return png_path, pdf_path


def export_interactive_html():
    """Export interactive HTML visualization."""
    print("Creating interactive HTML with SPIKE visualization...")
    fig = create_visualization(use_spikes=True)
    print(f"  -> Figure has {len(fig.data)} traces")

    # Set a good default camera
    fig.update_layout(
        scene_camera=dict(
            eye=dict(x=-1.8, y=-1.8, z=1.5),
            up=dict(x=0, y=0, z=1)
        ),
        width=900,
        height=700,
        title="Theorem 5.1.2: Vacuum Energy Density on Stella Octangula"
    )

    html_path = output_dir / 'fig_thm_5_1_2_vacuum_energy.html'
    fig.write_html(str(html_path))
    print(f"Saved HTML to {html_path}")
    return html_path


def main():
    """Main entry point."""
    print("=" * 70)
    print("Theorem 5.1.2: Vacuum Energy Density Visualization")
    print("=" * 70)

    html_path = export_interactive_html()
    png_path, pdf_path = export_two_panel_figure()

    print("\nDone!")
    print(f"HTML: {html_path}")
    print(f"PNG: {png_path}")
    print(f"PDF: {pdf_path}")


if __name__ == "__main__":
    main()
