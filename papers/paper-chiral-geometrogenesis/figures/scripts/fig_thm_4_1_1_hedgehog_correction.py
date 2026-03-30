#!/usr/bin/env python3
"""
Figure: Tetrahedral Hedgehog Correction (Theorem 4.1.1)

Static paper figure showing the pure hedgehog (gray cones, n̂ = r̂) overlaid
with the corrected hedgehog (colored cones, n̂_corr) on the stella octangula.
The correction arises from the tangential gradient of |χ_total|, tilting the
isospin direction toward R, G, B vertices with ℓ=3 harmonic character.

Key physics:
- Pure hedgehog n̂ = r̂ is the global energy minimum (Theorem 4.1.1)
- Anisotropic pressure induces tangential correction δn̂ ⊥ r̂
- Correction vanishes at field extrema (vertices), largest between them

Proof Document: docs/proofs/Phase4/Theorem-4.1.1-Existence-of-Solitons.md
Paper Section: Section 3.4 (Topological Solitons)

Output: fig_thm_4_1_1_hedgehog_correction.pdf, .png
"""

import numpy as np
import plotly.graph_objects as go

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05          # Regularization for pressure function
A0 = 1.0                # Field amplitude
EPSILON_CORRECTION = 0.5   # Hedgehog correction strength (gives ~27° max tilt)
N_THETA_CONE = 8         # Cone grid density in theta
N_PHI_CONE = 12          # Cone grid density in phi
CONE_RADIUS = 0.55       # Sphere radius for cone placement
CONE_LENGTH = 0.25       # Cone vector magnitude (larger = easier to see tilt)
FD_DELTA = 1e-3         # Finite-difference step size
SCALE = 2.0             # Stella scale factor

# Color field phases
EXP_PHASES = {
    'R': np.exp(1j * 0.0),
    'G': np.exp(1j * 2 * np.pi / 3),
    'B': np.exp(1j * 4 * np.pi / 3),
}

T_PLUS_LABELS = ['R', 'G', 'B', 'W']
T_MINUS_LABELS = ['\u0052\u0304', '\u0047\u0304', '\u0042\u0304', '\u0057\u0304']

EDGES = [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]


# =============================================================================
# GEOMETRY (reused from visualize_modulated_hedgehog.py)
# =============================================================================

def create_tetrahedron_vertices(scale=1.0):
    """Create vertices of T₊ tetrahedron per Definition 0.1.1."""
    vertices = np.array([
        [1, 1, 1],      # R
        [1, -1, -1],    # G
        [-1, 1, -1],    # B
        [-1, -1, 1]     # W
    ]) * scale / np.sqrt(3)
    return vertices


def compute_view_rotation():
    """Rotation matrix: W → +z (toward camera), R → top (+y on screen)."""
    w_dir = np.array([-1, -1, 1]) / np.sqrt(3)
    z = np.array([0.0, 0.0, 1.0])

    v = np.cross(w_dir, z)
    s = np.linalg.norm(v)
    c = np.dot(w_dir, z)
    vx = np.array([[0, -v[2], v[1]],
                    [v[2], 0, -v[0]],
                    [-v[1], v[0], 0]])
    R1 = np.eye(3) + vx + vx @ vx * (1 - c) / (s * s)

    r_dir = np.array([1, 1, 1]) / np.sqrt(3)
    r_rot = R1 @ r_dir
    angle = np.arctan2(r_rot[0], r_rot[1])
    ca, sa = np.cos(angle), np.sin(angle)
    R2 = np.array([[ca, -sa, 0],
                    [sa,  ca, 0],
                    [0,    0, 1]])
    return R2 @ R1


def pressure_function(x, y, z, vertex, epsilon=EPSILON):
    """Pressure function P_c(x) = 1/(|x - x_c|² + ε²)."""
    dist_sq = (x - vertex[0])**2 + (y - vertex[1])**2 + (z - vertex[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def profile_function(r, r0=0.6):
    """Skyrmion profile f(r): f(0) = π, f(∞) = 0."""
    r_safe = np.maximum(r, 1e-10)
    return 2 * np.arctan(r0 / r_safe)


# =============================================================================
# VECTORIZED FIELD COMPUTATION
# =============================================================================

def total_chiral_field_magnitude_vectorized(theta, phi, radius, vertices):
    """Compute |χ_total| on a grid of (theta, phi) at given radius.

    Parameters
    ----------
    theta, phi : ndarray
        Angular coordinates (can be any shape).
    radius : float
        Radial distance from origin.
    vertices : ndarray, shape (4, 3)
        T₊ vertex positions (R, G, B, W).

    Returns
    -------
    mag : ndarray
        |χ_total| at each (theta, phi), same shape as input.
    """
    x = radius * np.sin(theta) * np.cos(phi)
    y = radius * np.sin(theta) * np.sin(phi)
    z = radius * np.cos(theta)

    total = np.zeros_like(x, dtype=complex)
    for i, c in enumerate(['R', 'G', 'B']):
        vx, vy, vz = vertices[i]
        dist_sq = (x - vx)**2 + (y - vy)**2 + (z - vz)**2
        P_c = 1.0 / (dist_sq + EPSILON**2)
        total += A0 * P_c * EXP_PHASES[c]

    return np.abs(total)


def compute_tangential_gradient(theta_grid, phi_grid, radius, vertices):
    """Compute tangential gradient of |χ_total| via finite differences.

    Returns Cartesian components (δnx, δny, δnz) and magnitude |δn|.
    The gradient is guaranteed tangent to the sphere by construction:
      ∇_tang = (∂|χ|/∂θ) ê_θ + (1/sinθ)(∂|χ|/∂φ) ê_φ
    """
    delta = FD_DELTA

    # Central differences for ∂|χ|/∂θ
    mag_tp = total_chiral_field_magnitude_vectorized(
        theta_grid + delta, phi_grid, radius, vertices)
    mag_tm = total_chiral_field_magnitude_vectorized(
        theta_grid - delta, phi_grid, radius, vertices)
    d_dtheta = (mag_tp - mag_tm) / (2 * delta)

    # Central differences for ∂|χ|/∂φ
    mag_pp = total_chiral_field_magnitude_vectorized(
        theta_grid, phi_grid + delta, radius, vertices)
    mag_pm = total_chiral_field_magnitude_vectorized(
        theta_grid, phi_grid - delta, radius, vertices)
    d_dphi = (mag_pp - mag_pm) / (2 * delta)

    # Spherical basis vectors in Cartesian coordinates
    # ê_θ = (cosθ cosφ, cosθ sinφ, -sinθ)
    # ê_φ = (-sinφ, cosφ, 0)
    cos_t = np.cos(theta_grid)
    sin_t = np.sin(theta_grid)
    cos_p = np.cos(phi_grid)
    sin_p = np.sin(phi_grid)

    e_theta_x = cos_t * cos_p
    e_theta_y = cos_t * sin_p
    e_theta_z = -sin_t

    e_phi_x = -sin_p
    e_phi_y = cos_p
    e_phi_z = np.zeros_like(phi_grid)

    # Tangential gradient: ∂|χ|/∂θ · ê_θ + (1/sinθ) ∂|χ|/∂φ · ê_φ
    # Guard against sinθ = 0 at poles
    sin_t_safe = np.where(np.abs(sin_t) < 1e-8, 1e-8, sin_t)
    phi_coeff = d_dphi / sin_t_safe

    dnx = d_dtheta * e_theta_x + phi_coeff * e_phi_x
    dny = d_dtheta * e_theta_y + phi_coeff * e_phi_y
    dnz = d_dtheta * e_theta_z + phi_coeff * e_phi_z

    dn_mag = np.sqrt(dnx**2 + dny**2 + dnz**2)

    return dnx, dny, dnz, dn_mag


def compute_corrected_hedgehog(theta_grid, phi_grid, radius, vertices, epsilon):
    """Compute both pure and corrected hedgehog vectors.

    Returns
    -------
    pure_vecs : tuple (ux, uy, uz)
        Pure radial hedgehog r̂ components.
    corr_vecs : tuple (cx, cy, cz)
        Corrected hedgehog n̂_corr components.
    dn_mag : ndarray
        Magnitude of the correction |δn̂|.
    """
    # Pure radial direction
    sin_t = np.sin(theta_grid)
    cos_t = np.cos(theta_grid)
    cos_p = np.cos(phi_grid)
    sin_p = np.sin(phi_grid)

    rx = sin_t * cos_p
    ry = sin_t * sin_p
    rz = cos_t

    # Tangential gradient
    dnx, dny, dnz, dn_mag = compute_tangential_gradient(
        theta_grid, phi_grid, radius, vertices)

    # Normalize gradient for correction
    dn_max = np.max(dn_mag) if np.max(dn_mag) > 0 else 1.0
    dnx_norm = dnx / dn_max
    dny_norm = dny / dn_max
    dnz_norm = dnz / dn_max

    # Corrected: n̂_corr = normalize(r̂ + ε · δn̂)
    cx = rx + epsilon * dnx_norm
    cy = ry + epsilon * dny_norm
    cz = rz + epsilon * dnz_norm
    c_mag = np.sqrt(cx**2 + cy**2 + cz**2)
    c_mag_safe = np.where(c_mag < 1e-10, 1e-10, c_mag)
    cx /= c_mag_safe
    cy /= c_mag_safe
    cz /= c_mag_safe

    # Also normalize dn_mag for coloring (0 to 1)
    dn_mag_norm = dn_mag / dn_max if dn_max > 0 else np.zeros_like(dn_mag)

    return (rx, ry, rz), (cx, cy, cz), dn_mag_norm


# =============================================================================
# REUSABLE TRACE BUILDERS
# =============================================================================

def add_stella_wireframe(traces, t_plus, t_minus, prefix, visible=True):
    """Add stella octangula wireframe traces."""
    vertex_colors_plus = ['red', 'green', 'blue', 'white']
    vertex_colors_minus = ['darkred', 'darkgreen', 'darkblue', 'gray']

    for idx, edge in enumerate(EDGES):
        v = t_plus[edge]
        traces.append(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='royalblue', width=6),
            legendgroup=f'{prefix}_T+', name='T₊ tetrahedron',
            showlegend=(idx == 0), hoverinfo='skip', visible=visible,
        ))

    for idx, edge in enumerate(EDGES):
        v = t_minus[edge]
        traces.append(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='salmon', width=2),
            legendgroup=f'{prefix}_T-', name='T₋ tetrahedron',
            showlegend=(idx == 0), hoverinfo='skip', visible=visible,
        ))

    for i, (label, color) in enumerate(zip(T_PLUS_LABELS, vertex_colors_plus)):
        traces.append(go.Scatter3d(
            x=[t_plus[i, 0]], y=[t_plus[i, 1]], z=[t_plus[i, 2]],
            mode='markers+text',
            marker=dict(size=12, color=color, line=dict(color='black', width=2)),
            text=[label], textposition='top center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            showlegend=False, visible=visible,
            hovertemplate=f'T₊: {label}<extra></extra>',
        ))

    for i, (label, color) in enumerate(zip(T_MINUS_LABELS, vertex_colors_minus)):
        traces.append(go.Scatter3d(
            x=[t_minus[i, 0]], y=[t_minus[i, 1]], z=[t_minus[i, 2]],
            mode='markers+text',
            marker=dict(size=12, color=color, line=dict(color='black', width=2)),
            text=[label], textposition='bottom center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            showlegend=False, visible=visible,
            hovertemplate=f'T₋: {label}<extra></extra>',
        ))


def add_central_octahedron(traces, rot, scale, prefix, visible=True):
    """Add central octahedron wireframe (Prop 0.0.39d)."""
    s = scale / np.sqrt(3)
    oct_verts_orig = np.array([
        [s, 0, 0], [-s, 0, 0],
        [0, s, 0], [0, -s, 0],
        [0, 0, s], [0, 0, -s],
    ])
    oct_verts = (rot @ oct_verts_orig.T).T

    oct_edges = [
        [0, 2], [0, 3], [0, 4], [0, 5],
        [1, 2], [1, 3], [1, 4], [1, 5],
        [2, 4], [2, 5], [3, 4], [3, 5],
    ]

    for idx, edge in enumerate(oct_edges):
        v = oct_verts[edge]
        traces.append(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='gray', width=3, dash='dot'),
            legendgroup=f'{prefix}_oct', name='Central octahedron (T₊∩T₋)',
            showlegend=(idx == 0), hoverinfo='skip', visible=visible,
        ))


def add_baryon_center(traces, prefix, visible=True):
    """Add baryon center marker at origin."""
    traces.append(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=15, color='red', symbol='diamond',
                    line=dict(color='darkred', width=2)),
        name='Baryon center (Q=1)',
        legendgroup=f'{prefix}_baryon', visible=visible,
    ))


def make_cone_grid(t_plus, rot):
    """Generate cone positions on the modulated sphere.

    Returns arrays of (theta, phi, positions) for the cone grid.
    """
    w_axis = rot @ (np.array([-1, -1, 1]) / np.sqrt(3))
    e1 = rot @ (np.array([1, -1, 0]) / np.sqrt(2))
    e2 = np.cross(w_axis, e1)

    thetas = []
    phis = []
    positions = []

    for i in range(N_THETA_CONE):
        theta = np.pi * (i + 0.5) / N_THETA_CONE
        for j in range(N_PHI_CONE):
            phi = 2 * np.pi * j / N_PHI_CONE

            pos = CONE_RADIUS * (np.sin(theta) * np.cos(phi) * e1 +
                                 np.sin(theta) * np.sin(phi) * e2 +
                                 np.cos(theta) * w_axis)

            # Modulate position by field magnitude
            mag = total_chiral_field_magnitude_vectorized(
                np.array([theta]), np.array([phi]), CONE_RADIUS, t_plus)
            mag_val = mag[0]
            mag_norm = min(mag_val / 500, 1.0)
            r_actual = CONE_RADIUS * (1 + 0.4 * (mag_norm - 0.5))
            pos_mod = pos * (r_actual / CONE_RADIUS)

            # Recover angular coordinates for this position (in standard frame)
            r_norm = np.linalg.norm(pos_mod)
            theta_std = np.arccos(np.clip(pos_mod[2] / r_norm, -1, 1))
            phi_std = np.arctan2(pos_mod[1], pos_mod[0])

            thetas.append(theta_std)
            phis.append(phi_std)
            positions.append(pos_mod)

    return np.array(thetas), np.array(phis), np.array(positions)


# =============================================================================
# SCENE BUILDERS
# =============================================================================

def build_scene_1(t_plus, t_minus, rot):
    """Scene 1: Pure Hedgehog — baseline n̂ = r̂ with modulated shell."""
    traces = []

    add_stella_wireframe(traces, t_plus, t_minus, 's1', visible=True)
    add_central_octahedron(traces, rot, SCALE, 's1', visible=True)

    # Modulated shell
    n_theta_shell, n_phi_shell = 35, 50
    theta = np.linspace(0, np.pi, n_theta_shell)
    phi = np.linspace(0, 2 * np.pi, n_phi_shell)
    THETA, PHI = np.meshgrid(theta, phi)

    base_radius = 0.50
    mags = total_chiral_field_magnitude_vectorized(THETA, PHI, base_radius, t_plus)
    mag_min, mag_max = mags.min(), mags.max()
    mags_norm = (mags - mag_min) / (mag_max - mag_min) if mag_max > mag_min else np.ones_like(mags) * 0.5

    mod_strength = 0.5
    r_mod = base_radius * (1 + mod_strength * (mags_norm - 0.5))
    X = r_mod * np.sin(THETA) * np.cos(PHI)
    Y = r_mod * np.sin(THETA) * np.sin(PHI)
    Z = r_mod * np.cos(THETA)

    traces.append(go.Surface(
        x=X, y=Y, z=Z,
        surfacecolor=mags_norm,
        colorscale='RdYlBu_r', cmin=0, cmax=1,
        opacity=0.3, showscale=False,
        name='Modulated shell (|χ_total|)',
        hovertemplate='|χ| modulation<extra></extra>',
        visible=True,
    ))

    # Pure hedgehog cones
    theta_arr, phi_arr, pos_arr = make_cone_grid(t_plus, rot)
    all_x, all_y, all_z = [], [], []
    all_u, all_v, all_w = [], [], []
    all_colors = []

    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        r_norm = np.linalg.norm(pos)
        r_hat = pos / r_norm
        f_r = profile_function(r_norm)
        vec = CONE_LENGTH * r_hat

        all_x.append(pos[0])
        all_y.append(pos[1])
        all_z.append(pos[2])
        all_u.append(vec[0])
        all_v.append(vec[1])
        all_w.append(vec[2])
        all_colors.append(f_r / np.pi)

    traces.append(go.Cone(
        x=all_x, y=all_y, z=all_z,
        u=all_u, v=all_v, w=all_w,
        colorscale='RdYlBu_r', cmin=0, cmax=1,
        sizemode='absolute', sizeref=CONE_LENGTH,
        anchor='tail', showscale=True,
        colorbar=dict(
            title=dict(text='f(r)/π', font=dict(size=12)),
            tickvals=[0, 0.5, 1],
            ticktext=['0', 'π/2', 'π'],
            len=0.4, y=0.8,
        ),
        name='Pure hedgehog (n̂ = r̂)',
        visible=True,
    ))

    add_baryon_center(traces, 's1', visible=True)

    return traces


def build_scene_2(t_plus, t_minus, rot):
    """Scene 2: Pressure Landscape — |χ_total| heatmap + gradient arrows."""
    traces = []

    add_stella_wireframe(traces, t_plus, t_minus, 's2', visible=False)

    # Sphere colored by |χ_total|
    n_theta_sphere, n_phi_sphere = 50, 70
    theta = np.linspace(0, np.pi, n_theta_sphere)
    phi = np.linspace(0, 2 * np.pi, n_phi_sphere)
    THETA, PHI = np.meshgrid(theta, phi)

    radius = 0.55
    mags = total_chiral_field_magnitude_vectorized(THETA, PHI, radius, t_plus)
    mag_min, mag_max = mags.min(), mags.max()
    mags_norm = (mags - mag_min) / (mag_max - mag_min) if mag_max > mag_min else np.ones_like(mags) * 0.5

    X = radius * np.sin(THETA) * np.cos(PHI)
    Y = radius * np.sin(THETA) * np.sin(PHI)
    Z = radius * np.cos(THETA)

    traces.append(go.Surface(
        x=X, y=Y, z=Z,
        surfacecolor=mags_norm,
        colorscale='Hot', cmin=0, cmax=1,
        opacity=0.6, showscale=True,
        colorbar=dict(
            title=dict(text='|χ_total|', font=dict(size=12)),
            len=0.4, y=0.8,
        ),
        name='|χ_total| heatmap',
        visible=False,
    ))

    # Tangential gradient arrows (sparser grid)
    n_t_arrow, n_p_arrow = 8, 12
    theta_arr = np.array([np.pi * (i + 0.5) / n_t_arrow for i in range(n_t_arrow)])
    phi_arr = np.array([2 * np.pi * j / n_p_arrow for j in range(n_p_arrow)])
    THETA_A, PHI_A = np.meshgrid(theta_arr, phi_arr)
    theta_flat = THETA_A.flatten()
    phi_flat = PHI_A.flatten()

    dnx, dny, dnz, dn_mag = compute_tangential_gradient(
        theta_flat, phi_flat, radius, t_plus)

    # Normalize for display
    dn_max = np.max(dn_mag) if np.max(dn_mag) > 0 else 1.0
    arrow_scale = 0.08

    ax, ay, az = [], [], []
    au, av, aw = [], [], []
    a_colors = []

    for k in range(len(theta_flat)):
        if dn_mag[k] / dn_max < 0.05:
            continue  # Skip near-zero gradients
        x = radius * np.sin(theta_flat[k]) * np.cos(phi_flat[k])
        y = radius * np.sin(theta_flat[k]) * np.sin(phi_flat[k])
        z = radius * np.cos(theta_flat[k])

        norm_k = dn_mag[k] / dn_max
        ax.append(x)
        ay.append(y)
        az.append(z)
        au.append(arrow_scale * dnx[k] / dn_max)
        av.append(arrow_scale * dny[k] / dn_max)
        aw.append(arrow_scale * dnz[k] / dn_max)
        a_colors.append(norm_k)

    traces.append(go.Cone(
        x=ax, y=ay, z=az,
        u=au, v=av, w=aw,
        colorscale='Viridis', cmin=0, cmax=1,
        sizemode='absolute', sizeref=0.06,
        anchor='tail', showscale=False,
        name='∇_tang |χ_total|',
        visible=False,
    ))

    # Dummy legend entry for gradient arrows
    traces.append(go.Scatter3d(
        x=[None], y=[None], z=[None],
        mode='markers',
        marker=dict(size=8, color='limegreen', symbol='diamond'),
        name='Tangential gradient ∇|χ|',
        showlegend=True, visible=False,
    ))

    return traces


def build_scene_3(t_plus, t_minus, rot):
    """Scene 3: Correction Vectors — faint r̂ vs bold corrected n̂."""
    traces = []

    # Stella wireframe for spatial context (which vertices the cones tilt toward)
    add_stella_wireframe(traces, t_plus, t_minus, 's3', visible=False)

    # Compute cone grid
    theta_arr, phi_arr, pos_arr = make_cone_grid(t_plus, rot)

    # Compute corrected hedgehog
    pure_vecs, corr_vecs, dn_mag_norm = compute_corrected_hedgehog(
        theta_arr, phi_arr, CONE_RADIUS, t_plus, EPSILON_CORRECTION)

    # Faint gray cones: pure r̂ (made 40% longer so they visibly poke past corrected)
    gray_length = CONE_LENGTH * 1.4
    px, py, pz = [], [], []
    pu, pv, pw = [], [], []
    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        r_hat = pos / np.linalg.norm(pos)
        vec = gray_length * r_hat

        px.append(pos[0])
        py.append(pos[1])
        pz.append(pos[2])
        pu.append(vec[0])
        pv.append(vec[1])
        pw.append(vec[2])

    traces.append(go.Cone(
        x=px, y=py, z=pz,
        u=pu, v=pv, w=pw,
        colorscale=[[0, 'rgba(180,180,180,0.5)'], [1, 'rgba(180,180,180,0.5)']],
        sizemode='absolute', sizeref=gray_length,
        anchor='tail', showscale=False,
        name='Pure r̂ (baseline)',
        opacity=0.5, visible=False,
    ))

    # Bold colored cones: corrected n̂ (color = |δn̂| magnitude)
    cx_list, cy_list, cz_list = [], [], []
    cu, cv, cw = [], [], []
    c_colors = []

    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        cvec = np.array([corr_vecs[0][k], corr_vecs[1][k], corr_vecs[2][k]])
        vec = CONE_LENGTH * cvec

        cx_list.append(pos[0])
        cy_list.append(pos[1])
        cz_list.append(pos[2])
        cu.append(vec[0])
        cv.append(vec[1])
        cw.append(vec[2])
        c_colors.append(dn_mag_norm[k])

    traces.append(go.Cone(
        x=cx_list, y=cy_list, z=cz_list,
        u=cu, v=cv, w=cw,
        colorscale='Plasma', cmin=0, cmax=1,
        sizemode='absolute', sizeref=CONE_LENGTH,
        anchor='tail', showscale=True,
        colorbar=dict(
            title=dict(text='|δn̂|', font=dict(size=12)),
            len=0.4, y=0.8,
        ),
        name='Corrected n̂ (color = |δn̂|)',
        visible=False,
    ))

    # Dummy legend entries
    traces.append(go.Scatter3d(
        x=[None], y=[None], z=[None],
        mode='markers',
        marker=dict(size=8, color='gray', symbol='circle'),
        name='Faint: pure r̂ (baseline)',
        showlegend=True, visible=False,
    ))
    traces.append(go.Scatter3d(
        x=[None], y=[None], z=[None],
        mode='markers',
        marker=dict(size=8, color='darkorchid', symbol='diamond'),
        name='Bold: corrected n̂_corr',
        showlegend=True, visible=False,
    ))

    return traces


def build_scene_4(t_plus, t_minus, rot):
    """Scene 4: Full Corrected Hedgehog — combined picture."""
    traces = []

    add_stella_wireframe(traces, t_plus, t_minus, 's4', visible=False)
    add_central_octahedron(traces, rot, SCALE, 's4', visible=False)

    # Shell colored by correction magnitude
    n_theta_shell, n_phi_shell = 35, 50
    theta = np.linspace(0, np.pi, n_theta_shell)
    phi = np.linspace(0, 2 * np.pi, n_phi_shell)
    THETA, PHI = np.meshgrid(theta, phi)

    base_radius = 0.50
    mags = total_chiral_field_magnitude_vectorized(THETA, PHI, base_radius, t_plus)
    mag_min, mag_max = mags.min(), mags.max()
    mags_norm = (mags - mag_min) / (mag_max - mag_min) if mag_max > mag_min else np.ones_like(mags) * 0.5

    # Compute correction magnitude on the shell grid
    _, _, _, dn_mag_shell = compute_tangential_gradient(THETA, PHI, base_radius, t_plus)
    dn_max_shell = np.max(dn_mag_shell) if np.max(dn_mag_shell) > 0 else 1.0
    dn_shell_norm = dn_mag_shell / dn_max_shell

    mod_strength = 0.5
    r_mod = base_radius * (1 + mod_strength * (mags_norm - 0.5))
    X = r_mod * np.sin(THETA) * np.cos(PHI)
    Y = r_mod * np.sin(THETA) * np.sin(PHI)
    Z = r_mod * np.cos(THETA)

    traces.append(go.Surface(
        x=X, y=Y, z=Z,
        surfacecolor=dn_shell_norm,
        colorscale='Plasma', cmin=0, cmax=1,
        opacity=0.25, showscale=False,
        name='Shell (color = correction |δn̂|)',
        visible=False,
    ))

    # Corrected hedgehog cones
    theta_arr, phi_arr, pos_arr = make_cone_grid(t_plus, rot)
    pure_vecs, corr_vecs, dn_mag_norm = compute_corrected_hedgehog(
        theta_arr, phi_arr, CONE_RADIUS, t_plus, EPSILON_CORRECTION)

    cx_list, cy_list, cz_list = [], [], []
    cu, cv, cw = [], [], []
    c_colors = []

    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        cvec = np.array([corr_vecs[0][k], corr_vecs[1][k], corr_vecs[2][k]])
        vec = CONE_LENGTH * cvec

        cx_list.append(pos[0])
        cy_list.append(pos[1])
        cz_list.append(pos[2])
        cu.append(vec[0])
        cv.append(vec[1])
        cw.append(vec[2])
        c_colors.append(dn_mag_norm[k])

    traces.append(go.Cone(
        x=cx_list, y=cy_list, z=cz_list,
        u=cu, v=cv, w=cw,
        colorscale='Plasma', cmin=0, cmax=1,
        sizemode='absolute', sizeref=CONE_LENGTH,
        anchor='tail', showscale=True,
        colorbar=dict(
            title=dict(text='|δn̂|', font=dict(size=12)),
            len=0.4, y=0.8,
        ),
        name='Corrected hedgehog n̂_corr',
        visible=False,
    ))

    add_baryon_center(traces, 's4', visible=False)

    return traces


# =============================================================================
# VERIFICATION CHECKS
# =============================================================================

def run_verification(t_plus, rot):
    """Run tangentiality and symmetry checks, print results."""
    print("=" * 60)
    print("VERIFICATION CHECKS")
    print("=" * 60)

    theta_arr, phi_arr, pos_arr = make_cone_grid(t_plus, rot)

    # 1. Tangentiality: δn̂ · r̂ ≈ 0
    dnx, dny, dnz, dn_mag = compute_tangential_gradient(
        theta_arr, phi_arr, CONE_RADIUS, t_plus)

    dots = []
    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        r_hat = pos / np.linalg.norm(pos)
        dn_vec = np.array([dnx[k], dny[k], dnz[k]])
        if np.linalg.norm(dn_vec) > 1e-12:
            dot = abs(np.dot(dn_vec, r_hat)) / np.linalg.norm(dn_vec)
            dots.append(dot)

    max_dot = max(dots) if dots else 0
    mean_dot = np.mean(dots) if dots else 0
    print(f"\n1. Tangentiality check (δn̂ · r̂ ≈ 0):")
    print(f"   max |δn̂ · r̂| / |δn̂| = {max_dot:.6f}")
    print(f"   mean                   = {mean_dot:.6f}")
    print(f"   PASS: {'YES' if max_dot < 0.01 else 'NO'}")

    # 2. Gradient-field anticorrelation: |∇|χ|| should be small where |χ|
    # is extremal (maxima at vertices, minima at W) and large at inflection
    # points. We check this on a fine grid, not the sparse cone grid.
    n_fine = 50
    theta_fine = np.linspace(0.1, np.pi - 0.1, n_fine)
    phi_fine = np.linspace(0, 2 * np.pi, 2 * n_fine)
    TH_F, PH_F = np.meshgrid(theta_fine, phi_fine)
    th_flat, ph_flat = TH_F.flatten(), PH_F.flatten()

    field_vals = total_chiral_field_magnitude_vectorized(
        th_flat, ph_flat, CONE_RADIUS, t_plus)
    _, _, _, grad_mag = compute_tangential_gradient(
        th_flat, ph_flat, CONE_RADIUS, t_plus)

    f_min, f_max = field_vals.min(), field_vals.max()
    f_norm = (field_vals - f_min) / (f_max - f_min) if f_max > f_min else np.zeros_like(field_vals)
    g_max = grad_mag.max() if grad_mag.max() > 0 else 1.0
    g_norm = grad_mag / g_max

    # Points near field extrema (top 20% and bottom 20%)
    extremal_mask = (f_norm > 0.8) | (f_norm < 0.2)
    mid_mask = (f_norm > 0.35) & (f_norm < 0.65)
    mean_grad_extremal = np.mean(g_norm[extremal_mask]) if np.any(extremal_mask) else 0
    mean_grad_mid = np.mean(g_norm[mid_mask]) if np.any(mid_mask) else 0

    print(f"\n2. Gradient-field anticorrelation (|∇|χ|| small at extrema):")
    print(f"   Points at field extrema (top/bottom 20%):  {np.sum(extremal_mask)}")
    print(f"   Points at field midrange (35-65%):         {np.sum(mid_mask)}")
    print(f"   Mean |∇|χ|| at extrema:  {mean_grad_extremal:.4f}")
    print(f"   Mean |∇|χ|| at midrange: {mean_grad_mid:.4f}")
    if mean_grad_extremal > 0:
        print(f"   Ratio (midrange/extrema): {mean_grad_mid/mean_grad_extremal:.2f}")
    pass_2 = mean_grad_mid > mean_grad_extremal
    print(f"   PASS (gradient larger at midrange): {'YES' if pass_2 else 'NO'}")

    # 3. T_d symmetry check: correction magnitude should be similar for
    # points related by R↔G↔B permutation
    # Sample a specific direction and its permutations
    test_theta = np.pi / 3
    test_phi = np.pi / 4
    mag_base = total_chiral_field_magnitude_vectorized(
        np.array([test_theta]), np.array([test_phi]), CONE_RADIUS, t_plus)[0]
    # Check at 3 equally-spaced phi rotations (approximate T_d test)
    mags_td = []
    for dp in [0, 2*np.pi/3, 4*np.pi/3]:
        m = total_chiral_field_magnitude_vectorized(
            np.array([test_theta]), np.array([test_phi + dp]), CONE_RADIUS, t_plus)[0]
        mags_td.append(m)
    spread = (max(mags_td) - min(mags_td)) / np.mean(mags_td) if np.mean(mags_td) > 0 else 0
    print(f"\n3. Approximate T_d symmetry:")
    print(f"   |χ| at 120° rotations: {[f'{m:.2f}' for m in mags_td]}")
    print(f"   Relative spread: {spread:.4f}")
    print(f"   PASS (spread < 0.3): {'YES' if spread < 0.3 else 'NO (expected — T_d is not just φ-rotation)'}")

    print("\n" + "=" * 60)


# =============================================================================
# MAIN — Static paper figure (Scene 3: correction vectors + stella)
# =============================================================================

import os

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/


def build_paper_figure(t_plus, t_minus, rot):
    """Combined scene for paper: stella + shell + both cone sets."""
    traces = []

    # Stella wireframe + vertex labels
    add_stella_wireframe(traces, t_plus, t_minus, 'paper', visible=True)

    # Central octahedron
    add_central_octahedron(traces, rot, SCALE, 'paper', visible=True)

    # Modulated shell (from Scene 1 / Scene 4)
    n_theta_shell, n_phi_shell = 35, 50
    theta = np.linspace(0, np.pi, n_theta_shell)
    phi = np.linspace(0, 2 * np.pi, n_phi_shell)
    THETA, PHI = np.meshgrid(theta, phi)

    base_radius = 0.50
    mags = total_chiral_field_magnitude_vectorized(THETA, PHI, base_radius, t_plus)
    mag_min, mag_max = mags.min(), mags.max()
    mags_norm = (mags - mag_min) / (mag_max - mag_min) if mag_max > mag_min else np.ones_like(mags) * 0.5

    mod_strength = 0.5
    r_mod = base_radius * (1 + mod_strength * (mags_norm - 0.5))
    X = r_mod * np.sin(THETA) * np.cos(PHI)
    Y = r_mod * np.sin(THETA) * np.sin(PHI)
    Z = r_mod * np.cos(THETA)

    traces.append(go.Surface(
        x=X, y=Y, z=Z,
        surfacecolor=mags_norm,
        colorscale='RdYlBu_r', cmin=0, cmax=1,
        opacity=0.3, showscale=False,
        name='Modulated shell (|χ_total|)',
        visible=True,
    ))

    # Cone grid
    theta_arr, phi_arr, pos_arr = make_cone_grid(t_plus, rot)
    pure_vecs, corr_vecs, dn_mag_norm = compute_corrected_hedgehog(
        theta_arr, phi_arr, CONE_RADIUS, t_plus, EPSILON_CORRECTION)

    # Gray cones: pure r̂ (40% longer so they poke past corrected)
    gray_length = CONE_LENGTH * 1.4
    px, py, pz, pu, pv, pw = [], [], [], [], [], []
    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        r_hat = pos / np.linalg.norm(pos)
        vec = gray_length * r_hat
        px.append(pos[0]); py.append(pos[1]); pz.append(pos[2])
        pu.append(vec[0]); pv.append(vec[1]); pw.append(vec[2])

    traces.append(go.Cone(
        x=px, y=py, z=pz, u=pu, v=pv, w=pw,
        colorscale=[[0, 'rgba(180,180,180,0.5)'], [1, 'rgba(180,180,180,0.5)']],
        sizemode='absolute', sizeref=gray_length,
        anchor='tail', showscale=False,
        name='Pure r̂ (baseline)',
        opacity=0.5, visible=True,
    ))

    # Colored cones: corrected n̂
    cx_list, cy_list, cz_list, cu, cv, cw = [], [], [], [], [], []
    for k in range(len(theta_arr)):
        pos = pos_arr[k]
        cvec = np.array([corr_vecs[0][k], corr_vecs[1][k], corr_vecs[2][k]])
        vec = CONE_LENGTH * cvec
        cx_list.append(pos[0]); cy_list.append(pos[1]); cz_list.append(pos[2])
        cu.append(vec[0]); cv.append(vec[1]); cw.append(vec[2])

    traces.append(go.Cone(
        x=cx_list, y=cy_list, z=cz_list, u=cu, v=cv, w=cw,
        colorscale='Plasma', cmin=0, cmax=1,
        sizemode='absolute', sizeref=CONE_LENGTH,
        anchor='tail', showscale=True,
        colorbar=dict(
            title=dict(text='|δn̂|', font=dict(size=12), side='right'),
            tickfont=dict(size=10),
            orientation='h',
            len=0.3, thickness=12,
            x=0.7, y=-0.06,
            xanchor='center', yanchor='top',
        ),
        name='Corrected n̂ (color = |δn̂|)',
        visible=True,
    ))

    # Dummy legend entries for cones (Plotly Cone traces don't appear in legend)
    traces.append(go.Scatter3d(
        x=[None], y=[None], z=[None], mode='markers',
        marker=dict(size=10, color='gray', symbol='diamond'),
        name='Pure r̂ (baseline)', showlegend=True, visible=True,
    ))
    traces.append(go.Scatter3d(
        x=[None], y=[None], z=[None], mode='markers',
        marker=dict(size=10, color='darkorchid', symbol='diamond'),
        name='Corrected n̂_corr', showlegend=True, visible=True,
    ))

    # Baryon center
    add_baryon_center(traces, 'paper', visible=True)

    return traces


def main():
    rot = compute_view_rotation()
    t_plus = (rot @ create_tetrahedron_vertices(SCALE).T).T
    t_minus = -t_plus

    traces = build_paper_figure(t_plus, t_minus, rot)
    fig = go.Figure(data=traces)

    fig.update_layout(
        title=dict(
            text=("Tetrahedral Hedgehog Correction: ℓ=3 Harmonic Character"
                  "<br><sup>Anisotropic pressure tilts isospin toward "
                  "R, G, B vertices (Thm 0.2.1 + Thm 4.1.1)</sup>"),
            x=0.5, font=dict(size=18),
        ),
        scene=dict(
            xaxis=dict(title='', range=[-2.3, 2.3], showticklabels=False,
                       showgrid=False, zeroline=False, showbackground=False),
            yaxis=dict(title='', range=[-2.3, 2.3], showticklabels=False,
                       showgrid=False, zeroline=False, showbackground=False),
            zaxis=dict(title='', range=[-2.3, 2.3], showticklabels=False,
                       showgrid=False, zeroline=False, showbackground=False),
            camera=dict(
                eye=dict(x=0, y=0.2, z=1.15),
                up=dict(x=0, y=1, z=0),
                center=dict(x=0, y=-0.02, z=0),
                projection=dict(type='perspective'),
            ),
            aspectmode='cube',
            bgcolor='rgba(255,255,255,1)',
            domain=dict(x=[0, 1.0], y=[0, 1.0]),
        ),
        legend=dict(
            x=0.5, y=-0.02,
            xanchor='center', yanchor='top',
            orientation='h',
            bgcolor='rgba(255,255,255,0.9)',
            bordercolor='gray', borderwidth=1,
            font=dict(size=11),
        ),
        margin=dict(l=0, r=0, t=60, b=80),
        width=700, height=900,
        paper_bgcolor='white',
    )

    # Save to figures/ directory
    pdf_path = os.path.join(OUTPUT_DIR, 'fig_thm_4_1_1_hedgehog_correction.pdf')
    png_path = os.path.join(OUTPUT_DIR, 'fig_thm_4_1_1_hedgehog_correction.png')

    fig.write_image(pdf_path, width=700, height=900)
    print(f"Saved: {pdf_path}")

    fig.write_image(png_path, width=700, height=900, scale=2)
    print(f"Saved: {png_path}")


if __name__ == '__main__':
    main()
