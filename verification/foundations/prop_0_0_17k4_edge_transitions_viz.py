#!/usr/bin/env python3
"""
Interactive 3D Visualization for Proposition 0.0.17k4: Edge Transitions

Visualizes the edge transitions critical to Prop 0.0.17k4:
1. W-face edges where Robin BC applies (vector excitation confinement)
2. Color face-to-face transitions showing phase changes
3. Inter-tetrahedral overlap region where T+ and T- couple
4. Field amplitude decay at boundaries (Robin BC effect)

The key physics: Vector excitations couple to phase gradients. At W-face
edges, the field sees a Robin-type boundary condition (partial confinement)
determined by the inter-tetrahedral coupling strength K.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from scipy.interpolate import RegularGridInterpolator

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

# Z3 phases: 0, 2pi/3, 4pi/3 (120 deg separation)
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

# Stella octangula vertices (two interpenetrating tetrahedra)
# T+ tetrahedron
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),  # White vertex (color singlet)
}

# T- tetrahedron (dual)
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}

# Edge definitions for T+
# Each edge connects two vertices
EDGES_T_PLUS = {
    # Edges FROM W vertex (W-vertex edges)
    'W-R': ('W', 'R'),
    'W-G': ('W', 'G'),
    'W-B': ('W', 'B'),
    # Color face edges (these are the W-face edges from Prop 0.0.17k4)
    'R-G': ('R', 'G'),  # W-face edge
    'G-B': ('G', 'B'),  # W-face edge
    'B-R': ('B', 'R'),  # W-face edge
}

# Face definitions for T+
FACES_T_PLUS = {
    'W-face': ['R', 'G', 'B'],      # Color singlet face (opposite W vertex)
    'R-face': ['W', 'G', 'B'],      # Face opposite R vertex
    'G-face': ['W', 'R', 'B'],      # Face opposite G vertex
    'B-face': ['W', 'R', 'G'],      # Face opposite B vertex
}


# =============================================================================
# FIELD FUNCTIONS
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def individual_field_at_point(point, a0=A0, epsilon=EPSILON):
    """Compute individual color field values at a single point."""
    fields = {}
    for c in ['R', 'G', 'B']:
        dist_sq = np.sum((point - VERTICES_PLUS[c])**2)
        P_c = 1.0 / (dist_sq + epsilon**2)
        fields[c] = a0 * P_c * EXP_PHASES[c]
    return fields


def total_chiral_field_at_point(point, a0=A0, epsilon=EPSILON):
    """Compute total chiral field at a single point."""
    fields = individual_field_at_point(point, a0, epsilon)
    return sum(fields.values())


def compute_field_along_path(points, a0=A0, epsilon=EPSILON):
    """
    Compute field properties along a path (array of points).
    Returns: magnitudes of R, G, B fields, total magnitude, and total phase.
    """
    n = len(points)
    r_mag = np.zeros(n)
    g_mag = np.zeros(n)
    b_mag = np.zeros(n)
    total_mag = np.zeros(n)
    total_phase = np.zeros(n)

    for i, pt in enumerate(points):
        fields = individual_field_at_point(pt, a0, epsilon)
        r_mag[i] = np.abs(fields['R'])
        g_mag[i] = np.abs(fields['G'])
        b_mag[i] = np.abs(fields['B'])
        total = sum(fields.values())
        total_mag[i] = np.abs(total)
        total_phase[i] = np.angle(total)

    return r_mag, g_mag, b_mag, total_mag, total_phase


def compute_phase_color_singlet(point, a0=A0, epsilon=EPSILON):
    """
    Compute how close a point is to being a color singlet.
    Returns 1 when sum of phasors = 0, 0 when far from it.
    """
    fields = individual_field_at_point(point, a0, epsilon)
    phasor_sum = sum(EXP_PHASES[c] for c in ['R', 'G', 'B'])  # Exact zero

    # Compute weighted sum
    total = sum(fields.values())
    max_mag = max(np.abs(fields[c]) for c in ['R', 'G', 'B'])

    # Measure deviation from perfect cancellation
    if max_mag < 1e-10:
        return 1.0

    cancellation = 1.0 - np.abs(total) / (3 * max_mag)
    return max(0, cancellation)


# =============================================================================
# EDGE PATH GENERATION
# =============================================================================

def generate_edge_path(edge_name, n_points=50):
    """Generate points along an edge of T+."""
    v1_name, v2_name = EDGES_T_PLUS[edge_name]
    v1 = VERTICES_PLUS[v1_name]
    v2 = VERTICES_PLUS[v2_name]

    t = np.linspace(0, 1, n_points)
    points = np.array([v1 + ti * (v2 - v1) for ti in t])
    return points, t


def generate_face_to_face_path(start_face, end_face, n_points=50):
    """
    Generate a path from center of one face to center of another.
    This shows the phase transition between color regions.
    """
    # Face centers
    start_center = np.mean([VERTICES_PLUS[v] for v in FACES_T_PLUS[start_face]], axis=0)
    end_center = np.mean([VERTICES_PLUS[v] for v in FACES_T_PLUS[end_face]], axis=0)

    t = np.linspace(0, 1, n_points)
    points = np.array([start_center + ti * (end_center - start_center) for ti in t])
    return points, t


def generate_inter_tetrahedral_path(n_points=50):
    """
    Generate a path through the inter-tetrahedral overlap region.
    This is where T+ and T- surfaces pass near each other.
    """
    # Path from center of T+ to center of T- (both at origin)
    # Go through the overlap region off-center
    center_plus = np.mean([VERTICES_PLUS[v] for v in ['R', 'G', 'B', 'W']], axis=0)
    center_minus = np.mean([VERTICES_MINUS[v] for v in ['R_bar', 'G_bar', 'B_bar', 'W_bar']], axis=0)

    # Midpoint is at origin, offset to pass through overlap
    offset = np.array([0.2, 0.2, 0])

    t = np.linspace(0, 1, n_points)
    mid = 0.5 * (center_plus + center_minus) + offset

    # Create curved path through overlap
    points = []
    for ti in t:
        if ti < 0.5:
            # From T+ center toward overlap midpoint
            pt = center_plus + 2*ti * (mid - center_plus)
        else:
            # From overlap midpoint toward T- center
            pt = mid + 2*(ti - 0.5) * (center_minus - mid)
        points.append(pt)

    return np.array(points), t


# =============================================================================
# VISUALIZATION: EDGE TRANSITION PROFILES
# =============================================================================

def create_edge_transition_figure():
    """
    Create a figure showing field profiles along key edges.
    Shows how fields transition at boundaries.
    """
    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=(
            'W-Face Edge (R-G): Robin BC Region',
            'W-Face Edge (G-B): Robin BC Region',
            'W-Vertex Edge (W-R): Phase Transition',
            'Color Face Path (R-face to G-face)'
        ),
        specs=[[{'type': 'xy'}, {'type': 'xy'}],
               [{'type': 'xy'}, {'type': 'xy'}]]
    )

    # Edge R-G (W-face edge)
    points, t = generate_edge_path('R-G')
    r_mag, g_mag, b_mag, total_mag, total_phase = compute_field_along_path(points)

    # Normalize for visibility
    max_val = max(r_mag.max(), g_mag.max(), b_mag.max())

    fig.add_trace(go.Scatter(x=t, y=r_mag/max_val, name='R field',
                             line=dict(color='red', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=t, y=g_mag/max_val, name='G field',
                             line=dict(color='green', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=t, y=b_mag/max_val, name='B field',
                             line=dict(color='blue', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=t, y=total_mag/max_val, name='|Total|',
                             line=dict(color='black', width=2, dash='dash')), row=1, col=1)

    # Edge G-B (W-face edge)
    points, t = generate_edge_path('G-B')
    r_mag, g_mag, b_mag, total_mag, total_phase = compute_field_along_path(points)
    max_val = max(r_mag.max(), g_mag.max(), b_mag.max())

    fig.add_trace(go.Scatter(x=t, y=r_mag/max_val, showlegend=False,
                             line=dict(color='red', width=2)), row=1, col=2)
    fig.add_trace(go.Scatter(x=t, y=g_mag/max_val, showlegend=False,
                             line=dict(color='green', width=2)), row=1, col=2)
    fig.add_trace(go.Scatter(x=t, y=b_mag/max_val, showlegend=False,
                             line=dict(color='blue', width=2)), row=1, col=2)
    fig.add_trace(go.Scatter(x=t, y=total_mag/max_val, showlegend=False,
                             line=dict(color='black', width=2, dash='dash')), row=1, col=2)

    # Edge W-R (W-vertex edge - shows transition from W vertex)
    points, t = generate_edge_path('W-R')
    r_mag, g_mag, b_mag, total_mag, total_phase = compute_field_along_path(points)
    max_val = max(r_mag.max(), g_mag.max(), b_mag.max())

    fig.add_trace(go.Scatter(x=t, y=r_mag/max_val, showlegend=False,
                             line=dict(color='red', width=2)), row=2, col=1)
    fig.add_trace(go.Scatter(x=t, y=g_mag/max_val, showlegend=False,
                             line=dict(color='green', width=2)), row=2, col=1)
    fig.add_trace(go.Scatter(x=t, y=b_mag/max_val, showlegend=False,
                             line=dict(color='blue', width=2)), row=2, col=1)
    fig.add_trace(go.Scatter(x=t, y=total_phase/np.pi, name='Phase/pi',
                             line=dict(color='purple', width=2, dash='dot')), row=2, col=1)

    # Face-to-face path (R-face to G-face)
    points, t = generate_face_to_face_path('R-face', 'G-face')
    r_mag, g_mag, b_mag, total_mag, total_phase = compute_field_along_path(points)
    max_val = max(r_mag.max(), g_mag.max(), b_mag.max())

    fig.add_trace(go.Scatter(x=t, y=r_mag/max_val, showlegend=False,
                             line=dict(color='red', width=2)), row=2, col=2)
    fig.add_trace(go.Scatter(x=t, y=g_mag/max_val, showlegend=False,
                             line=dict(color='green', width=2)), row=2, col=2)
    fig.add_trace(go.Scatter(x=t, y=b_mag/max_val, showlegend=False,
                             line=dict(color='blue', width=2)), row=2, col=2)
    fig.add_trace(go.Scatter(x=t, y=total_phase/np.pi, showlegend=False,
                             line=dict(color='purple', width=2, dash='dot')), row=2, col=2)

    # Update axes labels
    for row in [1, 2]:
        for col in [1, 2]:
            fig.update_xaxes(title_text='Position along path (0=start, 1=end)', row=row, col=col)
            fig.update_yaxes(title_text='Normalized field / Phase', row=row, col=col)

    fig.update_layout(
        height=700,
        width=1000,
        title=dict(
            text='Prop 0.0.17k4: Edge Transition Profiles<br>'
                 '<sub>Shows how color fields transition along edges - key to Robin BC determination</sub>',
            x=0.5
        ),
        legend=dict(x=1.02, y=1, bgcolor='rgba(255,255,255,0.9)')
    )

    return fig


# =============================================================================
# VISUALIZATION: 3D WITH HIGHLIGHTED EDGES
# =============================================================================

def create_3d_edge_visualization():
    """
    Create interactive 3D visualization highlighting the edge transitions.
    """
    fig = go.Figure()

    # --- Stella wireframe ---
    # T+ tetrahedron edges (thicker for W-face edges)
    for edge_name, (v1_name, v2_name) in EDGES_T_PLUS.items():
        v1 = VERTICES_PLUS[v1_name]
        v2 = VERTICES_PLUS[v2_name]

        # W-face edges are special (Robin BC region)
        is_w_face_edge = 'W' not in edge_name

        if is_w_face_edge:
            # W-face edges: thick, gradient colored
            n_seg = 20
            t = np.linspace(0, 1, n_seg)
            points = [v1 + ti * (v2 - v1) for ti in t]

            # Color gradient based on field mixture
            for i in range(len(points)-1):
                pt = points[i]
                fields = individual_field_at_point(pt)
                r = np.abs(fields['R'])
                g = np.abs(fields['G'])
                b = np.abs(fields['B'])
                total = r + g + b + 1e-10

                color = f'rgb({int(255*r/total)},{int(255*g/total)},{int(255*b/total)})'

                fig.add_trace(go.Scatter3d(
                    x=[points[i][0], points[i+1][0]],
                    y=[points[i][1], points[i+1][1]],
                    z=[points[i][2], points[i+1][2]],
                    mode='lines',
                    line=dict(color=color, width=8),
                    showlegend=False,
                    hoverinfo='text',
                    hovertext=f'{edge_name}: W-face edge (Robin BC)'
                ))
        else:
            # W-vertex edges: thin, blue
            fig.add_trace(go.Scatter3d(
                x=[v1[0], v2[0]],
                y=[v1[1], v2[1]],
                z=[v1[2], v2[2]],
                mode='lines',
                line=dict(color='steelblue', width=3),
                showlegend=False,
                hoverinfo='text',
                hovertext=f'{edge_name}'
            ))

    # T- tetrahedron (semi-transparent)
    t_minus_verts = [VERTICES_MINUS[k] for k in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    edges_minus = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    for i, j in edges_minus:
        fig.add_trace(go.Scatter3d(
            x=[t_minus_verts[i][0], t_minus_verts[j][0]],
            y=[t_minus_verts[i][1], t_minus_verts[j][1]],
            z=[t_minus_verts[i][2], t_minus_verts[j][2]],
            mode='lines',
            line=dict(color='rgba(200, 100, 100, 0.5)', width=2),
            showlegend=False,
            hoverinfo='skip'
        ))

    # --- Vertex markers ---
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'white'}
    for name, v in VERTICES_PLUS.items():
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers+text',
            marker=dict(size=12, color=colors_map[name],
                       line=dict(color='black', width=2)),
            text=[name],
            textposition='top center',
            name=f'{name} vertex',
            hoverinfo='name'
        ))

    # --- W-face (color singlet surface) ---
    w_face_verts = np.array([VERTICES_PLUS['R'], VERTICES_PLUS['G'], VERTICES_PLUS['B']])
    fig.add_trace(go.Mesh3d(
        x=w_face_verts[:, 0],
        y=w_face_verts[:, 1],
        z=w_face_verts[:, 2],
        i=[0], j=[1], k=[2],
        color='rgba(200, 200, 200, 0.3)',
        name='W-face (color singlet)',
        showlegend=True,
        hoverinfo='name'
    ))

    # --- Phase gradient arrows at W-face edges ---
    # Show how phase gradient points ALONG the edges (vector confinement)
    # The gradient points in the direction of INCREASING phase
    for edge_name, (v1_name, v2_name) in EDGES_T_PLUS.items():
        if 'W' in edge_name:  # Skip non-W-face edges
            continue

        v1 = VERTICES_PLUS[v1_name]
        v2 = VERTICES_PLUS[v2_name]
        mid = 0.5 * (v1 + v2)

        # Compute phase gradient at midpoint using numerical differentiation
        delta = 0.02
        edge_dir = (v2 - v1) / np.linalg.norm(v2 - v1)

        fields_plus = individual_field_at_point(mid + delta * edge_dir)
        fields_minus = individual_field_at_point(mid - delta * edge_dir)

        phase_plus = np.angle(sum(fields_plus.values()))
        phase_minus = np.angle(sum(fields_minus.values()))

        # Handle phase wrapping: use the smallest angular difference
        phase_diff = phase_plus - phase_minus
        # Wrap to [-pi, pi]
        if phase_diff > np.pi:
            phase_diff -= 2 * np.pi
        elif phase_diff < -np.pi:
            phase_diff += 2 * np.pi

        # The gradient magnitude (d_phase / d_s) along the edge
        grad_along_edge = phase_diff / (2 * delta)

        # Arrow points in direction of increasing phase
        # If grad_along_edge > 0, phase increases in edge_dir direction
        # If grad_along_edge < 0, phase increases in -edge_dir direction
        arrow_scale = 0.15
        fig.add_trace(go.Cone(
            x=[mid[0]], y=[mid[1]], z=[mid[2]],
            u=[grad_along_edge * edge_dir[0] / abs(grad_along_edge + 1e-10) * arrow_scale],
            v=[grad_along_edge * edge_dir[1] / abs(grad_along_edge + 1e-10) * arrow_scale],
            w=[grad_along_edge * edge_dir[2] / abs(grad_along_edge + 1e-10) * arrow_scale],
            sizemode='absolute',
            sizeref=0.1,
            colorscale=[[0, 'magenta'], [1, 'magenta']],
            showscale=False,
            name=f'Phase grad ({edge_name})',
            hoverinfo='name'
        ))

    # --- Inter-tetrahedral overlap region ---
    # Show as a semi-transparent sphere at origin
    n_sphere = 20
    u = np.linspace(0, 2*np.pi, n_sphere)
    v = np.linspace(0, np.pi, n_sphere)
    r_overlap = 0.25  # Overlap region radius

    x_sphere = r_overlap * np.outer(np.cos(u), np.sin(v))
    y_sphere = r_overlap * np.outer(np.sin(u), np.sin(v))
    z_sphere = r_overlap * np.outer(np.ones(n_sphere), np.cos(v))

    fig.add_trace(go.Surface(
        x=x_sphere, y=y_sphere, z=z_sphere,
        opacity=0.15,
        colorscale=[[0, 'orange'], [1, 'orange']],
        showscale=False,
        name='T+ T- overlap region',
        hoverinfo='name'
    ))

    # --- Layout ---
    fig.update_layout(
        title=dict(
            text='Prop 0.0.17k4: Edge Transitions & Robin BC Regions<br>'
                 '<sub>Thick colored edges = W-face (Robin BC) | Magenta cones = phase gradient | Orange sphere = T+/T- overlap</sub>',
            x=0.5,
            font=dict(size=14)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-0.8, 0.8]),
            yaxis=dict(title='y', range=[-0.8, 0.8]),
            zaxis=dict(title='z', range=[-0.8, 0.8]),
            aspectmode='cube',
            camera=dict(
                eye=dict(x=-1.8, y=-1.8, z=1.5),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.02, y=0.98,
            bgcolor='rgba(255,255,255,0.9)'
        ),
        margin=dict(l=0, r=0, t=80, b=0),
        width=900,
        height=700
    )

    return fig


# =============================================================================
# VISUALIZATION: ROBIN BC EFFECT
# =============================================================================

def create_robin_bc_visualization():
    """
    Visualize the Robin BC effect: how field amplitude varies
    perpendicular to the W-face edge.

    Robin BC: d_n(psi) + alpha * psi = 0
    - alpha = 0: Neumann (free) - field extends freely
    - alpha -> inf: Dirichlet (clamped) - field goes to zero at boundary
    """
    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            'Field Amplitude vs Distance from W-Face Edge',
            'Effective Robin Parameter Along W-Face'
        ),
        specs=[[{'type': 'xy'}, {'type': 'xy'}]]
    )

    # --- Left plot: Field amplitude perpendicular to edge ---
    # Take the R-G edge and look perpendicular to it (toward/away from W vertex)

    edge_mid = 0.5 * (VERTICES_PLUS['R'] + VERTICES_PLUS['G'])
    edge_dir = VERTICES_PLUS['G'] - VERTICES_PLUS['R']
    edge_dir = edge_dir / np.linalg.norm(edge_dir)

    # Perpendicular direction (toward W vertex)
    to_w = VERTICES_PLUS['W'] - edge_mid
    to_w = to_w - np.dot(to_w, edge_dir) * edge_dir  # Remove edge component
    to_w = to_w / np.linalg.norm(to_w)

    # Sample perpendicular to edge
    n_perp = 50
    d_range = np.linspace(-0.4, 0.4, n_perp)

    total_mags = []
    r_mags = []
    g_mags = []
    b_mags = []

    for d in d_range:
        pt = edge_mid + d * to_w
        fields = individual_field_at_point(pt)
        r_mags.append(np.abs(fields['R']))
        g_mags.append(np.abs(fields['G']))
        b_mags.append(np.abs(fields['B']))
        total_mags.append(np.abs(sum(fields.values())))

    # Normalize
    max_val = max(total_mags)

    fig.add_trace(go.Scatter(x=d_range, y=np.array(r_mags)/max_val, name='R field',
                             line=dict(color='red', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=d_range, y=np.array(g_mags)/max_val, name='G field',
                             line=dict(color='green', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=d_range, y=np.array(b_mags)/max_val, name='B field',
                             line=dict(color='blue', width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=d_range, y=np.array(total_mags)/max_val, name='|Total|',
                             line=dict(color='black', width=3, dash='dash')), row=1, col=1)

    # Mark W-face edge location
    fig.add_vline(x=0, line=dict(color='gray', dash='dot'), row=1, col=1)
    fig.add_annotation(x=0, y=0.5, text='W-face<br>edge', showarrow=False,
                      xanchor='left', row=1, col=1)

    # Mark W vertex direction
    fig.add_annotation(x=-0.35, y=0.9, text='Toward W', showarrow=True,
                      ax=40, ay=0, row=1, col=1)
    fig.add_annotation(x=0.35, y=0.9, text='Away from W', showarrow=True,
                      ax=-40, ay=0, row=1, col=1)

    # --- Right plot: Effective Robin parameter ---
    # The Robin parameter alpha measures how quickly the field decays
    # alpha = -d_n(psi) / psi at the boundary

    # Sample along the W-face edges
    edges_to_sample = ['R-G', 'G-B', 'B-R']

    for edge_name in edges_to_sample:
        v1_name, v2_name = EDGES_T_PLUS[edge_name]
        v1 = VERTICES_PLUS[v1_name]
        v2 = VERTICES_PLUS[v2_name]

        n_edge = 30
        t_edge = np.linspace(0.1, 0.9, n_edge)  # Avoid vertices
        alpha_eff = []

        for t in t_edge:
            pt = v1 + t * (v2 - v1)

            # Compute normal derivative (toward W vertex)
            edge_dir = (v2 - v1) / np.linalg.norm(v2 - v1)
            to_w = VERTICES_PLUS['W'] - pt
            to_w = to_w - np.dot(to_w, edge_dir) * edge_dir
            normal = to_w / np.linalg.norm(to_w)

            # Field and its normal derivative
            delta = 0.02
            psi_0 = np.abs(total_chiral_field_at_point(pt))
            psi_plus = np.abs(total_chiral_field_at_point(pt + delta * normal))
            psi_minus = np.abs(total_chiral_field_at_point(pt - delta * normal))

            d_n_psi = (psi_plus - psi_minus) / (2 * delta)

            # Robin parameter: alpha = -d_n(psi) / psi
            if psi_0 > 1e-10:
                alpha = -d_n_psi / psi_0
            else:
                alpha = 0

            alpha_eff.append(alpha)

        # Color based on edge
        colors = {'R-G': 'purple', 'G-B': 'teal', 'B-R': 'orange'}
        fig.add_trace(go.Scatter(x=t_edge, y=alpha_eff, name=f'{edge_name} edge',
                                 line=dict(color=colors[edge_name], width=2)), row=1, col=2)

    # Reference lines
    fig.add_hline(y=0, line=dict(color='gray', dash='dot'), row=1, col=2)
    fig.add_annotation(x=0.5, y=0.5, text='alpha > 0: Dirichlet-like',
                      showarrow=False, row=1, col=2)
    fig.add_annotation(x=0.5, y=-0.5, text='alpha < 0: Neumann-like',
                      showarrow=False, row=1, col=2)

    # Update axes
    fig.update_xaxes(title_text='Distance from edge (toward/away from W)', row=1, col=1)
    fig.update_yaxes(title_text='Normalized field amplitude', row=1, col=1)
    fig.update_xaxes(title_text='Position along edge', row=1, col=2)
    fig.update_yaxes(title_text='Effective Robin parameter alpha', row=1, col=2)

    fig.update_layout(
        height=450,
        width=1000,
        title=dict(
            text='Prop 0.0.17k4: Robin Boundary Condition Effect<br>'
                 '<sub>Shows field confinement at W-face edges - determines vector eigenvalue c_V</sub>',
            x=0.5
        ),
        legend=dict(x=1.02, y=1, bgcolor='rgba(255,255,255,0.9)')
    )

    return fig


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Create all visualizations and open in browser."""
    import webbrowser
    import plotly.io as pio

    print("Creating edge transition visualizations for Prop 0.0.17k4...")

    # Create all three figures
    fig_profiles = create_edge_transition_figure()
    fig_3d = create_3d_edge_visualization()
    fig_robin = create_robin_bc_visualization()

    # Combine into single HTML with tabs
    html_content = """
    <!DOCTYPE html>
    <html>
    <head>
        <title>Prop 0.0.17k4: Edge Transitions</title>
        <script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
        <style>
            body { font-family: Arial, sans-serif; margin: 20px; }
            .tab-container { margin-bottom: 20px; }
            .tab-btn {
                padding: 10px 20px;
                margin-right: 5px;
                cursor: pointer;
                background: #e0e0e0;
                border: 1px solid #ccc;
                border-radius: 5px 5px 0 0;
            }
            .tab-btn.active { background: #4CAF50; color: white; }
            .tab-content { display: none; }
            .tab-content.active { display: block; }
            h1 { color: #333; }
            .description {
                background: #f9f9f9;
                padding: 15px;
                border-left: 4px solid #4CAF50;
                margin-bottom: 20px;
            }
        </style>
    </head>
    <body>
        <h1>Proposition 0.0.17k4: Edge Transitions Visualization</h1>

        <div class="description">
            <strong>Key Physics:</strong> Vector excitations couple to phase gradients. At the W-face edges
            (where color faces R, G, B meet), the field experiences a Robin boundary condition determined
            by the inter-tetrahedral coupling strength K. This eigenvalue problem determines c_V, which
            predicts M_rho = 777 MeV (0.3% from experiment).
        </div>

        <div class="tab-container">
            <button class="tab-btn active" onclick="showTab('tab1')">3D Edge Structure</button>
            <button class="tab-btn" onclick="showTab('tab2')">Edge Profiles</button>
            <button class="tab-btn" onclick="showTab('tab3')">Robin BC Effect</button>
        </div>

        <div id="tab1" class="tab-content active">
            <div id="plot3d"></div>
        </div>
        <div id="tab2" class="tab-content">
            <div id="plotProfiles"></div>
        </div>
        <div id="tab3" class="tab-content">
            <div id="plotRobin"></div>
        </div>

        <script>
            function showTab(tabId) {
                document.querySelectorAll('.tab-content').forEach(t => t.classList.remove('active'));
                document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
                document.getElementById(tabId).classList.add('active');
                event.target.classList.add('active');
            }
        </script>
    """

    # Add the plotly figures
    html_content += f"""
        <script>
            var fig3d = {pio.to_json(fig_3d)};
            var figProfiles = {pio.to_json(fig_profiles)};
            var figRobin = {pio.to_json(fig_robin)};

            Plotly.newPlot('plot3d', fig3d.data, fig3d.layout);
            Plotly.newPlot('plotProfiles', figProfiles.data, figProfiles.layout);
            Plotly.newPlot('plotRobin', figRobin.data, figRobin.layout);
        </script>
    </body>
    </html>
    """

    # Save and open
    html_path = '/tmp/prop_0_0_17k4_edge_transitions.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    print(f"Opening {html_path} in browser...")
    webbrowser.open(f'file://{html_path}')

    print("\nVisualization shows three tabs:")
    print("  1. 3D Edge Structure - Stella with highlighted W-face edges (Robin BC region)")
    print("  2. Edge Profiles - Field strength along key edges showing transitions")
    print("  3. Robin BC Effect - Field amplitude decay and effective Robin parameter")
    print("\nKey physical insight:")
    print("  - Thick colored edges = W-face (where Robin BC applies)")
    print("  - Orange sphere = T+/T- overlap region (inter-tetrahedral coupling)")
    print("  - Magenta cones = phase gradient direction (vector excitations couple to this)")
    print("\nDone!")


if __name__ == "__main__":
    main()
