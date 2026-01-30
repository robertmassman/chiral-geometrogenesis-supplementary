#!/usr/bin/env python3
"""
Visualization: Pre-Geometric Emergence of the Stella Octangula

This visualization demonstrates the key concept from Definition 0.1.1:
The stella octangula GEOMETRY emerges from FIELD GRADIENTS.

Visual Concept:
- Show the continuous field intensity distribution (like ρ incoherent energy)
- The geometric edges "emerge" where field gradients are strongest
- Edges appear as ridges in the field, not as imposed lines
- Gradient coloring shows the transition from diffuse field → sharp geometry

Key insight: The boundary lines of the stella octangula are not fundamental -
they emerge from the field topology. The pre-geometric structure is the
field distribution; the geometry is emergent.

Key References:
- Definition-0.1.1-Stella-Octangula-Boundary-Topology.md §3.3
- Gap-Analysis-Pre-Geometric-Structure.md §6

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# =============================================================================
# GEOMETRY DEFINITIONS
# =============================================================================

def get_tetrahedron_vertices(scale=1.0):
    """Return vertices of both tetrahedra T+ and T-."""
    T_plus = {
        'R': np.array([1, 1, 1]) / np.sqrt(3) * scale,
        'G': np.array([1, -1, -1]) / np.sqrt(3) * scale,
        'B': np.array([-1, 1, -1]) / np.sqrt(3) * scale,
        'W': np.array([-1, -1, 1]) / np.sqrt(3) * scale,
    }
    T_minus = {
        'R̄': -T_plus['R'],
        'Ḡ': -T_plus['G'],
        'B̄': -T_plus['B'],
        'W̄': -T_plus['W'],
    }
    return T_plus, T_minus

def get_tetrahedron_edges():
    """Return edge pairs for each tetrahedron."""
    labels_plus = ['R', 'G', 'B', 'W']
    labels_minus = ['R̄', 'Ḡ', 'B̄', 'W̄']
    edges_plus = [(labels_plus[i], labels_plus[j]) for i in range(4) for j in range(i+1, 4)]
    edges_minus = [(labels_minus[i], labels_minus[j]) for i in range(4) for j in range(i+1, 4)]
    return edges_plus, edges_minus

# =============================================================================
# FIELD FUNCTIONS
# =============================================================================

def pressure_field(x, y, z, vertices, epsilon=0.15):
    """
    Compute total pressure field at point (x, y, z).
    This is the "incoherent" energy density ρ = Σ|χ_c|²
    """
    total = 0.0
    for v in vertices.values():
        r_sq = (x - v[0])**2 + (y - v[1])**2 + (z - v[2])**2
        total += 1.0 / (r_sq + epsilon**2)
    return total

def edge_field(x, y, z, vertices, edges, sigma=0.08):
    """
    Compute field intensity along edges.
    This represents the "ridge" where gradients from two vertices meet.
    """
    total = 0.0
    vert_list = list(vertices.keys())
    vert_vals = list(vertices.values())

    for v1_name, v2_name in edges:
        v1 = vertices[v1_name]
        v2 = vertices[v2_name]

        # Point-to-line distance
        pt = np.array([x, y, z])
        line_vec = v2 - v1
        line_len = np.linalg.norm(line_vec)
        line_unit = line_vec / line_len

        # Project point onto line
        t = np.dot(pt - v1, line_unit)
        t = np.clip(t, 0, line_len)  # Clamp to edge segment
        closest = v1 + t * line_unit

        dist = np.linalg.norm(pt - closest)
        total += np.exp(-dist**2 / (2 * sigma**2))

    return total

def compute_field_slice(vertices, edges, z_val=0.0, resolution=150,
                        epsilon=0.15, sigma=0.08, blend=0.5):
    """
    Compute 2D field slice showing blend of vertex field and edge field.

    blend=0: pure vertex/pressure field (diffuse, pre-geometric)
    blend=1: pure edge field (sharp geometry)
    """
    x = np.linspace(-1.2, 1.2, resolution)
    y = np.linspace(-1.2, 1.2, resolution)
    X, Y = np.meshgrid(x, y)

    F_vertex = np.zeros_like(X)
    F_edge = np.zeros_like(X)

    for i in range(resolution):
        for j in range(resolution):
            F_vertex[i, j] = pressure_field(X[i,j], Y[i,j], z_val, vertices, epsilon)
            F_edge[i, j] = edge_field(X[i,j], Y[i,j], z_val, vertices, edges, sigma)

    # Normalize
    F_vertex = F_vertex / F_vertex.max()
    F_edge = F_edge / F_edge.max()

    # Blend
    F_combined = (1 - blend) * F_vertex + blend * F_edge

    return X, Y, F_combined, F_vertex, F_edge

# =============================================================================
# 3D FIELD VISUALIZATION
# =============================================================================

def create_edge_tube(v1, v2, n_points=30, n_circle=12, radius=0.08):
    """Create a tube mesh along an edge for 3D visualization."""
    # Direction vector
    direction = v2 - v1
    length = np.linalg.norm(direction)
    direction = direction / length

    # Find perpendicular vectors
    if abs(direction[0]) < 0.9:
        perp1 = np.cross(direction, np.array([1, 0, 0]))
    else:
        perp1 = np.cross(direction, np.array([0, 1, 0]))
    perp1 = perp1 / np.linalg.norm(perp1)
    perp2 = np.cross(direction, perp1)

    # Generate tube surface
    t = np.linspace(0, 1, n_points)
    theta = np.linspace(0, 2 * np.pi, n_circle)

    x_tube = []
    y_tube = []
    z_tube = []

    for ti in t:
        center = v1 + ti * (v2 - v1)
        for th in theta:
            pt = center + radius * (np.cos(th) * perp1 + np.sin(th) * perp2)
            x_tube.append(pt[0])
            y_tube.append(pt[1])
            z_tube.append(pt[2])

    return np.array(x_tube), np.array(y_tube), np.array(z_tube)


def compute_3d_field_volume(vertices, edges, resolution=35, blend=0.0):
    """
    Compute 3D field on a grid.

    At blend=0: Very diffuse field - almost uniform fog with slight structure
    At blend=0.5: Vertex-centered field (like your ρ plot)
    At blend=1: Field concentrated along edges (geometric structure)

    The blend parameter now controls a 3-stage emergence:
    - 0.0-0.4: Diffuse fog → vertex-localized blobs
    - 0.4-1.0: Vertex blobs → edge-concentrated tubes
    """
    x = np.linspace(-1.3, 1.3, resolution)
    y = np.linspace(-1.3, 1.3, resolution)
    z = np.linspace(-1.3, 1.3, resolution)

    X, Y, Z = np.meshgrid(x, y, z, indexing='ij')

    # Stage 1: Very diffuse field (fog-like, nearly uniform)
    # Large epsilon = very spread out
    F_diffuse = np.zeros_like(X)
    epsilon_diffuse = 1.2  # Very wide - almost fills the whole space

    for v in vertices.values():
        r_sq = (X - v[0])**2 + (Y - v[1])**2 + (Z - v[2])**2
        F_diffuse += 1.0 / (r_sq + epsilon_diffuse**2)

    # Add a constant background to make it more fog-like
    F_diffuse += 0.3 * F_diffuse.max()

    # Stage 2: Vertex-localized field (like your ρ plot)
    F_vertex = np.zeros_like(X)
    epsilon_vertex = 0.35  # Medium - shows vertex structure

    for v in vertices.values():
        r_sq = (X - v[0])**2 + (Y - v[1])**2 + (Z - v[2])**2
        F_vertex += 1.0 / (r_sq + epsilon_vertex**2)

    # Stage 3: Edge-concentrated field (geometric structure)
    F_edge = np.zeros_like(X)
    sigma_edge = 0.10  # Tighter for sharper edges

    for v1, v2 in edges:
        edge_vec = v2 - v1
        edge_len = np.linalg.norm(edge_vec)
        edge_unit = edge_vec / edge_len

        for i in range(resolution):
            for j in range(resolution):
                for k in range(resolution):
                    pt = np.array([X[i,j,k], Y[i,j,k], Z[i,j,k]])
                    t = np.dot(pt - v1, edge_unit)
                    t = np.clip(t, 0, edge_len)
                    closest = v1 + t * edge_unit
                    dist = np.linalg.norm(pt - closest)
                    F_edge[i,j,k] += np.exp(-dist**2 / (2 * sigma_edge**2))

    # Normalize all fields
    F_diffuse = F_diffuse / F_diffuse.max()
    F_vertex = F_vertex / F_vertex.max()
    F_edge = F_edge / F_edge.max()

    # Three-stage blending:
    # blend 0.0 -> 0.4: diffuse -> vertex (fog condensing to blobs)
    # blend 0.4 -> 1.0: vertex -> edge (blobs condensing to lines)
    if blend <= 0.4:
        # Transition from diffuse fog to vertex blobs
        t = blend / 0.4  # 0 to 1 over this range
        F_combined = (1 - t) * F_diffuse + t * F_vertex
    else:
        # Transition from vertex blobs to edge tubes
        t = (blend - 0.4) / 0.6  # 0 to 1 over this range
        F_combined = (1 - t) * F_vertex + t * F_edge

    return X, Y, Z, F_combined


def create_3d_emergence_figure():
    """
    Create 3D figure showing field-to-geometry emergence.
    Uses layered isosurfaces to create smooth gradient effect.
    """

    T_plus, T_minus = get_tetrahedron_vertices()
    edges_plus, edges_minus = get_tetrahedron_edges()
    all_vertices = {**T_plus, **T_minus}

    # Convert edges to vertex arrays
    all_edges_arrays = []
    for v1_name, v2_name in edges_plus:
        all_edges_arrays.append((T_plus[v1_name], T_plus[v2_name]))
    for v1_name, v2_name in edges_minus:
        all_edges_arrays.append((T_minus[v1_name], T_minus[v2_name]))

    colors_plus = ['red', 'green', 'blue', 'silver']
    colors_minus = ['darkred', 'darkgreen', 'darkblue', 'dimgray']

    fig = go.Figure()

    n_steps = 11
    resolution = 30  # Grid resolution for volume

    print("  Computing 3D field volumes (this may take a moment)...")

    for step in range(n_steps):
        blend = step / (n_steps - 1)
        visible = (step == 0)  # Start at 0% emergence

        print(f"    Step {step+1}/{n_steps} (blend={blend:.0%})...")

        # Compute the blended field volume
        X, Y, Z, F = compute_3d_field_volume(
            all_vertices, all_edges_arrays,
            resolution=resolution,
            blend=blend
        )

        # Create layered isosurfaces for smooth gradient effect
        # Multiple surfaces at different iso-values create gradient appearance
        iso_levels = [0.15, 0.30, 0.50, 0.70, 0.85]

        # Color scale matching your 2D heatmaps
        level_colors = [
            'rgba(40, 20, 80, 0.15)',    # Deep purple, very transparent
            'rgba(120, 50, 100, 0.25)',  # Magenta
            'rgba(200, 100, 50, 0.35)',  # Orange
            'rgba(255, 180, 50, 0.50)',  # Yellow-orange
            'rgba(255, 240, 150, 0.70)', # Bright yellow
        ]

        for iso_val, color in zip(iso_levels, level_colors):
            fig.add_trace(go.Isosurface(
                x=X.flatten(),
                y=Y.flatten(),
                z=Z.flatten(),
                value=F.flatten(),
                isomin=iso_val - 0.02,
                isomax=iso_val + 0.02,
                surface_count=1,
                colorscale=[[0, color], [1, color]],
                showscale=False,
                opacity=float(color.split(',')[3].rstrip(')')),
                caps=dict(x_show=False, y_show=False, z_show=False),
                visible=visible,
                hoverinfo='skip'
            ))

        # --- Edge lines (fade in with emergence) ---
        edge_opacity = blend * 0.9
        edge_width = 2 + 6 * blend

        # T+ edges
        for v1_name, v2_name in edges_plus:
            v1 = T_plus[v1_name]
            v2 = T_plus[v2_name]

            fig.add_trace(go.Scatter3d(
                x=[v1[0], v2[0]],
                y=[v1[1], v2[1]],
                z=[v1[2], v2[2]],
                mode='lines',
                line=dict(
                    color=f'rgba(150, 200, 255, {edge_opacity})',
                    width=edge_width
                ),
                visible=visible,
                showlegend=False,
                hoverinfo='skip'
            ))

        # T- edges
        for v1_name, v2_name in edges_minus:
            v1 = T_minus[v1_name]
            v2 = T_minus[v2_name]

            fig.add_trace(go.Scatter3d(
                x=[v1[0], v2[0]],
                y=[v1[1], v2[1]],
                z=[v1[2], v2[2]],
                mode='lines',
                line=dict(
                    color=f'rgba(220, 150, 220, {edge_opacity * 0.7})',
                    width=edge_width * 0.7
                ),
                visible=visible,
                showlegend=False,
                hoverinfo='skip'
            ))

        # --- Vertex markers (fade in with emergence) ---
        vertex_opacity = 0.3 + 0.7 * blend
        vertex_size = 6 + 8 * blend

        fig.add_trace(go.Scatter3d(
            x=[v[0] for v in T_plus.values()],
            y=[v[1] for v in T_plus.values()],
            z=[v[2] for v in T_plus.values()],
            mode='markers+text' if blend > 0.5 else 'markers',
            marker=dict(
                size=vertex_size,
                color=colors_plus,
                opacity=vertex_opacity,
                line=dict(width=2 if blend > 0.3 else 0, color='white')
            ),
            text=list(T_plus.keys()) if blend > 0.5 else None,
            textposition='top center',
            textfont=dict(size=10, color='white'),
            visible=visible,
            showlegend=False
        ))

        fig.add_trace(go.Scatter3d(
            x=[v[0] for v in T_minus.values()],
            y=[v[1] for v in T_minus.values()],
            z=[v[2] for v in T_minus.values()],
            mode='markers',
            marker=dict(
                size=vertex_size * 0.7,
                color=colors_minus,
                opacity=vertex_opacity * 0.6,
                line=dict(width=1 if blend > 0.3 else 0, color='gray')
            ),
            visible=visible,
            showlegend=False
        ))

    # Traces per step: 5 isosurfaces + 6 T+ edges + 6 T- edges + 2 vertex markers = 19
    traces_per_step = 19

    # Create slider steps
    steps = []
    for i in range(n_steps):
        blend = i / (n_steps - 1)
        visibility = [False] * (n_steps * traces_per_step)
        for j in range(traces_per_step):
            visibility[i * traces_per_step + j] = True

        step = dict(
            method='update',
            args=[{'visible': visibility}],
            label=f'{blend:.0%}'
        )
        steps.append(step)

    sliders = [dict(
        active=0,  # Start at 0% to show diffuse field
        currentvalue={"prefix": "Geometry Emergence: ", "font": {"size": 14, "color": "white"}},
        pad={"t": 50},
        steps=steps,
        bgcolor='rgba(50,50,60,0.8)',
        bordercolor='gray',
        font=dict(color='white')
    )]

    fig.update_layout(
        title=dict(
            text='<b>Pre-Geometric Emergence: Field → Geometry</b><br>' +
                 '<sup>Smooth field gradients condense into stella octangula edges</sup>',
            font=dict(size=16, color='white'),
            x=0.5
        ),
        scene=dict(
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False,
                      showbackground=False, title=''),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False,
                      showbackground=False, title=''),
            zaxis=dict(showgrid=False, zeroline=False, showticklabels=False,
                      showbackground=False, title=''),
            bgcolor='rgb(15, 15, 25)',
            camera=dict(eye=dict(x=1.8, y=1.8, z=1.2)),
            aspectmode='cube'
        ),
        paper_bgcolor='rgb(15, 15, 25)',
        font=dict(color='white'),
        sliders=sliders,
        showlegend=False,
        height=750,
        width=950,
        annotations=[
            dict(
                text='<b>0%:</b> Smooth diffuse field (pre-geometric)<br>' +
                     '<b>100%:</b> Field condensed into geometric edges',
                showarrow=False,
                x=0.02, y=0.12,
                xref='paper', yref='paper',
                align='left',
                font=dict(size=11, color='lightgray'),
                bgcolor='rgba(30,30,40,0.9)',
                bordercolor='gray',
                borderwidth=1
            )
        ]
    )

    return fig

# =============================================================================
# 2D SLICE VISUALIZATION (Main requested style)
# =============================================================================

def create_2d_emergence_figure():
    """
    Create 2D figure showing field-to-geometry emergence in a slice.
    This matches the style of the user's reference images.
    """

    T_plus, T_minus = get_tetrahedron_vertices()
    edges_plus, edges_minus = get_tetrahedron_edges()
    all_vertices = {**T_plus, **T_minus}
    all_edges = edges_plus + edges_minus

    # Create subplots for different emergence levels
    fig = make_subplots(
        rows=1, cols=3,
        subplot_titles=[
            '<b>Pre-Geometric Field</b><br><sup>Vertex pressure only (no edges)</sup>',
            '<b>Emerging Geometry</b><br><sup>Edge ridges appear from gradients</sup>',
            '<b>Full Geometry</b><br><sup>Stella octangula edges crystallized</sup>'
        ],
        horizontal_spacing=0.08
    )

    # Z-slice through the structure (z=0 plane)
    z_slice = 0.0
    resolution = 200

    # Compute fields for different blend levels
    blends = [0.0, 0.5, 1.0]

    for col, blend in enumerate(blends, 1):
        X, Y, F_combined, F_vertex, F_edge = compute_field_slice(
            all_vertices, all_edges, z_val=z_slice,
            resolution=resolution, epsilon=0.18, sigma=0.10, blend=blend
        )

        # Create heatmap
        fig.add_trace(
            go.Heatmap(
                x=X[0, :],
                y=Y[:, 0],
                z=F_combined,
                colorscale=[
                    [0.0, 'rgb(15, 15, 35)'],       # Dark blue
                    [0.2, 'rgb(40, 20, 80)'],       # Deep purple
                    [0.4, 'rgb(120, 50, 100)'],     # Magenta
                    [0.6, 'rgb(200, 100, 50)'],     # Orange
                    [0.8, 'rgb(255, 200, 50)'],     # Yellow
                    [1.0, 'rgb(255, 255, 200)'],    # Bright
                ],
                showscale=(col == 3),
                colorbar=dict(
                    title=dict(text='Field<br>Intensity', font=dict(color='white')),
                    tickfont=dict(color='white'),
                    x=1.02
                ) if col == 3 else None,
                hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>Field: %{z:.3f}<extra></extra>'
            ),
            row=1, col=col
        )

        # Overlay edge lines with opacity based on blend
        edge_opacity = 0.1 + 0.7 * blend
        edge_width = 1 + 2 * blend

        for v1_name, v2_name in all_edges:
            v1 = all_vertices[v1_name]
            v2 = all_vertices[v2_name]

            # Only draw edges that intersect or are near z=0 plane
            if abs(v1[2]) < 0.8 or abs(v2[2]) < 0.8:
                # Color based on tetrahedron
                if v1_name in T_plus and v2_name in T_plus:
                    color = f'rgba(100, 150, 255, {edge_opacity})'
                elif v1_name in T_minus and v2_name in T_minus:
                    color = f'rgba(255, 100, 100, {edge_opacity})'
                else:
                    continue  # Skip inter-tetrahedron for clarity

                fig.add_trace(
                    go.Scatter(
                        x=[v1[0], v2[0]],
                        y=[v1[1], v2[1]],
                        mode='lines',
                        line=dict(color=color, width=edge_width),
                        showlegend=False,
                        hoverinfo='skip'
                    ),
                    row=1, col=col
                )

        # Mark vertices in z=0 slice
        for name, v in all_vertices.items():
            if abs(v[2]) < 0.3:  # Near z=0
                if name in T_plus:
                    color = {'R': 'red', 'G': 'lime', 'B': 'blue', 'W': 'white'}[name]
                else:
                    color = 'gray'

                fig.add_trace(
                    go.Scatter(
                        x=[v[0]], y=[v[1]],
                        mode='markers',
                        marker=dict(
                            size=10 + 5 * blend,
                            color=color,
                            line=dict(width=2, color='white'),
                            opacity=0.3 + 0.7 * blend
                        ),
                        showlegend=False,
                        hovertemplate=f'{name}<extra></extra>'
                    ),
                    row=1, col=col
                )

        # Mark center
        fig.add_trace(
            go.Scatter(
                x=[0], y=[0],
                mode='markers',
                marker=dict(
                    symbol='star',
                    size=12,
                    color='white',
                    line=dict(width=1, color='black')
                ),
                showlegend=False,
                name='Center'
            ),
            row=1, col=col
        )

    # Update layout
    fig.update_layout(
        title=dict(
            text='<b>Stella Octangula: Pre-Geometric → Geometric Emergence</b><br>' +
                 '<sup>Z = 0 cross-section showing how edge structure emerges from field gradients</sup>',
            font=dict(size=16, color='white'),
            x=0.5
        ),
        paper_bgcolor='rgb(15, 15, 25)',
        plot_bgcolor='rgb(15, 15, 25)',
        font=dict(color='white'),
        height=500,
        width=1400
    )

    # Update axes
    for col in range(1, 4):
        fig.update_xaxes(
            range=[-1.2, 1.2],
            scaleanchor=f'y{col}' if col > 1 else 'y',
            scaleratio=1,
            showgrid=False,
            zeroline=False,
            title='x' if col == 2 else '',
            row=1, col=col
        )
        fig.update_yaxes(
            range=[-1.2, 1.2],
            showgrid=False,
            zeroline=False,
            title='y' if col == 1 else '',
            row=1, col=col
        )

    return fig

# =============================================================================
# ANIMATED 2D FIGURE
# =============================================================================

def create_animated_2d_emergence():
    """
    Create animated 2D figure showing continuous emergence.
    """

    T_plus, T_minus = get_tetrahedron_vertices()
    edges_plus, edges_minus = get_tetrahedron_edges()
    all_vertices = {**T_plus, **T_minus}
    all_edges = edges_plus + edges_minus

    z_slice = 0.0
    resolution = 150
    n_frames = 30

    # Precompute vertex and edge fields
    X, Y, _, F_vertex, F_edge = compute_field_slice(
        all_vertices, all_edges, z_val=z_slice,
        resolution=resolution, epsilon=0.18, sigma=0.10, blend=0.0
    )

    # Create initial figure
    fig = go.Figure()

    # Initial heatmap (full emergence)
    F_initial = F_edge  # Start at full geometry

    fig.add_trace(
        go.Heatmap(
            x=X[0, :],
            y=Y[:, 0],
            z=F_initial,
            colorscale=[
                [0.0, 'rgb(15, 15, 35)'],
                [0.2, 'rgb(40, 20, 80)'],
                [0.4, 'rgb(120, 50, 100)'],
                [0.6, 'rgb(200, 100, 50)'],
                [0.8, 'rgb(255, 200, 50)'],
                [1.0, 'rgb(255, 255, 200)'],
            ],
            showscale=True,
            colorbar=dict(
                title=dict(text='Field', font=dict(color='white')),
                tickfont=dict(color='white')
            )
        )
    )

    # Add center marker
    fig.add_trace(
        go.Scatter(
            x=[0], y=[0],
            mode='markers',
            marker=dict(symbol='star', size=15, color='white',
                       line=dict(width=1, color='black')),
            showlegend=False
        )
    )

    # Create frames
    frames = []
    for i in range(n_frames):
        blend = i / (n_frames - 1)
        F_combined = (1 - blend) * F_vertex + blend * F_edge

        frame = go.Frame(
            data=[
                go.Heatmap(
                    x=X[0, :],
                    y=Y[:, 0],
                    z=F_combined,
                    colorscale=[
                        [0.0, 'rgb(15, 15, 35)'],
                        [0.2, 'rgb(40, 20, 80)'],
                        [0.4, 'rgb(120, 50, 100)'],
                        [0.6, 'rgb(200, 100, 50)'],
                        [0.8, 'rgb(255, 200, 50)'],
                        [1.0, 'rgb(255, 255, 200)'],
                    ],
                    showscale=True
                ),
                go.Scatter(
                    x=[0], y=[0],
                    mode='markers',
                    marker=dict(symbol='star', size=15, color='white',
                               line=dict(width=1, color='black'))
                )
            ],
            name=str(i)
        )
        frames.append(frame)

    fig.frames = frames

    # Slider and buttons
    fig.update_layout(
        title=dict(
            text='<b>Geometry Emerging from Field Gradients</b><br>' +
                 '<sup>Watch edges crystallize from the diffuse pre-geometric field</sup>',
            font=dict(size=16, color='white'),
            x=0.5
        ),
        paper_bgcolor='rgb(15, 15, 25)',
        plot_bgcolor='rgb(15, 15, 25)',
        font=dict(color='white'),
        xaxis=dict(
            range=[-1.2, 1.2],
            scaleanchor='y',
            scaleratio=1,
            showgrid=False,
            zeroline=False,
            title='x'
        ),
        yaxis=dict(
            range=[-1.2, 1.2],
            showgrid=False,
            zeroline=False,
            title='y'
        ),
        height=650,
        width=750,
        updatemenus=[
            dict(
                type='buttons',
                showactive=True,
                y=0.0,
                x=0.1,
                xanchor='left',
                buttons=[
                    dict(
                        label='▶ Animate',
                        method='animate',
                        args=[None, {
                            'frame': {'duration': 100, 'redraw': True},
                            'fromcurrent': True,
                            'transition': {'duration': 50}
                        }]
                    ),
                    dict(
                        label='⏸ Pause',
                        method='animate',
                        args=[[None], {
                            'frame': {'duration': 0, 'redraw': False},
                            'mode': 'immediate',
                            'transition': {'duration': 0}
                        }]
                    )
                ]
            )
        ],
        sliders=[{
            'active': n_frames - 1,
            'yanchor': 'top',
            'xanchor': 'left',
            'currentvalue': {
                'font': {'size': 14, 'color': 'white'},
                'prefix': 'Emergence: ',
                'suffix': '%',
                'visible': True,
                'xanchor': 'center'
            },
            'transition': {'duration': 50},
            'pad': {'b': 10, 't': 60},
            'len': 0.75,
            'x': 0.15,
            'y': 0,
            'steps': [
                {
                    'args': [[str(i)], {
                        'frame': {'duration': 100, 'redraw': True},
                        'mode': 'immediate',
                        'transition': {'duration': 50}
                    }],
                    'label': str(int(i * 100 / (n_frames - 1))),
                    'method': 'animate'
                }
                for i in range(n_frames)
            ]
        }]
    )

    return fig

# =============================================================================
# MAIN
# =============================================================================

def main():
    """Generate and save the visualizations."""
    import os

    output_dir = 'verification/plots'
    os.makedirs(output_dir, exist_ok=True)

    print("=" * 70)
    print("PRE-GEOMETRIC EMERGENCE VISUALIZATION")
    print("Stella Octangula: Field Gradients → Geometric Edges")
    print("=" * 70)
    print()

    # Create 2D triptych (static comparison)
    print("Creating 2D emergence triptych...")
    fig_2d = create_2d_emergence_figure()
    output_path = os.path.join(output_dir, 'stella_pregeometric_emergence.html')
    fig_2d.write_html(output_path)
    print(f"  ✓ Saved: {output_path}")

    # Create animated 2D figure
    print("\nCreating animated 2D emergence...")
    fig_anim = create_animated_2d_emergence()
    output_path_anim = os.path.join(output_dir, 'stella_emergence_animated.html')
    fig_anim.write_html(output_path_anim)
    print(f"  ✓ Saved: {output_path_anim}")

    # Create 3D isosurface figure
    print("\nCreating 3D emergence visualization...")
    fig_3d = create_3d_emergence_figure()
    output_path_3d = os.path.join(output_dir, 'stella_emergence_3d.html')
    fig_3d.write_html(output_path_3d)
    print(f"  ✓ Saved: {output_path_3d}")

    print()
    print("=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    print()
    print("Key concept illustrated:")
    print("  The geometric EDGES of the stella octangula are not fundamental.")
    print("  They EMERGE from field gradient ridges - where pressure from")
    print("  adjacent vertices creates intensity maxima along the lines")
    print("  connecting them.")
    print()
    print("  0% emergence: Pure vertex field (diffuse blobs at corners)")
    print("  100% emergence: Edge field (sharp ridges along connections)")
    print()
    print("  This is the visualization of Definition 0.1.1 §3.3:")
    print("  'The ℝ³ embedding is computational scaffolding — physics depends")
    print("   only on abstract properties, not on the specific realization.'")

if __name__ == "__main__":
    main()
