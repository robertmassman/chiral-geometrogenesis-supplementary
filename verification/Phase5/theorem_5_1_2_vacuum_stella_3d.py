#!/usr/bin/env python3
"""
Theorem 5.1.2: Vacuum Energy Field on Stella Octangula
=======================================================

Maps the vacuum energy density field (same calculation as Panel A)
onto the stella octangula geometry. The color field sources (R, G, B)
are placed at three vertices of T+, and the vacuum energy is computed
at every point on the stella's triangular faces.

Author: Verification Suite
Date: February 2026
"""

import numpy as np
import plotly.graph_objects as go
import os

# =============================================================================
# GEOMETRY CONSTANTS
# =============================================================================

# Stella octangula vertices (two interpenetrating tetrahedra)
# T+ tetrahedron vertices
V_PLUS = np.array([
    [+1, +1, +1],   # Vertex 0: R color source
    [+1, -1, -1],   # Vertex 1: G color source
    [-1, +1, -1],   # Vertex 2: B color source
    [-1, -1, +1],   # Vertex 3: W (white/neutral)
]) / np.sqrt(3)

# T- tetrahedron vertices (inverted)
V_MINUS = np.array([
    [-1, -1, -1],   # Vertex 0
    [-1, +1, +1],   # Vertex 1
    [+1, -1, +1],   # Vertex 2
    [+1, +1, -1],   # Vertex 3
]) / np.sqrt(3)

# Color source positions (R, G, B at first 3 vertices of T+)
COLOR_VERTICES = V_PLUS[:3]

# Face definitions
FACES = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

# Regularization parameter
EPSILON = 0.05


# =============================================================================
# VACUUM ENERGY CALCULATION (same as Panel A)
# =============================================================================

def pressure_function(points, x_c, epsilon=EPSILON):
    """
    Pressure function P_c(x) = 1/(|x - x_c|² + ε²)

    Parameters:
        points: Nx3 array of positions
        x_c: 1x3 color source position
    """
    diff = points - x_c
    r_sq = np.sum(diff**2, axis=1)
    return 1.0 / (r_sq + epsilon**2)


def compute_vev_squared(points, color_vertices=COLOR_VERTICES, epsilon=EPSILON):
    """
    Compute v_χ²(x) from pressure functions.

    v_χ² = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]

    This is the same calculation used in Panel A.
    """
    P_R = pressure_function(points, color_vertices[0], epsilon)
    P_G = pressure_function(points, color_vertices[1], epsilon)
    P_B = pressure_function(points, color_vertices[2], epsilon)

    v_sq = 0.5 * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)
    return v_sq


def vacuum_energy_density(points, **kwargs):
    """
    Compute vacuum energy density: ρ_vac = λ v_χ⁴ (with λ=1)

    Same formula as Panel A.
    """
    v_sq = compute_vev_squared(points, **kwargs)
    return v_sq**2  # ρ = v⁴ = (v²)²


def log_vacuum_energy(points, **kwargs):
    """Compute log₁₀(ρ_vac) for visualization."""
    rho = vacuum_energy_density(points, **kwargs)
    return np.log10(np.maximum(rho, 1e-20))


# =============================================================================
# MESH GENERATION
# =============================================================================

def subdivide_triangle(v0, v1, v2, subdivisions=30):
    """
    Subdivide a triangle into a fine mesh using barycentric coordinates.

    Returns:
        vertices: Nx3 array of vertex positions
        faces: Mx3 array of triangle indices
    """
    vertices = []
    vertex_map = {}

    n = subdivisions
    for i in range(n + 1):
        for j in range(n + 1 - i):
            k = n - i - j
            # Barycentric coordinates
            u, v, w = i / n, j / n, k / n
            # Cartesian position
            point = u * v0 + v * v1 + w * v2
            vertex_map[(i, j)] = len(vertices)
            vertices.append(point)

    vertices = np.array(vertices)

    # Generate faces
    faces = []
    for i in range(n):
        for j in range(n - i):
            idx0 = vertex_map[(i, j)]
            idx1 = vertex_map[(i + 1, j)]
            idx2 = vertex_map[(i, j + 1)]
            faces.append([idx0, idx1, idx2])

            if i + j < n - 1:
                idx3 = vertex_map[(i + 1, j + 1)]
                faces.append([idx1, idx3, idx2])

    return vertices, np.array(faces)


def create_tetrahedron_mesh(base_vertices, face_defs, subdivisions=30):
    """Create subdivided mesh for all faces of a tetrahedron."""
    all_verts = []
    all_faces = []
    offset = 0

    for face_idx in face_defs:
        v0 = base_vertices[face_idx[0]]
        v1 = base_vertices[face_idx[1]]
        v2 = base_vertices[face_idx[2]]

        verts, faces = subdivide_triangle(v0, v1, v2, subdivisions)
        all_verts.append(verts)
        all_faces.append(faces + offset)
        offset += len(verts)

    return np.vstack(all_verts), np.vstack(all_faces)


# =============================================================================
# VISUALIZATION
# =============================================================================

def create_visualization(subdivisions=35):
    """Create the 3D Plotly visualization."""

    print("Creating stella octangula mesh...")

    # Create meshes
    verts_plus, faces_plus = create_tetrahedron_mesh(V_PLUS, FACES, subdivisions)
    verts_minus, faces_minus = create_tetrahedron_mesh(V_MINUS, FACES, subdivisions)

    print(f"  T+ mesh: {len(verts_plus)} vertices, {len(faces_plus)} faces")
    print(f"  T- mesh: {len(verts_minus)} vertices, {len(faces_minus)} faces")

    # Compute vacuum energy (log scale)
    print("Computing vacuum energy density...")
    log_rho_plus = log_vacuum_energy(verts_plus)
    log_rho_minus = log_vacuum_energy(verts_minus)

    # Get range for consistent colorscale
    log_min = min(log_rho_plus.min(), log_rho_minus.min())
    log_max = max(log_rho_plus.max(), log_rho_minus.max())
    print(f"  Log(rho) range: {log_min:.1f} to {log_max:.1f}")

    # Create figure
    fig = go.Figure()

    # Viridis colorscale (same as Panel A)
    colorscale = 'Viridis'

    # Add T+ tetrahedron
    fig.add_trace(go.Mesh3d(
        x=verts_plus[:, 0],
        y=verts_plus[:, 1],
        z=verts_plus[:, 2],
        i=faces_plus[:, 0],
        j=faces_plus[:, 1],
        k=faces_plus[:, 2],
        intensity=log_rho_plus,
        colorscale=colorscale,
        cmin=log_min,
        cmax=log_max,
        showscale=True,
        colorbar=dict(
            title=dict(text='log₁₀(ρ_vac)', side='right'),
            x=1.02,
            len=0.75
        ),
        opacity=1.0,
        name='T+ (colors R,G,B,W)',
        showlegend=True,
        flatshading=False,
        lighting=dict(ambient=0.7, diffuse=0.8, specular=0.3, roughness=0.4),
        lightposition=dict(x=100, y=200, z=150)
    ))

    # Add T- tetrahedron
    fig.add_trace(go.Mesh3d(
        x=verts_minus[:, 0],
        y=verts_minus[:, 1],
        z=verts_minus[:, 2],
        i=faces_minus[:, 0],
        j=faces_minus[:, 1],
        k=faces_minus[:, 2],
        intensity=log_rho_minus,
        colorscale=colorscale,
        cmin=log_min,
        cmax=log_max,
        showscale=False,
        opacity=1.0,
        name='T- (inverted)',
        showlegend=True,
        flatshading=False,
        lighting=dict(ambient=0.7, diffuse=0.8, specular=0.3, roughness=0.4),
        lightposition=dict(x=100, y=200, z=150)
    ))

    # Add wireframe edges
    def add_edges(vertices, faces_def, color, width=3):
        edges = set()
        for f in faces_def:
            for i in range(3):
                e = tuple(sorted([f[i], f[(i+1)%3]]))
                edges.add(e)
        for i, j in edges:
            fig.add_trace(go.Scatter3d(
                x=[vertices[i][0], vertices[j][0]],
                y=[vertices[i][1], vertices[j][1]],
                z=[vertices[i][2], vertices[j][2]],
                mode='lines',
                line=dict(color=color, width=width),
                showlegend=False,
                hoverinfo='skip'
            ))

    add_edges(V_PLUS, FACES, 'cyan', 4)
    add_edges(V_MINUS, FACES, 'magenta', 4)

    # Add color source markers (R, G, B)
    colors = ['red', 'green', 'blue']
    labels = ['R', 'G', 'B']
    for i, (c, l) in enumerate(zip(colors, labels)):
        v = COLOR_VERTICES[i]
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers+text',
            marker=dict(size=12, color=c, line=dict(color='white', width=2)),
            text=[f'χ_{l}'],
            textposition='top center',
            textfont=dict(size=14, color='white'),
            name=f'χ_{l} source',
            showlegend=True
        ))

    # W vertex marker
    fig.add_trace(go.Scatter3d(
        x=[V_PLUS[3, 0]], y=[V_PLUS[3, 1]], z=[V_PLUS[3, 2]],
        mode='markers',
        marker=dict(size=10, color='white', line=dict(color='black', width=2)),
        name='W vertex',
        showlegend=True
    ))

    # Center marker
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=14, color='gold', symbol='diamond',
                   line=dict(color='black', width=2)),
        name='Center (ρ→0)',
        showlegend=True
    ))

    # Layout
    extent = 0.75
    fig.update_layout(
        title=dict(
            text='Theorem 5.1.2: Vacuum Energy on Stella Octangula<br>'
                 '<sub>ρ_vac = v_χ⁴ mapped to triangular faces | '
                 'Color sources at R,G,B vertices of T+</sub>',
            x=0.5,
            font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-extent, extent],
                      backgroundcolor='rgb(30,30,40)',
                      gridcolor='rgb(60,60,70)'),
            yaxis=dict(title='Y', range=[-extent, extent],
                      backgroundcolor='rgb(30,30,40)',
                      gridcolor='rgb(60,60,70)'),
            zaxis=dict(title='Z', range=[-extent, extent],
                      backgroundcolor='rgb(30,30,40)',
                      gridcolor='rgb(60,60,70)'),
            aspectmode='cube',
            bgcolor='rgb(30,30,40)',
            camera=dict(
                eye=dict(x=1.6, y=1.6, z=1.3),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.01, y=0.99,
            bgcolor='rgba(255,255,255,0.9)',
            font=dict(size=10)
        ),
        paper_bgcolor='rgb(40,40,50)',
        margin=dict(l=0, r=0, t=80, b=0),
        width=1000,
        height=800
    )

    return fig, (log_min, log_max)


def export_static(fig, log_range):
    """Export static PNG with multiple views."""
    from PIL import Image, ImageDraw, ImageFont

    print("\nExporting static views...")

    fig.update_layout(title=None, margin=dict(l=0, r=0, t=0, b=0))

    views = [
        (dict(eye=dict(x=1.8, y=1.8, z=1.3), up=dict(x=0, y=0, z=1)), '(a) Isometric'),
        (dict(eye=dict(x=0, y=0, z=2.8), up=dict(x=0, y=1, z=0)), '(b) Top (Z-axis)'),
        (dict(eye=dict(x=2.8, y=0, z=0), up=dict(x=0, y=0, z=1)), '(c) Side (X-axis)'),
    ]

    plots_dir = os.path.join(os.path.dirname(__file__), '..', 'plots')
    os.makedirs(plots_dir, exist_ok=True)

    panels = []
    for i, (cam, title) in enumerate(views):
        fig.update_layout(scene_camera=cam, width=750, height=650)
        path = f'/tmp/stella_vac_{i}.png'
        print(f"  Exporting {title}...")
        fig.write_image(path, scale=2)
        panels.append((path, title))

    # Combine panels
    print("  Combining panels...")
    images = [Image.open(p[0]) for p in panels]

    gap = 15
    title_h = 90
    w_total = sum(img.width for img in images) + gap * 2
    h_total = images[0].height + title_h + 50

    combined = Image.new('RGB', (w_total, h_total), 'white')
    draw = ImageDraw.Draw(combined)

    try:
        title_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 26)
        sub_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 18)
        info_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 14)
    except:
        title_font = sub_font = info_font = ImageFont.load_default()

    # Title
    main = "Theorem 5.1.2: Vacuum Energy Density Mapped to Stella Octangula"
    bbox = draw.textbbox((0, 0), main, font=title_font)
    draw.text(((w_total - bbox[2]) // 2, 12), main, fill='black', font=title_font)

    # Subtitle
    sub = f"rho_vac = v_chi^4  |  log10(rho) range: {log_range[0]:.1f} to {log_range[1]:.1f}  |  Same calculation as Panel A"
    bbox = draw.textbbox((0, 0), sub, font=info_font)
    draw.text(((w_total - bbox[2]) // 2, 45), sub, fill='gray', font=info_font)

    # Paste panels
    x = 0
    for img, (path, label) in zip(images, panels):
        combined.paste(img, (x, title_h))
        bbox = draw.textbbox((0, 0), label, font=sub_font)
        draw.text((x + (img.width - bbox[2]) // 2, title_h - 22), label, fill='black', font=sub_font)
        x += img.width + gap
        os.remove(path)

    out_path = os.path.join(plots_dir, 'theorem_5_1_2_vacuum_energy_stella_mapped.png')
    combined.save(out_path, dpi=(150, 150))
    print(f"  Saved: {out_path}")
    return out_path


def main():
    import sys
    import plotly.io as pio

    print("="*65)
    print("Theorem 5.1.2: Vacuum Energy on Stella Octangula")
    print("="*65)
    print()
    print("This visualization maps the SAME vacuum energy calculation")
    print("from Panel A onto the stella octangula's triangular faces.")
    print()
    print("Key points:")
    print("  - Color sources (R,G,B) at three T+ vertices")
    print("  - v_chi^2 = 0.5*[(P_R-P_G)^2 + (P_G-P_B)^2 + (P_B-P_R)^2]")
    print("  - rho_vac = v_chi^4 (same formula as Panel A)")
    print("  - Yellow = high energy | Blue = low energy")
    print()

    fig, log_range = create_visualization(subdivisions=40)

    if '--export' in sys.argv:
        export_static(fig, log_range)
        return

    # Interactive HTML
    html = pio.to_html(fig, include_plotlyjs=True, full_html=True)

    info = """
    <div style="position:fixed; bottom:10px; left:10px; background:rgba(0,0,0,0.9);
         color:white; padding:15px; border-radius:8px; font-family:sans-serif;
         font-size:12px; max-width:300px; z-index:1000;">
        <strong style="color:#ffd700;">Same as Panel A!</strong><br><br>
        Color sources at T+ vertices:<br>
        <span style="color:red;">R</span>,
        <span style="color:green;">G</span>,
        <span style="color:blue;">B</span><br><br>
        <strong>Formula:</strong><br>
        v_chi^2 = 0.5*[sum of squared<br>
        pressure differences]<br>
        rho_vac = v_chi^4<br><br>
        <span style="color:#ffff00;">Yellow</span> = High energy<br>
        <span style="color:#440154;">Purple/Blue</span> = Low energy
    </div>
    """
    html = html.replace('</body>', info + '</body>')

    path = '/tmp/theorem_5_1_2_vacuum_stella.html'
    with open(path, 'w') as f:
        f.write(html)

    print(f"\nSaved: {path}")

    import webbrowser
    webbrowser.open(f'file://{path}')
    print("Opened in browser!")


if __name__ == "__main__":
    main()
