#!/usr/bin/env python3
"""
Theorem 5.1.2: Vacuum Energy Density Mapped to Stella Octangula
================================================================

Creates an interactive 3D visualization showing vacuum energy density
directly mapped onto the triangular faces of the stella octangula.

The stella octangula is two interpenetrating tetrahedra (T+ and T-).
Each has 4 triangular faces, giving 8 faces total with Euler χ = 4.

The vacuum energy ρ_vac(x) = λ × v_χ(x)⁴ is computed at each point
on the surface, showing how it varies across the geometry and
demonstrating the phase cancellation at the center.

Author: Verification Suite
Date: February 2026
"""

import numpy as np
import plotly.graph_objects as go
import os

# =============================================================================
# PHYSICAL CONSTANTS
# =============================================================================

HIGGS_QUARTIC = 0.13  # λ (Higgs quartic coupling)
HIGGS_VEV = 246.22    # v in GeV
EPSILON = 0.05        # Regularization parameter
A0 = 1.0              # Base amplitude

# SU(3) phases: cube roots of unity
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
# T+ tetrahedron vertices (normalized to unit distance from origin)
V_PLUS = np.array([
    [1, 1, 1],      # R vertex
    [1, -1, -1],    # G vertex
    [-1, 1, -1],    # B vertex
    [-1, -1, 1],    # W vertex
]) / np.sqrt(3)

# T- tetrahedron vertices (inverted)
V_MINUS = np.array([
    [-1, -1, -1],   # R_bar vertex
    [-1, 1, 1],     # G_bar vertex
    [1, -1, 1],     # B_bar vertex
    [1, 1, -1],     # W_bar vertex
]) / np.sqrt(3)

# Face definitions (vertex indices for each triangular face)
# Each tetrahedron has 4 faces
FACES_PLUS = [
    [0, 1, 2],  # RGB face
    [0, 1, 3],  # RGW face
    [0, 2, 3],  # RBW face
    [1, 2, 3],  # GBW face
]

FACES_MINUS = [
    [0, 1, 2],  # R_bar G_bar B_bar face
    [0, 1, 3],  # R_bar G_bar W_bar face
    [0, 2, 3],  # R_bar B_bar W_bar face
    [1, 2, 3],  # G_bar B_bar W_bar face
]


# =============================================================================
# CORE FIELD FUNCTIONS
# =============================================================================

def pressure_function(x, y, z, x_c, epsilon=EPSILON):
    """
    Pressure function P_c(x) at a single point or array of points.

    P_c(x) = 1/(|x - x_c|² + ε²)
    """
    dist_sq = (x - x_c[0])**2 + (y - x_c[1])**2 + (z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field(x, y, z, a0=A0, epsilon=EPSILON):
    """
    Compute the total chiral field χ_total at given points.

    χ_total(x) = Σ_c a₀ P_c(x) exp(iφ_c)

    where c ∈ {R, G, B} and φ_c = 0, 2π/3, 4π/3
    """
    total = np.zeros_like(x, dtype=complex)
    colors = ['R', 'G', 'B']
    for i, c in enumerate(colors):
        x_c = V_PLUS[i]  # R, G, B are at indices 0, 1, 2
        P_c = pressure_function(x, y, z, x_c, epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def vacuum_energy_density(x, y, z, lambda_quartic=HIGGS_QUARTIC,
                         v_higgs=HIGGS_VEV, a0=A0, epsilon=EPSILON):
    """
    Compute vacuum energy density: ρ_vac(x) = λ × v_χ(x)⁴

    Position-dependent VEV: v_χ(x) = v × |χ_total(x)|/|χ_total|_max
    """
    chi_total = total_chiral_field(x, y, z, a0, epsilon)
    chi_mag = np.abs(chi_total)

    # For normalization, compute max on a reference grid
    # (or use analytical approximation near vertices)
    chi_max = np.max(chi_mag) if chi_mag.size > 1 else 400.0  # approx max
    if chi_max < 1e-10:
        chi_max = 400.0  # fallback

    normalized = chi_mag / chi_max
    v_chi = v_higgs * normalized

    return lambda_quartic * v_chi**4


def log_vacuum_energy(x, y, z, **kwargs):
    """Compute log₁₀(ρ_vac) for visualization."""
    rho = vacuum_energy_density(x, y, z, **kwargs)
    rho_clipped = np.maximum(rho, 1e-20)
    return np.log10(rho_clipped)


# =============================================================================
# TRIANGULAR MESH GENERATION
# =============================================================================

def subdivide_triangle(v0, v1, v2, subdivisions=20):
    """
    Subdivide a triangle into a fine mesh for smooth color mapping.

    Uses barycentric coordinates to create a uniform grid of points
    within the triangle.

    Returns:
        vertices: Nx3 array of vertex positions
        faces: Mx3 array of triangle indices
    """
    vertices = []
    vertex_indices = {}

    # Generate points using barycentric coordinates
    n = subdivisions
    for i in range(n + 1):
        for j in range(n + 1 - i):
            k = n - i - j
            # Barycentric coordinates
            u = i / n
            v = j / n
            w = k / n
            # Cartesian position
            point = u * v0 + v * v1 + w * v2
            vertex_indices[(i, j)] = len(vertices)
            vertices.append(point)

    vertices = np.array(vertices)

    # Generate triangular faces
    faces = []
    for i in range(n):
        for j in range(n - i):
            # Lower triangle
            idx0 = vertex_indices[(i, j)]
            idx1 = vertex_indices[(i + 1, j)]
            idx2 = vertex_indices[(i, j + 1)]
            faces.append([idx0, idx1, idx2])

            # Upper triangle (if it exists)
            if i + j < n - 1:
                idx3 = vertex_indices[(i + 1, j + 1)]
                faces.append([idx1, idx3, idx2])

    return vertices, np.array(faces)


def create_tetrahedron_mesh(vertices, face_indices, subdivisions=20, scale=1.0):
    """
    Create a subdivided mesh for a tetrahedron.

    Returns combined vertices, faces, and which original face each belongs to.
    """
    all_vertices = []
    all_faces = []
    face_ids = []
    vertex_offset = 0

    for face_idx, face in enumerate(face_indices):
        v0 = vertices[face[0]] * scale
        v1 = vertices[face[1]] * scale
        v2 = vertices[face[2]] * scale

        verts, faces = subdivide_triangle(v0, v1, v2, subdivisions)

        all_vertices.append(verts)
        all_faces.append(faces + vertex_offset)
        face_ids.extend([face_idx] * len(faces))

        vertex_offset += len(verts)

    return np.vstack(all_vertices), np.vstack(all_faces), np.array(face_ids)


# =============================================================================
# VISUALIZATION
# =============================================================================

def create_stella_vacuum_energy_visualization(subdivisions=25, scale=1.0):
    """
    Create interactive 3D visualization of vacuum energy on stella octangula.

    The vacuum energy density is computed at each vertex of the subdivided
    triangular mesh and displayed as a color map on the surface.
    """
    print("Creating stella octangula mesh...")

    # Create meshes for both tetrahedra
    verts_plus, faces_plus, fids_plus = create_tetrahedron_mesh(
        V_PLUS, FACES_PLUS, subdivisions, scale
    )
    verts_minus, faces_minus, fids_minus = create_tetrahedron_mesh(
        V_MINUS, FACES_MINUS, subdivisions, scale
    )

    print(f"  T+ mesh: {len(verts_plus)} vertices, {len(faces_plus)} faces")
    print(f"  T- mesh: {len(verts_minus)} vertices, {len(faces_minus)} faces")

    # Compute vacuum energy at all vertices
    print("Computing vacuum energy density...")

    # Need global normalization for chi_max
    # Sample on a grid to find true maximum
    test_grid = np.linspace(-0.6, 0.6, 50)
    X, Y, Z = np.meshgrid(test_grid, test_grid, test_grid)
    chi_test = np.abs(total_chiral_field(X.ravel(), Y.ravel(), Z.ravel()))
    chi_max_global = np.max(chi_test)
    print(f"  Global chi_max: {chi_max_global:.2f}")

    def compute_log_rho(vertices):
        """Compute log vacuum energy with global normalization."""
        x, y, z = vertices[:, 0], vertices[:, 1], vertices[:, 2]
        chi = np.abs(total_chiral_field(x, y, z))
        normalized = chi / chi_max_global
        v_chi = HIGGS_VEV * normalized
        rho = HIGGS_QUARTIC * v_chi**4
        return np.log10(np.maximum(rho, 1e-20))

    log_rho_plus = compute_log_rho(verts_plus)
    log_rho_minus = compute_log_rho(verts_minus)

    print(f"  T+ log(rho) range: {log_rho_plus.min():.1f} to {log_rho_plus.max():.1f}")
    print(f"  T- log(rho) range: {log_rho_minus.min():.1f} to {log_rho_minus.max():.1f}")

    # Combined range for consistent colorscale
    log_rho_min = min(log_rho_plus.min(), log_rho_minus.min())
    log_rho_max = max(log_rho_plus.max(), log_rho_minus.max())

    # Create figure
    fig = go.Figure()

    # Plasma-like colorscale for energy visualization
    colorscale = [
        [0.0, 'rgb(13, 8, 135)'],     # Deep blue (low energy)
        [0.25, 'rgb(126, 3, 168)'],   # Purple
        [0.5, 'rgb(203, 71, 119)'],   # Pink/magenta
        [0.75, 'rgb(248, 149, 64)'],  # Orange
        [1.0, 'rgb(240, 249, 33)']    # Yellow (high energy)
    ]

    # Add T+ tetrahedron mesh
    fig.add_trace(go.Mesh3d(
        x=verts_plus[:, 0],
        y=verts_plus[:, 1],
        z=verts_plus[:, 2],
        i=faces_plus[:, 0],
        j=faces_plus[:, 1],
        k=faces_plus[:, 2],
        intensity=log_rho_plus,
        colorscale=colorscale,
        cmin=log_rho_min,
        cmax=log_rho_max,
        showscale=True,
        colorbar=dict(
            title=dict(text='log₁₀(ρ_vac) [GeV⁴]', side='right'),
            x=1.02,
            len=0.7
        ),
        opacity=0.95,
        name='T+ tetrahedron',
        showlegend=True,
        flatshading=False,
        lighting=dict(
            ambient=0.6,
            diffuse=0.8,
            specular=0.2,
            roughness=0.5
        ),
        lightposition=dict(x=100, y=200, z=300)
    ))

    # Add T- tetrahedron mesh
    fig.add_trace(go.Mesh3d(
        x=verts_minus[:, 0],
        y=verts_minus[:, 1],
        z=verts_minus[:, 2],
        i=faces_minus[:, 0],
        j=faces_minus[:, 1],
        k=faces_minus[:, 2],
        intensity=log_rho_minus,
        colorscale=colorscale,
        cmin=log_rho_min,
        cmax=log_rho_max,
        showscale=False,
        opacity=0.95,
        name='T- tetrahedron',
        showlegend=True,
        flatshading=False,
        lighting=dict(
            ambient=0.6,
            diffuse=0.8,
            specular=0.2,
            roughness=0.5
        ),
        lightposition=dict(x=100, y=200, z=300)
    ))

    # Add wireframe edges for clarity
    def add_wireframe(vertices, face_indices, color, name):
        """Add wireframe edges for a tetrahedron."""
        # Get unique edges
        edges = set()
        for face in face_indices:
            for i in range(3):
                edge = tuple(sorted([face[i], face[(i+1) % 3]]))
                edges.add(edge)

        for i, j in edges:
            fig.add_trace(go.Scatter3d(
                x=[vertices[i][0], vertices[j][0]],
                y=[vertices[i][1], vertices[j][1]],
                z=[vertices[i][2], vertices[j][2]],
                mode='lines',
                line=dict(color=color, width=4),
                showlegend=False,
                hoverinfo='skip'
            ))

    add_wireframe(V_PLUS * scale, FACES_PLUS, 'cyan', 'T+ edges')
    add_wireframe(V_MINUS * scale, FACES_MINUS, 'magenta', 'T- edges')

    # Add vertex markers
    vertex_names_plus = ['R', 'G', 'B', 'W']
    vertex_colors_plus = ['red', 'green', 'blue', 'white']

    for i, (name, color) in enumerate(zip(vertex_names_plus, vertex_colors_plus)):
        v = V_PLUS[i] * scale
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers+text',
            marker=dict(size=8, color=color, line=dict(color='black', width=1)),
            text=[name],
            textposition='top center',
            textfont=dict(size=12, color='white'),
            name=f'T+ {name}',
            showlegend=False,
            hoverinfo='name'
        ))

    vertex_names_minus = ['R̄', 'Ḡ', 'B̄', 'W̄']
    vertex_colors_minus = ['darkred', 'darkgreen', 'darkblue', 'gray']

    for i, (name, color) in enumerate(zip(vertex_names_minus, vertex_colors_minus)):
        v = V_MINUS[i] * scale
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=6, color=color, line=dict(color='black', width=1)),
            name=f'T- {name}',
            showlegend=False,
            hoverinfo='name'
        ))

    # Add center marker
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(
            size=10,
            color='yellow',
            symbol='diamond',
            line=dict(color='black', width=2)
        ),
        name='Center (ρ_vac → 0)',
        showlegend=True,
        hoverinfo='name'
    ))

    # Layout
    extent = 0.7 * scale
    fig.update_layout(
        title=dict(
            text='Theorem 5.1.2: Vacuum Energy Density on Stella Octangula<br>'
                 '<sub>ρ_vac(x) = λ v_χ(x)⁴ mapped to triangular faces | '
                 'Two interpenetrating tetrahedra (T+ cyan, T- magenta)</sub>',
            x=0.5,
            font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 30)',
                      gridcolor='rgb(50, 50, 60)',
                      showbackground=True),
            yaxis=dict(title='y', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 30)',
                      gridcolor='rgb(50, 50, 60)',
                      showbackground=True),
            zaxis=dict(title='z', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 30)',
                      gridcolor='rgb(50, 50, 60)',
                      showbackground=True),
            aspectmode='cube',
            bgcolor='rgb(20, 20, 30)',
            camera=dict(
                eye=dict(x=1.5, y=1.5, z=1.2),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.9)',
            font=dict(size=11)
        ),
        paper_bgcolor='rgb(30, 30, 40)',
        margin=dict(l=0, r=0, t=80, b=0),
        width=1000,
        height=800
    )

    return fig, (log_rho_min, log_rho_max)


def export_static_views(fig, log_range):
    """Export static PNG images from multiple camera angles."""
    from PIL import Image, ImageDraw, ImageFont

    print("\n" + "="*60)
    print("Exporting Static Views")
    print("="*60)

    # Remove title for cleaner images
    fig.update_layout(title=None, margin=dict(l=0, r=0, t=0, b=0))

    # Camera views
    views = [
        (dict(eye=dict(x=1.8, y=1.8, z=1.2), up=dict(x=0, y=0, z=1)),
         '(a) Isometric view'),
        (dict(eye=dict(x=0, y=0, z=2.5), up=dict(x=0, y=1, z=0)),
         '(b) Top view (Z axis)'),
        (dict(eye=dict(x=2.5, y=0, z=0), up=dict(x=0, y=0, z=1)),
         '(c) Side view (X axis)'),
    ]

    # Output paths
    plots_dir = os.path.join(os.path.dirname(__file__), '..', 'plots')
    plots_dir = os.path.normpath(plots_dir)
    os.makedirs(plots_dir, exist_ok=True)

    panel_paths = []
    panel_width = 800
    panel_height = 700

    for i, (camera, title) in enumerate(views):
        fig.update_layout(
            scene_camera=camera,
            width=panel_width,
            height=panel_height
        )

        temp_path = f'/tmp/stella_vacuum_panel_{i}.png'
        print(f"Exporting {title}...")
        fig.write_image(temp_path, scale=2)
        panel_paths.append((temp_path, title))

    # Combine into multi-panel figure
    print("Combining panels...")
    images = [Image.open(p[0]) for p in panel_paths]

    # 3-panel horizontal layout
    gap = 20
    title_height = 100
    combined_width = sum(img.width for img in images) + gap * 2
    combined_height = images[0].height + title_height + 80

    combined = Image.new('RGB', (combined_width, combined_height), 'white')
    draw = ImageDraw.Draw(combined)

    # Try to load a font
    try:
        title_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 28)
        subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 20)
        info_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 16)
    except (IOError, OSError):
        title_font = ImageFont.load_default()
        subtitle_font = ImageFont.load_default()
        info_font = ImageFont.load_default()

    # Main title
    main_title = "Theorem 5.1.2: Vacuum Energy Density Mapped to Stella Octangula"
    bbox = draw.textbbox((0, 0), main_title, font=title_font)
    title_x = (combined_width - (bbox[2] - bbox[0])) // 2
    draw.text((title_x, 15), main_title, fill='black', font=title_font)

    # Subtitle
    subtitle = f"rho_vac(x) = lambda * v_chi(x)^4  |  Range: 10^{log_range[0]:.1f} to 10^{log_range[1]:.1f} GeV^4"
    bbox = draw.textbbox((0, 0), subtitle, font=info_font)
    sub_x = (combined_width - (bbox[2] - bbox[0])) // 2
    draw.text((sub_x, 50), subtitle, fill='gray', font=info_font)

    # Paste panels and add subtitles
    x_offset = 0
    for i, (img, (path, panel_title)) in enumerate(zip(images, panel_paths)):
        combined.paste(img, (x_offset, title_height))

        # Panel subtitle
        bbox = draw.textbbox((0, 0), panel_title, font=subtitle_font)
        sub_x = x_offset + (img.width - (bbox[2] - bbox[0])) // 2
        draw.text((sub_x, title_height - 25), panel_title, fill='black', font=subtitle_font)

        x_offset += img.width + gap

    # Save
    output_path = os.path.join(plots_dir, 'theorem_5_1_2_vacuum_energy_stella_mapped.png')
    combined.save(output_path, dpi=(150, 150))
    print(f"Saved combined figure to {output_path}")

    # Cleanup
    for path, _ in panel_paths:
        os.remove(path)

    return output_path


def main():
    """Main entry point."""
    import sys
    import plotly.io as pio

    print("="*70)
    print("Theorem 5.1.2: Vacuum Energy Mapped to Stella Octangula")
    print("="*70)
    print()
    print("Key physics:")
    print("  - Stella octangula = two interpenetrating tetrahedra (T+ and T-)")
    print("  - NOT an octahedron! (8 vertices, chi=4, not 6 vertices)")
    print("  - Vacuum energy: rho_vac(x) = lambda * v_chi(x)^4")
    print("  - Color shows energy density on each triangular face")
    print("  - Phase cancellation: energy vanishes at center")
    print()

    # Create visualization
    fig, log_range = create_stella_vacuum_energy_visualization(subdivisions=30)

    # Check for export flag
    if '--export' in sys.argv:
        export_static_views(fig, log_range)
        return

    # Generate interactive HTML
    html_content = pio.to_html(fig, include_plotlyjs=True, full_html=True)

    # Inject info overlay
    info_script = """
    <div id="physics-info" style="position: fixed; bottom: 10px; left: 10px;
         background: rgba(0,0,0,0.9); color: white; padding: 15px;
         border-radius: 8px; font-family: sans-serif; font-size: 12px;
         max-width: 320px; z-index: 1000; border: 1px solid #444;">
        <strong style="color: #ffd700; font-size: 14px;">Stella Octangula Geometry</strong><br><br>
        <span style="color: #00ffff;">T+ tetrahedron</span> (cyan edges)<br>
        <span style="color: #ff00ff;">T- tetrahedron</span> (magenta edges)<br><br>
        <strong>Vacuum Energy:</strong><br>
        rho_vac(x) = lambda * v_chi(x)^4<br><br>
        <strong style="color: #ffff00;">Yellow</strong> = High energy (near vertices)<br>
        <strong style="color: #0d0887;">Blue</strong> = Low energy (center)<br><br>
        <em>Phase cancellation (1 + omega + omega^2 = 0)<br>
        causes rho_vac -> 0 at the center</em>
    </div>
    <div id="camera-info" style="position: fixed; top: 10px; right: 10px;
         background: rgba(255,255,255,0.95); padding: 10px; border: 1px solid #ccc;
         border-radius: 5px; font-family: monospace; font-size: 11px; z-index: 1000;">
        <strong>Rotate to explore!</strong><br>
        <span id="camera-values">Drag to rotate</span>
    </div>
    <script>
    document.addEventListener('DOMContentLoaded', function() {
        var plotDiv = document.getElementsByClassName('plotly-graph-div')[0];
        if (plotDiv) {
            plotDiv.on('plotly_relayout', function(eventData) {
                if (eventData['scene.camera']) {
                    var cam = eventData['scene.camera'];
                    var eye = cam.eye || {x: 1.5, y: 1.5, z: 1.2};
                    var info = 'eye: (' + eye.x.toFixed(2) + ', ' + eye.y.toFixed(2) + ', ' + eye.z.toFixed(2) + ')';
                    document.getElementById('camera-values').innerHTML = info;
                }
            });
        }
    });
    </script>
    """

    html_content = html_content.replace('</body>', info_script + '</body>')

    # Save HTML
    html_path = '/tmp/theorem_5_1_2_vacuum_energy_stella.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    print(f"\nSaved interactive visualization to: {html_path}")

    # Open in browser
    import webbrowser
    print("Opening in browser...")
    webbrowser.open(f'file://{html_path}')

    print("\nDone! The vacuum energy is now mapped directly onto the stella's faces.")
    print("Yellow regions = high energy (near vertices)")
    print("Blue regions = low energy (approaches zero at center)")


if __name__ == "__main__":
    main()
