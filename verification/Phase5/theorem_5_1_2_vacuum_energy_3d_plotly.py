#!/usr/bin/env python3
"""
Theorem 5.1.2: Vacuum Energy Density - Interactive 3D Plotly Visualization
============================================================================

Stella octangula wireframe with vacuum energy slice.

Author: Verification Suite
Date: February 2026
"""

import numpy as np
import plotly.graph_objects as go
import os

# Stella octangula vertices (two interpenetrating tetrahedra)
# T+ tetrahedron
V_PLUS = np.array([
    [+1, +1, +1],
    [+1, -1, -1],
    [-1, +1, -1],
    [-1, -1, +1],
]) / np.sqrt(3)

# T- tetrahedron
V_MINUS = np.array([
    [-1, -1, -1],
    [-1, +1, +1],
    [+1, -1, +1],
    [+1, +1, -1],
]) / np.sqrt(3)

EDGES = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]


# =============================================================================
# CORE FIELD FUNCTIONS
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """
    Vectorized pressure function P_c(x) for 3D grids.

    P_c(x) = 1/(|x - x_c|² + ε²)

    This represents the amplitude modulation from geometric opposition
    at color vertex position x_c.
    """
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_grid(X, Y, Z, a0=A0, epsilon=EPSILON):
    """
    Compute the total chiral field χ_total on a 3D grid.

    χ_total(x) = Σ_c a₀ P_c(x) exp(iφ_c)

    where c ∈ {R, G, B} and φ_c = 0, 2π/3, 4π/3
    """
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def position_dependent_vev(X, Y, Z, v_higgs=HIGGS_VEV, a0=A0, epsilon=EPSILON):
    """
    Compute position-dependent VEV: v_χ(x) = v × |χ_total(x)|/|χ_total|_max

    This captures how the effective Higgs VEV varies with position due to
    the SU(3) phase structure. At the center, v_χ → 0 due to phase cancellation.
    """
    chi_total = total_chiral_field_grid(X, Y, Z, a0, epsilon)
    chi_mag = np.abs(chi_total)

    # Normalize by maximum value
    chi_max = np.max(chi_mag)
    if chi_max > 0:
        normalized = chi_mag / chi_max
    else:
        normalized = chi_mag

    return v_higgs * normalized


def vacuum_energy_density(X, Y, Z, lambda_quartic=HIGGS_QUARTIC,
                         v_higgs=HIGGS_VEV, a0=A0, epsilon=EPSILON):
    """
    Compute vacuum energy density: ρ_vac(x) = λ × v_χ(x)⁴

    This is the key result: vacuum energy density is position-dependent
    and vanishes at the stella octangula center where phase cancellation
    makes v_χ(x) → 0.

    Returns values in GeV⁴.
    """
    v_chi = position_dependent_vev(X, Y, Z, v_higgs, a0, epsilon)
    return lambda_quartic * v_chi**4


def log_vacuum_energy(X, Y, Z, **kwargs):
    """
    Compute log₁₀(ρ_vac) for visualization purposes.
    Uses floor value for very small densities to avoid log(0).
    """
    rho = vacuum_energy_density(X, Y, Z, **kwargs)
    # Set minimum to avoid log(0)
    rho_min = 1e-20  # GeV⁴
    rho_clipped = np.maximum(rho, rho_min)
    return np.log10(rho_clipped)


# =============================================================================
# STELLA OCTANGULA VISUALIZATION
# =============================================================================

def create_stella_traces():
    """
    Create Plotly traces for stella octangula wireframe.

    The stella octangula is two interpenetrating tetrahedra (T+ and T-),
    NOT an octahedron. This is geometrically and topologically distinct.

    - 8 vertices (4 + 4)
    - 12 edges (6 + 6)
    - Euler characteristic χ = 4 (two S², each with χ=2)
    """
    traces = []

    # T+ tetrahedron edges (cyan/blue)
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
            line=dict(color='cyan', width=4),
            showlegend=False,
            hoverinfo='skip'
        ))

    # T- tetrahedron edges (magenta/red)
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
            line=dict(color='magenta', width=4),
            showlegend=False,
            hoverinfo='skip'
        ))

    # Color vertices for T+ (RGB + White)
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'white'}
    for name, v in VERTICES_PLUS.items():
        traces.append(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=8, color=colors_map[name],
                       line=dict(color='black', width=1)),
            name=f'T+ {name}',
            hoverinfo='name'
        ))

    # T- vertices (anticolors)
    anticolors = {'R_bar': 'darkred', 'G_bar': 'darkgreen',
                  'B_bar': 'darkblue', 'W_bar': 'gray'}
    for name, v in VERTICES_MINUS.items():
        traces.append(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=6, color=anticolors[name],
                       line=dict(color='black', width=1)),
            name=f'T- {name.replace("_bar", "")}',
            hoverinfo='name',
            showlegend=False
        ))

    # Origin marker (where vacuum energy vanishes)
    traces.append(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=12, color='yellow',
                   line=dict(color='black', width=2),
                   symbol='diamond'),
        name='Center (rho_vac = 0)',
        hoverinfo='name'
    ))

    return traces


# =============================================================================
# ISOSURFACE CREATION
# =============================================================================

def create_isosurface_trace(field_3d, x_grid, y_grid, z_grid, level,
                           color, opacity, name, colorscale=None,
                           intensity=None, showscale=False):
    """
    Create a Plotly Mesh3d trace for an isosurface using marching cubes.

    Parameters:
    -----------
    field_3d : 3D array of field values
    x_grid, y_grid, z_grid : 1D arrays of grid coordinates
    level : isosurface level
    color : color for single-color surface
    opacity : surface opacity
    name : trace name for legend
    colorscale : optional colorscale for intensity-based coloring
    intensity : optional per-vertex intensity values
    showscale : whether to show colorbar
    """
    try:
        verts, faces, normals, values = measure.marching_cubes(
            field_3d, level=level, allow_degenerate=False
        )

        # Scale vertices from grid indices to real coordinates
        n_x, n_y, n_z = len(x_grid), len(y_grid), len(z_grid)
        verts_scaled = np.zeros_like(verts)
        verts_scaled[:, 0] = x_grid[0] + verts[:, 0] * (x_grid[-1] - x_grid[0]) / (n_x - 1)
        verts_scaled[:, 1] = y_grid[0] + verts[:, 1] * (y_grid[-1] - y_grid[0]) / (n_y - 1)
        verts_scaled[:, 2] = z_grid[0] + verts[:, 2] * (z_grid[-1] - z_grid[0]) / (n_z - 1)

        mesh_kwargs = dict(
            x=verts_scaled[:, 0],
            y=verts_scaled[:, 1],
            z=verts_scaled[:, 2],
            i=faces[:, 0],
            j=faces[:, 1],
            k=faces[:, 2],
            opacity=opacity,
            name=name,
            showlegend=True
        )

        if intensity is not None and colorscale is not None:
            # Interpolate intensity at vertex positions
            interp = RegularGridInterpolator(
                (x_grid, y_grid, z_grid), intensity,
                method='linear', bounds_error=False, fill_value=np.nanmin(intensity)
            )
            vertex_intensity = interp(verts_scaled)
            mesh_kwargs['intensity'] = vertex_intensity
            mesh_kwargs['colorscale'] = colorscale
            mesh_kwargs['showscale'] = showscale
            mesh_kwargs['colorbar'] = dict(
                title=dict(text='log10(rho_vac)', side='right')
            ) if showscale else None
        else:
            mesh_kwargs['color'] = color

        return go.Mesh3d(**mesh_kwargs)

    except (ValueError, RuntimeError) as e:
        print(f"Warning: Could not create isosurface at level {level}: {e}")
        return None


def create_vacuum_energy_visualization():
    """
    Create the full interactive 3D visualization of vacuum energy density
    mapped onto the stella octangula geometry.
    """
    print("Computing vacuum energy density field...")

    # Grid parameters
    extent = 0.85  # Slightly larger than stella to show complete structure
    n_grid = 70    # Resolution

    x_grid = np.linspace(-extent, extent, n_grid)
    y_grid = np.linspace(-extent, extent, n_grid)
    z_grid = np.linspace(-extent, extent, n_grid)
    X3d, Y3d, Z3d = np.meshgrid(x_grid, y_grid, z_grid, indexing='ij')

    # Compute vacuum energy density
    rho_vac = vacuum_energy_density(X3d, Y3d, Z3d)
    log_rho = np.log10(np.maximum(rho_vac, 1e-20))

    # Find range for isosurfaces
    log_rho_max = np.max(log_rho)
    log_rho_min = np.min(log_rho[log_rho > -19])  # Exclude floor values

    print(f"  Vacuum energy range: 10^{log_rho_min:.1f} to 10^{log_rho_max:.1f} GeV^4")

    # Create figure
    fig = go.Figure()

    # Define isosurface levels in log space
    # Show several shells from low to high energy density
    log_levels = np.linspace(log_rho_min + 1, log_rho_max - 0.5, 5)

    # Plasma colorscale (good for energy visualization)
    colorscale = [
        [0.0, 'rgb(13, 8, 135)'],    # Deep blue (low energy)
        [0.25, 'rgb(126, 3, 168)'],  # Purple
        [0.5, 'rgb(203, 71, 119)'],  # Pink
        [0.75, 'rgb(248, 149, 64)'], # Orange
        [1.0, 'rgb(240, 249, 33)']   # Yellow (high energy)
    ]

    # Opacities (outer shells more transparent)
    opacities = [0.15, 0.2, 0.25, 0.3, 0.4]

    print("Creating isosurfaces...")
    for i, (log_level, opacity) in enumerate(zip(log_levels, opacities)):
        level_value = 10**log_level
        name = f'rho = 10^{log_level:.1f} GeV^4'

        trace = create_isosurface_trace(
            rho_vac, x_grid, y_grid, z_grid,
            level=level_value,
            color=None,
            opacity=opacity,
            name=name,
            colorscale=colorscale,
            intensity=log_rho,
            showscale=(i == len(log_levels) - 1)  # Only show colorbar for last
        )

        if trace:
            fig.add_trace(trace)
            print(f"  Added isosurface at log(rho) = {log_level:.2f}")

    # Add stella octangula wireframe
    print("Adding stella octangula wireframe...")
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Configure layout
    fig.update_layout(
        title=dict(
            text='Theorem 5.1.2: Vacuum Energy Density on Stella Octangula<br>'
                 '<sub>Isosurfaces of rho_vac(x) = lambda * v_chi(x)^4 | '
                 'Vanishes at center due to SU(3) phase cancellation</sub>',
            x=0.5,
            font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 20)',
                      gridcolor='rgb(50, 50, 50)'),
            yaxis=dict(title='y', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 20)',
                      gridcolor='rgb(50, 50, 50)'),
            zaxis=dict(title='z', range=[-extent, extent],
                      backgroundcolor='rgb(20, 20, 20)',
                      gridcolor='rgb(50, 50, 50)'),
            aspectmode='cube',
            bgcolor='rgb(20, 20, 20)',
            camera=dict(
                eye=dict(x=1.8, y=1.8, z=1.5),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.85)',
            font=dict(size=10)
        ),
        paper_bgcolor='rgb(30, 30, 30)',
        margin=dict(l=0, r=0, t=80, b=0),
        width=1000,
        height=800
    )

    return fig


def export_static_views():
    """
    Export static PNG images from multiple camera angles.
    """
    from PIL import Image, ImageDraw, ImageFont

    print("\n" + "="*60)
    print("Exporting Static Views")
    print("="*60)

    fig = create_vacuum_energy_visualization()

    # Remove title for cleaner images
    fig.update_layout(title=None, margin=dict(l=0, r=0, t=0, b=0))

    # Camera views
    views = [
        (dict(eye=dict(x=1.8, y=1.8, z=1.5), up=dict(x=0, y=0, z=1)),
         '(a) Isometric view'),
        (dict(eye=dict(x=0, y=0, z=3.0), up=dict(x=0, y=1, z=0)),
         '(b) Top view (XY plane)'),
        (dict(eye=dict(x=0, y=3.0, z=0), up=dict(x=0, y=0, z=1)),
         '(c) Front view (XZ plane)'),
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

        temp_path = f'/tmp/vacuum_energy_panel_{i}.png'
        print(f"Exporting {title}...")
        fig.write_image(temp_path, scale=2)
        panel_paths.append((temp_path, title))

    # Combine into multi-panel figure
    print("Combining panels...")
    images = [Image.open(p[0]) for p in panel_paths]

    # 3-panel horizontal layout
    gap = 20
    title_height = 80
    combined_width = sum(img.width for img in images) + gap * 2
    combined_height = images[0].height + title_height + 60

    combined = Image.new('RGB', (combined_width, combined_height), 'white')
    draw = ImageDraw.Draw(combined)

    # Try to load a font
    try:
        title_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 32)
        subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 24)
    except (IOError, OSError):
        title_font = ImageFont.load_default()
        subtitle_font = ImageFont.load_default()

    # Main title
    main_title = "Theorem 5.1.2: Vacuum Energy Density Isosurfaces on Stella Octangula"
    bbox = draw.textbbox((0, 0), main_title, font=title_font)
    title_x = (combined_width - (bbox[2] - bbox[0])) // 2
    draw.text((title_x, 15), main_title, fill='black', font=title_font)

    # Paste panels and add subtitles
    x_offset = 0
    for i, (img, (path, subtitle)) in enumerate(zip(images, panel_paths)):
        combined.paste(img, (x_offset, title_height))

        # Subtitle
        bbox = draw.textbbox((0, 0), subtitle, font=subtitle_font)
        sub_x = x_offset + (img.width - (bbox[2] - bbox[0])) // 2
        draw.text((sub_x, title_height - 30), subtitle, fill='black', font=subtitle_font)

        x_offset += img.width + gap

    # Save
    output_path = os.path.join(plots_dir, 'theorem_5_1_2_vacuum_energy_3d_isosurfaces.png')
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
    print("Theorem 5.1.2: Vacuum Energy Density - 3D Plotly Visualization")
    print("="*70)
    print()
    print("Key physics:")
    print("  - Vacuum energy: rho_vac(x) = lambda * v_chi(x)^4")
    print("  - Position-dependent VEV from SU(3) phase structure")
    print("  - Phase cancellation: 1 + omega + omega^2 = 0")
    print("  - Result: rho_vac -> 0 at stella octangula center")
    print()

    # Check for export flag
    if '--export' in sys.argv:
        export_static_views()
        return

    # Create interactive visualization
    fig = create_vacuum_energy_visualization()

    # Generate HTML with camera position display
    html_content = pio.to_html(fig, include_plotlyjs=True, full_html=True)

    # Inject camera position display script
    camera_script = """
    <div id="camera-info" style="position: fixed; top: 10px; right: 10px;
         background: rgba(255,255,255,0.95); padding: 12px; border: 1px solid #ccc;
         border-radius: 5px; font-family: monospace; font-size: 12px; z-index: 1000;
         box-shadow: 0 2px 5px rgba(0,0,0,0.2);">
        <strong>Theorem 5.1.2: Vacuum Energy</strong><br>
        <span style="color: #666;">Rotate to explore!</span><br><br>
        <strong>Camera:</strong><br>
        <span id="camera-values">eye: (1.80, 1.80, 1.50)</span>
    </div>
    <div id="physics-info" style="position: fixed; bottom: 10px; left: 10px;
         background: rgba(0,0,0,0.85); color: white; padding: 12px;
         border-radius: 5px; font-family: sans-serif; font-size: 11px;
         max-width: 300px; z-index: 1000;">
        <strong style="color: #ffd700;">Key Result:</strong><br>
        Vacuum energy rho_vac = lambda * v_chi^4<br>
        vanishes at center due to<br>
        SU(3) phase cancellation:<br>
        <span style="color: #00ffff;">1 + omega + omega^2 = 0</span>
    </div>
    <script>
    document.addEventListener('DOMContentLoaded', function() {
        var plotDiv = document.getElementsByClassName('plotly-graph-div')[0];
        if (plotDiv) {
            plotDiv.on('plotly_relayout', function(eventData) {
                if (eventData['scene.camera']) {
                    var cam = eventData['scene.camera'];
                    var eye = cam.eye || {x: 1.8, y: 1.8, z: 1.5};
                    var info = 'eye: (' + eye.x.toFixed(2) + ', ' + eye.y.toFixed(2) + ', ' + eye.z.toFixed(2) + ')';
                    document.getElementById('camera-values').innerHTML = info;
                }
            });
        }
    });
    </script>
    """

    html_content = html_content.replace('</body>', camera_script + '</body>')

    # Save HTML
    html_path = '/tmp/theorem_5_1_2_vacuum_energy_3d.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    print(f"\nSaved interactive visualization to: {html_path}")

    # Open in browser
    import webbrowser
    print("Opening in browser...")
    webbrowser.open(f'file://{html_path}')

    print("\nDone! Rotate the visualization to explore the vacuum energy structure.")
    print("The yellow diamond at the center marks where rho_vac = 0.")


if __name__ == "__main__":
    main()
