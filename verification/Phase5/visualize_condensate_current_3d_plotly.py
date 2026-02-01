#!/usr/bin/env python3
"""
3D Visualization: Condensate Current and Particle Creation (Plotly)
====================================================================

Shows the chiral condensate phase θ as a 3D "spiral staircase" surface.

- Surface height = phase θ
- Surface color blends: Hue = phase, Brightness = |J_5| ∝ 1/r
- Bright near core (strong current), dark far (weak current)
- Vortex core (r=0) = particle location (topological defect)

Reference: Theorem 5.3.1 (Torsion from Chiral Current)
"""

import numpy as np
import plotly.graph_objects as go
from colorsys import hsv_to_rgb

def main():
    # Create polar grid (extend close to core for visible white region)
    nr, nphi = 100, 150
    r = np.linspace(0.1, 2.0, nr)
    phi = np.linspace(0, 2 * np.pi, nphi)
    R, PHI = np.meshgrid(r, phi)

    # Convert to Cartesian
    X = R * np.cos(PHI)
    Y = R * np.sin(PHI)

    # Phase field: θ = φ (azimuthal angle) - creates helical surface
    THETA = PHI

    # Field amplitude |χ| → 0 at vortex core (standard vortex physics)
    # This creates a "funnel" effect - the surface dips toward the core
    # Use tanh profile: |χ|/v_χ = tanh(r/ξ) where ξ is coherence length
    xi = 0.3  # Coherence length (controls width of funnel)
    amplitude = np.tanh(R / xi)  # 0 at r=0, approaches 1 far from core

    # Height combines phase winding with amplitude profile
    # The surface "funnels" toward the core as amplitude drops
    Z = THETA * amplitude

    # =========================================================================
    # Create color array blending phase (hue) with current magnitude (brightness)
    # |J_5| ∝ 1/r: bright (white) near core, dark far away
    # =========================================================================

    # Current magnitude: use linear falloff for visible gradient across surface
    # (1/r is physically correct but too steep visually)
    r_min, r_max = 0.1, 2.0
    # Linear: white at r_min, black at r_max
    current_mag_norm = 1.0 - (R - r_min) / (r_max - r_min)
    current_mag_norm = np.clip(current_mag_norm, 0, 1)

    # Phase normalized to [0, 1] for hue
    hue = (THETA / (2 * np.pi)) % 1.0

    # Create RGB colors - SAME as 2D version:
    # White (high current) = low saturation, high value
    # Black (low current) = high saturation, low value
    colors = np.zeros((nphi, nr, 3))

    for i in range(nphi):
        for j in range(nr):
            h = hue[i, j]
            c = current_mag_norm[i, j]
            # Exactly like 2D version:
            s = 1.0 - c  # Low saturation near core (white)
            v = c        # High value near core, black at edge
            rgb = hsv_to_rgb(h, s, v)
            colors[i, j] = rgb

    # Convert to plotly color format (list of rgb strings)
    def rgb_to_str(rgb):
        return f'rgb({int(rgb[0]*255)},{int(rgb[1]*255)},{int(rgb[2]*255)})'

    # For plotly surface, we need surfacecolor as a 2D array
    # We'll create a custom colorscale based on a combined value
    # Simpler approach: use surfacecolor with a combined metric

    # Combined value for coloring: encode both phase and magnitude
    # We'll use a trick: create the surface color directly

    # Convert colors array to format plotly can use
    color_strings = [[rgb_to_str(colors[i, j]) for j in range(nr)] for i in range(nphi)]

    # Create figure
    fig = go.Figure()

    # =========================================================================
    # Helical surface with gradient coloring
    # =========================================================================
    # Plotly doesn't directly support per-vertex RGB, so we use a workaround
    # by creating a custom surfacecolor array

    # Create a combined scalar field for coloring
    # Map phase to [0, 0.5] and current to brightness modification
    combined = hue + 0.001 * current_mag_norm  # Small perturbation to preserve hue order

    # Custom colorscale that varies in both hue and brightness
    # We'll create a 2D colorscale approximation
    n_colors = 100
    colorscale = []
    for i in range(n_colors + 1):
        t = i / n_colors
        # Hue cycles with t
        h = t
        # For the colorscale, we show full saturation colors
        # The actual brightness variation comes from the surfacecolor values
        s = 0.8
        v = 0.9
        rgb = hsv_to_rgb(h, s, v)
        colorscale.append([t, f'rgb({int(rgb[0]*255)},{int(rgb[1]*255)},{int(rgb[2]*255)})'])

    # For proper blending, we need to create the surface differently
    # Let's use a mesh3d approach with explicit vertex colors

    # Flatten arrays for mesh3d
    x_flat = X.flatten()
    y_flat = Y.flatten()
    z_flat = Z.flatten()
    colors_flat = colors.reshape(-1, 3)

    # Create triangular mesh indices
    i_indices = []
    j_indices = []
    k_indices = []

    for i in range(nphi - 1):
        for j in range(nr - 1):
            # Two triangles per grid cell
            idx = i * nr + j
            idx_right = i * nr + (j + 1)
            idx_up = (i + 1) * nr + j
            idx_diag = (i + 1) * nr + (j + 1)

            # Triangle 1
            i_indices.append(idx)
            j_indices.append(idx_right)
            k_indices.append(idx_up)

            # Triangle 2
            i_indices.append(idx_right)
            j_indices.append(idx_diag)
            k_indices.append(idx_up)

    # Vertex colors as plotly color strings
    vertex_colors = [rgb_to_str(c) for c in colors_flat]

    # Use intensity for coloring with custom colorscale
    intensity = (hue.flatten() + current_mag_norm.flatten() * 0.0001) % 1.0

    # Create custom colorscale with brightness variation baked in
    # Actually, let's try a different approach - use facecolor

    # Simpler: use Surface with a modified colorscale
    # Create surfacecolor that encodes both phase and brightness

    # Value that varies with both: use HSV-inspired encoding
    # surfacecolor = phase (for hue), then modify colorscale based on r

    # Let's try the simplest working approach:
    # Two overlapping surfaces - one for phase color, one for brightness

    # Actually, the cleanest solution: compute face colors directly

    fig.add_trace(go.Mesh3d(
        x=x_flat,
        y=y_flat,
        z=z_flat,
        i=i_indices,
        j=j_indices,
        k=k_indices,
        vertexcolor=vertex_colors,
        opacity=0.92,
        name='Phase θ & Current |J₅|',
        hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>θ: %{z:.2f}<extra></extra>',
        flatshading=False,
    ))

    # =========================================================================
    # PARTICLE LOCATION - Vortex core (topological defect)
    # =========================================================================
    z_core = np.linspace(-0.2, 2*np.pi + 0.2, 50)
    x_core = np.zeros_like(z_core)
    y_core = np.zeros_like(z_core)

    fig.add_trace(go.Scatter3d(
        x=x_core, y=y_core, z=z_core,
        mode='lines',
        line=dict(color='red', width=15),
        name='Particle (vortex core)',
        hovertemplate='Topological defect<br>Phase undefined at r=0<extra></extra>',
    ))

    # Spheres along core
    z_spheres = [0.2, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi - 0.2]
    fig.add_trace(go.Scatter3d(
        x=[0]*len(z_spheres),
        y=[0]*len(z_spheres),
        z=z_spheres,
        mode='markers',
        marker=dict(size=8, color='red', line=dict(color='darkred', width=2)),
        showlegend=False,
        hovertemplate='Particle<extra></extra>',
    ))

    # =========================================================================
    # TOPOLOGICAL WINDING LOOP - Shows phase completes full 2π cycle
    # =========================================================================
    # A ring around the core where you can see all phase colors
    # This demonstrates: going around once = phase winds by 2π = winding number 1
    r_loop = 0.6  # Radius of the demonstration loop
    n_loop = 100
    phi_loop = np.linspace(0, 2*np.pi, n_loop)
    x_loop = r_loop * np.cos(phi_loop)
    y_loop = r_loop * np.sin(phi_loop)
    # Height on the surface: z = θ * amplitude = φ * tanh(r/ξ)
    amplitude_loop = np.tanh(r_loop / xi)
    z_loop = phi_loop * amplitude_loop

    # Color the loop by phase to show complete cycle
    loop_colors = phi_loop / (2*np.pi)  # 0 to 1 for colorscale

    # Create colorscale matching the phase colors
    phase_colorscale = [
        [0.0, '#1a0533'], [0.1, '#4a148c'], [0.2, '#1565c0'],
        [0.3, '#00897b'], [0.4, '#7cb342'], [0.5, '#fdd835'],
        [0.6, '#fb8c00'], [0.7, '#e53935'], [0.8, '#ad1457'],
        [0.9, '#6a1b9a'], [1.0, '#1a0533']
    ]

    fig.add_trace(go.Scatter3d(
        x=x_loop, y=y_loop, z=z_loop,
        mode='lines+markers',
        line=dict(color='white', width=8),
        marker=dict(
            size=5,
            color=loop_colors,
            colorscale=phase_colorscale,
            showscale=False,
        ),
        name='Winding loop (2π)',
        hovertemplate='Topological winding<br>Phase cycles through 2π<extra></extra>',
    ))

    # Add arrow to show direction of winding
    arrow_idx = n_loop // 4  # Position arrow at 90 degrees
    fig.add_trace(go.Cone(
        x=[x_loop[arrow_idx]],
        y=[y_loop[arrow_idx]],
        z=[z_loop[arrow_idx]],
        u=[-np.sin(phi_loop[arrow_idx]) * 0.2],
        v=[np.cos(phi_loop[arrow_idx]) * 0.2],
        w=[amplitude_loop * 0.2],
        sizemode='absolute',
        sizeref=0.15,
        anchor='tail',
        colorscale=[[0, 'yellow'], [1, 'yellow']],
        showscale=False,
        name='Winding direction',
        hovertemplate='Phase increases this direction<extra></extra>',
    ))

    # =========================================================================
    # Layout
    # =========================================================================
    fig.update_layout(
        title=dict(
            text='Chiral Vortex: Phase Winding (twist) × Amplitude (funnel) → Particle at Core',
            font=dict(size=14),
            x=0.5,
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-2.2, 2.2]),
            yaxis=dict(title='y', range=[-2.2, 2.2]),
            zaxis=dict(
                title='Phase θ',
                range=[-0.3, 2*np.pi + 0.3],
                tickvals=[0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi],
                ticktext=['0', 'π/2', 'π', '3π/2', '2π'],
            ),
            camera=dict(eye=dict(x=1.5, y=-1.5, z=1.0)),
            aspectmode='cube',
        ),
        legend=dict(
            x=0.02, y=0.98,
            bgcolor='rgba(255,255,255,0.9)',
            bordercolor='gray', borderwidth=1,
        ),
        margin=dict(l=0, r=0, t=50, b=0),
        annotations=[
            dict(
                text='<b>Topology creates the particle:</b><br>'
                     'Loop around core → phase winds 2π<br>'
                     'This winding cannot be removed<br>'
                     '∴ Particle is topologically protected',
                x=0.02, y=0.22,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=11),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=8,
                align='left',
            ),
            dict(
                text='<b>Surface encodes:</b><br>'
                     'Twist = Phase θ | Funnel = |χ| → 0<br>'
                     'Brightness = |J₅| (current)',
                x=0.02, y=0.05,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left',
            ),
        ],
    )

    # Save
    fig.write_html('plots/condensate_current_3d.html')
    fig.write_image('plots/condensate_current_3d_plotly.png', width=1200, height=900, scale=2)
    fig.write_image('plots/condensate_current_3d_plotly.pdf', width=1200, height=900)

    print("Saved: plots/condensate_current_3d.html (interactive)")
    print("Saved: plots/condensate_current_3d_plotly.png")
    print("Saved: plots/condensate_current_3d_plotly.pdf")

if __name__ == '__main__':
    main()
