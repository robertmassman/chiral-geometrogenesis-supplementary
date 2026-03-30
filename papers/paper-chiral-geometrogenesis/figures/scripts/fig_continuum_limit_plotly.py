#!/usr/bin/env python3
"""
Figure: Continuum Limit from Discrete Structure (Plotly version)
=================================================================

Two-panel figure showing how discrete stella octangula structure
connects to continuous SU(3) gauge theory.

Panel (a): A₂ root system derived from stella octangula weight differences
Panel (b): Discrete → Continuous limit visualization (a → 0)

Output:
- fig_continuum_limit.png
- fig_continuum_limit.pdf

Author: Chiral Geometrogenesis Project
Date: 2026-02-04
"""

import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from pathlib import Path

# Output directory
OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# COLOR SCHEME
# ============================================================================

COLOR_R = '#E74C3C'  # Red
COLOR_G = '#27AE60'  # Green
COLOR_B = '#3498DB'  # Blue
COLOR_RBAR = '#F1948A'  # Light red (anti-red)
COLOR_GBAR = '#82E0AA'  # Light green (anti-green)
COLOR_BBAR = '#85C1E9'  # Light blue (anti-blue)
COLOR_ROOT = '#2C3E50'  # Dark gray for root arrows

# ============================================================================
# PHYSICS DATA
# ============================================================================

def get_stella_weights():
    """Return the weight vectors for the stella octangula vertices."""
    sqrt3 = np.sqrt(3)
    weights = {
        'R': np.array([1/2, 1/(2*sqrt3)]),
        'G': np.array([-1/2, 1/(2*sqrt3)]),
        'B': np.array([0, -1/sqrt3]),
    }
    weights['R̄'] = -weights['R']
    weights['Ḡ'] = -weights['G']
    weights['B̄'] = -weights['B']
    return weights


def get_a2_roots():
    """Get the A₂ root system from weight differences."""
    weights = get_stella_weights()
    alpha1 = weights['R'] - weights['G']
    alpha2 = weights['G'] - weights['B']
    return alpha1, alpha2

# ============================================================================
# PANEL A: ROOT SYSTEM
# ============================================================================

def create_panel_a():
    """Create the A₂ root system panel."""
    weights = get_stella_weights()
    alpha1, alpha2 = get_a2_roots()
    weight_radius = 1 / np.sqrt(3)

    traces = []

    # Weight circle (dashed)
    theta = np.linspace(0, 2*np.pi, 100)
    traces.append(go.Scatter(
        x=weight_radius * np.cos(theta),
        y=weight_radius * np.sin(theta),
        mode='lines',
        line=dict(color='gray', width=1.2, dash='dash'),
        opacity=0.6,
        showlegend=False
    ))

    # Hexagon edges connecting adjacent weights
    weight_order = ['R', 'B̄', 'G', 'R̄', 'B', 'Ḡ']
    for i in range(6):
        w1 = weights[weight_order[i]]
        w2 = weights[weight_order[(i+1) % 6]]
        traces.append(go.Scatter(
            x=[w1[0], w2[0]], y=[w1[1], w2[1]],
            mode='lines',
            line=dict(color='gray', width=1),
            opacity=0.5,
            showlegend=False
        ))

    # R-G-B triangle (root edges)
    for (w1_name, w2_name) in [('G', 'R'), ('B', 'G'), ('B', 'R')]:
        w1, w2 = weights[w1_name], weights[w2_name]
        traces.append(go.Scatter(
            x=[w1[0], w2[0]], y=[w1[1], w2[1]],
            mode='lines',
            line=dict(color=COLOR_ROOT, width=2.5),
            opacity=0.9,
            showlegend=False
        ))

    # Weight vertices
    weight_colors = {
        'R': COLOR_R, 'G': COLOR_G, 'B': COLOR_B,
        'R̄': COLOR_RBAR, 'Ḡ': COLOR_GBAR, 'B̄': COLOR_BBAR
    }
    for name, w in weights.items():
        traces.append(go.Scatter(
            x=[w[0]], y=[w[1]],
            mode='markers+text',
            marker=dict(size=14, color=weight_colors[name],
                       line=dict(color='black', width=1.5)),
            text=[name],
            textposition='top right' if name in ['R', 'B'] else 'top left',
            textfont=dict(size=11, color='black'),
            showlegend=False
        ))

    # Origin
    traces.append(go.Scatter(
        x=[0], y=[0],
        mode='markers+text',
        marker=dict(size=10, color='white', line=dict(color='black', width=2)),
        text=['0'],
        textposition='top right',
        textfont=dict(size=10),
        showlegend=False
    ))

    # Simple root arrows α₁ and α₂
    arrow_scale = weight_radius

    # α₁ arrow
    traces.append(go.Scatter(
        x=[0, alpha1[0]*arrow_scale], y=[0, alpha1[1]*arrow_scale],
        mode='lines+text',
        line=dict(color=COLOR_ROOT, width=2.5),
        text=[None, 'α₁'],
        textposition='top right',
        textfont=dict(size=12, color=COLOR_ROOT),
        showlegend=False
    ))

    # α₂ arrow
    traces.append(go.Scatter(
        x=[0, alpha2[0]*arrow_scale], y=[0, alpha2[1]*arrow_scale],
        mode='lines+text',
        line=dict(color=COLOR_ROOT, width=2.5),
        text=[None, 'α₂'],
        textposition='top left',
        textfont=dict(size=12, color=COLOR_ROOT),
        showlegend=False
    ))

    return traces

# ============================================================================
# PANEL B: DISCRETE → CONTINUOUS LIMIT
# ============================================================================

def create_panel_b():
    """Create the continuum limit panel with controlled draw order."""
    weight_radius = 1 / np.sqrt(3)
    hue_offset = np.pi/6

    traces = []

    # --- Layer 1: Connections from finer to continuous (drawn first = bottom) ---
    n_intermediate = 18
    angles_intermediate = np.linspace(0, 2*np.pi, n_intermediate, endpoint=False) + np.pi/6
    r_intermediate = weight_radius * 0.75
    r_ring = weight_radius
    n_ring_points = 36
    ring_angles = np.linspace(0, 2*np.pi, n_ring_points, endpoint=False)

    for int_angle in angles_intermediate:
        x_int = r_intermediate * np.cos(int_angle)
        y_int = r_intermediate * np.sin(int_angle)
        for ring_angle in ring_angles:
            x_ring = r_ring * np.cos(ring_angle)
            y_ring = r_ring * np.sin(ring_angle)
            traces.append(go.Scatter(
                x=[x_int, x_ring], y=[y_int, y_ring],
                mode='lines',
                line=dict(color='gray', width=0.3),
                opacity=0.10,
                showlegend=False
            ))

    # --- Layer 2: Connections from discrete to finer ---
    r_discrete = weight_radius * 0.45
    discrete_angles = [np.pi/6, 5*np.pi/6, -np.pi/2, -5*np.pi/6, np.pi/2, -np.pi/6]

    for d_angle in discrete_angles:
        x_d = r_discrete * np.cos(d_angle)
        y_d = r_discrete * np.sin(d_angle)
        for int_angle in angles_intermediate:
            x_int = r_intermediate * np.cos(int_angle)
            y_int = r_intermediate * np.sin(int_angle)
            traces.append(go.Scatter(
                x=[x_d, x_int], y=[y_d, y_int],
                mode='lines',
                line=dict(color='gray', width=0.4),
                opacity=0.3,
                showlegend=False
            ))

    # --- Layer 3: Connections between discrete points ---
    for i in range(6):
        for j in range(i + 1, 6):
            angle1 = discrete_angles[i]
            angle2 = discrete_angles[j]
            x1, y1 = r_discrete * np.cos(angle1), r_discrete * np.sin(angle1)
            x2, y2 = r_discrete * np.cos(angle2), r_discrete * np.sin(angle2)
            traces.append(go.Scatter(
                x=[x1, x2], y=[y1, y2],
                mode='lines',
                line=dict(color='#2C3E50', width=1.2),
                opacity=0.7,
                showlegend=False
            ))

    # --- Layer 4: Continuous color ring ---
    r_outer = weight_radius * 1.08
    r_inner = weight_radius * 0.92

    for t in np.linspace(0, 2*np.pi, 72):
        t_shifted = (t - hue_offset) % (2*np.pi)
        if t_shifted < 2*np.pi/3:
            frac = t_shifted / (2*np.pi/3)
            color = f'rgba({int(230-100*frac)}, {int(76+100*frac)}, 51, 0.5)'
        elif t_shifted < 4*np.pi/3:
            frac = (t_shifted - 2*np.pi/3) / (2*np.pi/3)
            color = f'rgba({int(130-50*frac)}, {int(176-100*frac)}, {int(51+150*frac)}, 0.5)'
        else:
            frac = (t_shifted - 4*np.pi/3) / (2*np.pi/3)
            color = f'rgba({int(80+150*frac)}, 76, {int(201-150*frac)}, 0.5)'

        t_next = t + 2*np.pi/72
        traces.append(go.Scatter(
            x=[r_inner*np.cos(t), r_outer*np.cos(t), r_outer*np.cos(t_next),
               r_inner*np.cos(t_next), r_inner*np.cos(t)],
            y=[r_inner*np.sin(t), r_outer*np.sin(t), r_outer*np.sin(t_next),
               r_inner*np.sin(t_next), r_inner*np.sin(t)],
            mode='lines',
            fill='toself',
            fillcolor=color,
            line=dict(width=0),
            showlegend=False
        ))

    # --- Layer 5: Intermediate (finer) points ---
    for angle in angles_intermediate:
        x = r_intermediate * np.cos(angle)
        y = r_intermediate * np.sin(angle)

        a_norm = (angle - hue_offset) % (2*np.pi)
        if a_norm < 2*np.pi/3:
            frac = a_norm / (2*np.pi/3)
            color = f'rgb({int(230-130*frac)}, {int(76+130*frac)}, 51)'
        elif a_norm < 4*np.pi/3:
            frac = (a_norm - 2*np.pi/3) / (2*np.pi/3)
            color = f'rgb({int(100-50*frac)}, {int(206-130*frac)}, {int(51+150*frac)})'
        else:
            frac = (a_norm - 4*np.pi/3) / (2*np.pi/3)
            color = f'rgb({int(50+180*frac)}, 76, {int(201-150*frac)})'

        traces.append(go.Scatter(
            x=[x], y=[y],
            mode='markers',
            marker=dict(size=8, color=color, line=dict(color='black', width=0.5)),
            showlegend=False
        ))

    # --- Layer 6: Discrete points (on top) ---
    weight_colors_list = [COLOR_R, COLOR_G, COLOR_B, COLOR_RBAR, COLOR_GBAR, COLOR_BBAR]
    weight_names = ['R', 'G', 'B', 'R̄', 'Ḡ', 'B̄']

    for angle, color, name in zip(discrete_angles, weight_colors_list, weight_names):
        x = r_discrete * np.cos(angle)
        y = r_discrete * np.sin(angle)
        traces.append(go.Scatter(
            x=[x], y=[y],
            mode='markers+text',
            marker=dict(size=14, color=color, line=dict(color='black', width=1.5)),
            text=[name],
            textposition='middle center',
            textfont=dict(size=8, color=color),
            showlegend=False
        ))

    # --- Layer 7: Center point ---
    traces.append(go.Scatter(
        x=[0], y=[0],
        mode='markers',
        marker=dict(size=10, color='white', line=dict(color='black', width=1.5)),
        showlegend=False
    ))

    # --- Layer 8: Z₃ symmetry lines ---
    for angle in [np.pi/6, np.pi/6 + 2*np.pi/3, np.pi/6 + 4*np.pi/3]:
        traces.append(go.Scatter(
            x=[0, weight_radius*1.15*np.cos(angle)],
            y=[0, weight_radius*1.15*np.sin(angle)],
            mode='lines',
            line=dict(color='black', width=1, dash='dash'),
            opacity=0.3,
            showlegend=False
        ))

    return traces

# ============================================================================
# MAIN FIGURE
# ============================================================================

def generate_figure():
    """Generate the two-panel continuum limit figure."""

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=[
            '(a) A₂ Root System from Stella Weights',
            '(b) Continuum Limit: Discrete → Continuous'
        ],
        horizontal_spacing=0.12
    )

    # Add Panel A traces
    panel_a_traces = create_panel_a()
    for trace in panel_a_traces:
        fig.add_trace(trace, row=1, col=1)

    # Add Panel B traces
    panel_b_traces = create_panel_b()
    for trace in panel_b_traces:
        fig.add_trace(trace, row=1, col=2)

    # Update layout
    fig.update_layout(
        width=1000,
        height=450,
        showlegend=False,
        paper_bgcolor='white',
        plot_bgcolor='white',
        font=dict(family='serif', size=11),
        margin=dict(l=50, r=50, t=50, b=50)
    )

    # Panel A axes
    fig.update_xaxes(
        range=[-0.75, 0.75],
        scaleanchor='y', scaleratio=1,
        title_text='Weight space h₁',
        showgrid=True, gridwidth=0.5, gridcolor='lightgray',
        zeroline=True, zerolinewidth=0.5, zerolinecolor='gray',
        row=1, col=1
    )
    fig.update_yaxes(
        range=[-0.75, 0.75],
        title_text='Weight space h₂',
        showgrid=True, gridwidth=0.5, gridcolor='lightgray',
        zeroline=True, zerolinewidth=0.5, zerolinecolor='gray',
        row=1, col=1
    )

    # Panel B axes
    fig.update_xaxes(
        range=[-0.85, 0.85],
        scaleanchor='y2', scaleratio=1,
        showgrid=False, showticklabels=False, showline=False,
        row=1, col=2
    )
    fig.update_yaxes(
        range=[-0.85, 0.85],
        showgrid=False, showticklabels=False, showline=False,
        row=1, col=2
    )

    # Add legend annotation for Panel B
    fig.add_annotation(
        x=-0.75, y=0.75,
        text='● a = a₀ (discrete)<br>● a = a₁ (finer)<br>▪ a → 0 (continuous)',
        showarrow=False,
        font=dict(size=9),
        align='left',
        bgcolor='white',
        bordercolor='gray',
        borderwidth=1,
        xref='x2', yref='y2'
    )

    # Add Z₃ symmetry annotation
    fig.add_annotation(
        x=0, y=-0.75,
        text='ℤ₃ symmetry preserved at all scales',
        showarrow=False,
        font=dict(size=9),
        bgcolor='white',
        bordercolor='gray',
        borderwidth=1,
        xref='x2', yref='y2'
    )

    # Save
    png_path = OUTPUT_DIR / 'fig_continuum_limit.png'
    pdf_path = OUTPUT_DIR / 'fig_continuum_limit.pdf'

    fig.write_image(str(png_path), scale=2)
    fig.write_image(str(pdf_path))

    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")

    return fig


if __name__ == "__main__":
    fig = generate_figure()
    fig.show()
