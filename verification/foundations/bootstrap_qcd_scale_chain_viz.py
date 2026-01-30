#!/usr/bin/env python3
"""
Visualization: Bootstrap & QCD Scale Determination Chain
=========================================================

Creates an interactive visualization showing how QCD parameters emerge
from pure geometry through the bootstrap fixed-point equations.

Group 1 Propositions:
- 0.0.17j: String Tension from Casimir Energy
- 0.0.17q: QCD Scale from Dimensional Transmutation
- 0.0.17y: Bootstrap Fixed-Point Uniqueness
- 0.0.17z: Non-Perturbative Corrections to Bootstrap
"""

import plotly.graph_objects as go
from plotly.subplots import make_subplots
import numpy as np

# =============================================================================
# CONSTANTS AND DATA
# =============================================================================

# Topological inputs (discrete, non-adjustable)
N_c = 3  # Colors
N_f = 3  # Light flavors
chi = 4  # Euler characteristic
Z3 = 3   # Center of SU(3)

# Derived topological quantities
dim_adj = N_c**2 - 1  # = 8 (gluons)
adj_squared = dim_adj**2  # = 64 (adj ⊗ adj channels)
b0 = (11*N_c - 2*N_f) / (12 * np.pi)  # β-function coefficient

# Physical constants
hbar_c = 197.327  # MeV·fm
M_P = 1.22089e19  # GeV (Planck mass)
ell_P = 1.616e-35  # m (Planck length)
ell_P_fm = ell_P * 1e15  # fm

# Bootstrap predictions
exponent = 128 * np.pi / 9  # ≈ 44.68
xi_predicted = np.exp(exponent)  # R_stella/ℓ_P
sqrt_sigma_oneloop = 481.1  # MeV (one-loop)
sqrt_sigma_corrected = 434.6  # MeV (after NP corrections)
sqrt_sigma_observed = 440  # MeV (FLAG 2024)
R_stella_observed = hbar_c / sqrt_sigma_observed  # fm

# Non-perturbative corrections
delta_gluon = 0.030  # 3%
delta_threshold = 0.030  # 3%
delta_twoloop = 0.020  # 2%
delta_instanton = 0.016  # 1.6%
delta_total = delta_gluon + delta_threshold + delta_twoloop + delta_instanton

# =============================================================================
# CREATE VISUALIZATION
# =============================================================================

def create_bootstrap_chain_visualization():
    """Create the main derivation chain visualization."""

    fig = go.Figure()

    # Define node positions (x, y)
    # Layer 0: Topological inputs
    # Layer 1: Derived topological quantities
    # Layer 2: Bootstrap equations
    # Layer 3: Predictions
    # Layer 4: Corrections
    # Layer 5: Final result

    nodes = {
        # Topological inputs (cyan - fundamental)
        'N_c': (0, 5),
        'N_f': (1, 5),
        'χ': (2, 5),
        '|Z₃|': (3, 5),

        # Derived topological (light blue)
        'dim(adj)=8': (0.5, 4),
        '64 channels': (1.5, 4),
        'b₀=9/(4π)': (2.5, 4),

        # Bootstrap equations (green)
        'Eq1: √σ=ℏc/R': (0, 3),
        'Eq2: R/ℓ_P=exp(...)': (1.5, 3),
        'Eq4: 1/αs=64': (3, 3),

        # Propositions (yellow/gold)
        '0.0.17j': (0, 2),
        '0.0.17q': (1.5, 2),
        '0.0.17y': (3, 2),

        # One-loop prediction (orange)
        '√σ=481 MeV': (1.5, 1),

        # Corrections (red)
        '0.0.17z': (0, 0),
        'NP: -9.6%': (1.5, 0),

        # Final result (purple)
        '√σ=435 MeV': (3, 0),
    }

    # Node colors by type
    colors = {
        'N_c': '#00CED1', 'N_f': '#00CED1', 'χ': '#00CED1', '|Z₃|': '#00CED1',
        'dim(adj)=8': '#87CEEB', '64 channels': '#87CEEB', 'b₀=9/(4π)': '#87CEEB',
        'Eq1: √σ=ℏc/R': '#90EE90', 'Eq2: R/ℓ_P=exp(...)': '#90EE90', 'Eq4: 1/αs=64': '#90EE90',
        '0.0.17j': '#FFD700', '0.0.17q': '#FFD700', '0.0.17y': '#FFD700',
        '√σ=481 MeV': '#FFA500',
        '0.0.17z': '#FF6B6B', 'NP: -9.6%': '#FF6B6B',
        '√σ=435 MeV': '#9370DB',
    }

    # Draw edges (arrows)
    edges = [
        # Topological inputs → derived quantities
        ('N_c', 'dim(adj)=8'), ('N_c', 'b₀=9/(4π)'),
        ('N_f', 'b₀=9/(4π)'),
        ('dim(adj)=8', '64 channels'),

        # Derived → equations
        ('64 channels', 'Eq4: 1/αs=64'),
        ('b₀=9/(4π)', 'Eq2: R/ℓ_P=exp(...)'),
        ('χ', 'Eq2: R/ℓ_P=exp(...)'),

        # Equations → propositions
        ('Eq1: √σ=ℏc/R', '0.0.17j'),
        ('Eq2: R/ℓ_P=exp(...)', '0.0.17q'),
        ('Eq4: 1/αs=64', '0.0.17y'),
        ('Eq2: R/ℓ_P=exp(...)', '0.0.17y'),

        # Propositions → one-loop
        ('0.0.17j', '√σ=481 MeV'),
        ('0.0.17q', '√σ=481 MeV'),
        ('0.0.17y', '√σ=481 MeV'),

        # One-loop → corrections
        ('√σ=481 MeV', '0.0.17z'),
        ('√σ=481 MeV', 'NP: -9.6%'),

        # Corrections → final
        ('0.0.17z', '√σ=435 MeV'),
        ('NP: -9.6%', '√σ=435 MeV'),
    ]

    # Draw edges as lines
    for start, end in edges:
        x0, y0 = nodes[start]
        x1, y1 = nodes[end]

        fig.add_trace(go.Scatter(
            x=[x0, x1], y=[y0, y1],
            mode='lines',
            line=dict(color='rgba(100,100,100,0.5)', width=2),
            hoverinfo='skip',
            showlegend=False
        ))

    # Draw nodes
    for name, (x, y) in nodes.items():
        fig.add_trace(go.Scatter(
            x=[x], y=[y],
            mode='markers+text',
            marker=dict(size=35, color=colors[name],
                       line=dict(color='black', width=2)),
            text=[name],
            textposition='middle center',
            textfont=dict(size=9, color='black'),
            hovertemplate=f"<b>{name}</b><extra></extra>",
            showlegend=False
        ))

    # Add layer labels
    layer_labels = [
        (3.8, 5, "Topological<br>Inputs", "#00CED1"),
        (3.8, 4, "Derived<br>Quantities", "#87CEEB"),
        (3.8, 3, "Bootstrap<br>Equations", "#90EE90"),
        (3.8, 2, "Propositions", "#FFD700"),
        (3.8, 1, "One-Loop<br>Prediction", "#FFA500"),
        (3.8, 0, "Corrected<br>Result", "#9370DB"),
    ]

    for x, y, text, color in layer_labels:
        fig.add_annotation(
            x=x, y=y,
            text=text,
            showarrow=False,
            font=dict(size=10, color=color),
            xanchor='left'
        )

    fig.update_layout(
        title=dict(
            text="<b>Bootstrap & QCD Scale Determination Chain</b><br>" +
                 "<sup>From Pure Topology to QCD Parameters (Group 1: Props 0.0.17j, q, y, z)</sup>",
            x=0.5,
            font=dict(size=16)
        ),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False, range=[-0.5, 5]),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False, range=[-0.5, 5.5]),
        plot_bgcolor='white',
        width=900,
        height=700,
        margin=dict(l=50, r=150, t=100, b=50)
    )

    return fig


def create_detailed_sankey():
    """Create a Sankey diagram showing the complete derivation flow."""

    # Define nodes
    labels = [
        # 0-3: Topological inputs
        "N_c = 3", "N_f = 3", "χ = 4", "|Z₃| = 3",
        # 4-6: Derived quantities
        "dim(adj) = 8", "(N²-1)² = 64", "b₀ = 9/(4π)",
        # 7-9: Physical scales
        "1/αs(M_P) = 64", "exp(128π/9)", "R_stella/ℓ_P",
        # 10: Casimir relation
        "√σ = ℏc/R",
        # 11: One-loop prediction
        "√σ = 481.1 MeV",
        # 12-15: NP corrections
        "Gluon Cond. (-3%)", "Threshold (-3%)", "Two-loop (-2%)", "Instantons (-1.6%)",
        # 16: Total correction
        "Total: -9.6%",
        # 17: Final result
        "√σ = 434.6 MeV",
        # 18: Observation
        "√σ_obs = 440±30 MeV"
    ]

    # Colors for each node
    colors = [
        # Topological inputs (cyan)
        "#00CED1", "#00CED1", "#00CED1", "#00CED1",
        # Derived (light blue)
        "#87CEEB", "#87CEEB", "#87CEEB",
        # Scales (green)
        "#90EE90", "#90EE90", "#90EE90",
        # Casimir (lime)
        "#32CD32",
        # One-loop (orange)
        "#FFA500",
        # Corrections (red tones)
        "#FF6B6B", "#FF8C69", "#FFA07A", "#FFB6C1",
        # Total (red)
        "#FF4500",
        # Final (purple)
        "#9370DB",
        # Observation (gold)
        "#FFD700"
    ]

    # Define links (source, target, value)
    links = [
        # Topological → derived
        (0, 4, 1), (0, 6, 1),  # N_c → dim(adj), b₀
        (1, 6, 1),  # N_f → b₀
        (4, 5, 1),  # dim(adj) → 64

        # Derived → scales
        (5, 7, 1),  # 64 → 1/αs
        (6, 8, 1),  # b₀ → exp
        (2, 9, 0.5),  # χ → R/ℓ_P
        (8, 9, 1),  # exp → R/ℓ_P

        # Scales → Casimir
        (9, 10, 1),  # R/ℓ_P → √σ = ℏc/R

        # Casimir → one-loop
        (10, 11, 1),  # √σ = ℏc/R → 481 MeV

        # One-loop → corrections
        (11, 12, 0.3), (11, 13, 0.3), (11, 14, 0.2), (11, 15, 0.16),

        # Corrections → total
        (12, 16, 0.3), (13, 16, 0.3), (14, 16, 0.2), (15, 16, 0.16),

        # Total + one-loop → final
        (11, 17, 0.5),
        (16, 17, 0.5),

        # Final ↔ observation (comparison)
        (17, 18, 1),
    ]

    source = [l[0] for l in links]
    target = [l[1] for l in links]
    value = [l[2] for l in links]

    fig = go.Figure(data=[go.Sankey(
        node=dict(
            pad=15,
            thickness=20,
            line=dict(color="black", width=0.5),
            label=labels,
            color=colors
        ),
        link=dict(
            source=source,
            target=target,
            value=value,
            color=['rgba(100,100,100,0.3)'] * len(links)
        )
    )])

    fig.update_layout(
        title=dict(
            text="<b>QCD Scale Determination: Complete Derivation Flow</b><br>" +
                 "<sup>Topology → Bootstrap → Predictions → Corrections → Agreement (0.17σ)</sup>",
            x=0.5,
            font=dict(size=14)
        ),
        font=dict(size=10),
        width=1100,
        height=600
    )

    return fig


def create_equation_summary():
    """Create a summary panel with the key equations."""

    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=[
            "<b>Prop 0.0.17j:</b> Casimir Energy",
            "<b>Prop 0.0.17q:</b> Dimensional Transmutation",
            "<b>Prop 0.0.17y:</b> Bootstrap Uniqueness",
            "<b>Prop 0.0.17z:</b> Non-Perturbative Corrections"
        ],
        specs=[[{"type": "table"}, {"type": "table"}],
               [{"type": "table"}, {"type": "table"}]]
    )

    # Prop 0.0.17j
    fig.add_trace(go.Table(
        header=dict(values=["<b>Key Formula</b>", "<b>Result</b>"],
                   fill_color='#90EE90', align='left'),
        cells=dict(
            values=[
                ["√σ = ℏc/R_stella", "R_stella", "σ"],
                ["440 MeV", "0.448 fm", "0.19 GeV²"]
            ],
            fill_color='#E8F5E9',
            align='left'
        )
    ), row=1, col=1)

    # Prop 0.0.17q
    fig.add_trace(go.Table(
        header=dict(values=["<b>Key Formula</b>", "<b>Result</b>"],
                   fill_color='#87CEEB', align='left'),
        cells=dict(
            values=[
                ["R/ℓ_P = exp(64/2b₀)", "ξ = exp(128π/9)", "log₁₀(ξ)"],
                ["2.5 × 10¹⁹", "exp(44.68)", "19.4"]
            ],
            fill_color='#E3F2FD',
            align='left'
        )
    ), row=1, col=2)

    # Prop 0.0.17y
    fig.add_trace(go.Table(
        header=dict(values=["<b>Input</b>", "<b>Value</b>"],
                   fill_color='#FFD700', align='left'),
        cells=dict(
            values=[
                ["(N_c, N_f, |Z₃|)", "α_s(M_P)", "b₀", "One-loop √σ"],
                ["(3, 3, 3)", "1/64 = 0.0156", "9/(4π) = 0.716", "481.1 MeV"]
            ],
            fill_color='#FFFDE7',
            align='left'
        )
    ), row=2, col=1)

    # Prop 0.0.17z
    fig.add_trace(go.Table(
        header=dict(values=["<b>Correction</b>", "<b>%</b>"],
                   fill_color='#FF6B6B', align='left'),
        cells=dict(
            values=[
                ["Gluon condensate", "Threshold", "Two-loop", "Instantons", "<b>Total</b>", "<b>Final √σ</b>"],
                ["-3.0%", "-3.0%", "-2.0%", "-1.6%", "<b>-9.6%</b>", "<b>434.6 MeV</b>"]
            ],
            fill_color=['#FFEBEE']*6,
            align='left'
        )
    ), row=2, col=2)

    fig.update_layout(
        title=dict(
            text="<b>Bootstrap & QCD Scale: Key Equations Summary</b>",
            x=0.5,
            font=dict(size=14)
        ),
        height=500,
        width=900,
        showlegend=False
    )

    return fig


def create_combined_visualization():
    """Create a comprehensive multi-panel visualization."""

    fig = make_subplots(
        rows=2, cols=2,
        specs=[
            [{"type": "scatter", "colspan": 2}, None],
            [{"type": "scatter"}, {"type": "bar"}]
        ],
        subplot_titles=[
            "",  # Main flow diagram
            "Scale Hierarchy",
            "Non-Perturbative Corrections"
        ],
        row_heights=[0.6, 0.4],
        vertical_spacing=0.12,
        horizontal_spacing=0.1
    )

    # ----- Panel 1: Main derivation flow (top, spanning both columns) -----
    nodes_x = [0, 1, 2, 3, 0.5, 1.5, 2.5, 0, 1.5, 3, 1.5, 1.5]
    nodes_y = [5, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 1]
    labels = ["N_c=3", "N_f=3", "χ=4", "|Z₃|=3",
              "dim=8", "64", "b₀",
              "0.17j", "0.17q", "0.17y",
              "481 MeV", "435 MeV"]
    colors = ["#00CED1"]*4 + ["#87CEEB"]*3 + ["#FFD700"]*3 + ["#FFA500", "#9370DB"]

    # Draw edges
    edges = [
        (0,4), (0,6), (1,6), (4,5),  # topology → derived
        (5,9), (6,8), (2,8),  # derived → props
        (7,10), (8,10), (9,10),  # props → one-loop
        (10,11)  # one-loop → corrected
    ]

    for i, j in edges:
        fig.add_trace(go.Scatter(
            x=[nodes_x[i], nodes_x[j]],
            y=[nodes_y[i], nodes_y[j]],
            mode='lines',
            line=dict(color='rgba(100,100,100,0.4)', width=2),
            hoverinfo='skip',
            showlegend=False
        ), row=1, col=1)

    # Draw nodes
    fig.add_trace(go.Scatter(
        x=nodes_x, y=nodes_y,
        mode='markers+text',
        marker=dict(size=30, color=colors, line=dict(color='black', width=1.5)),
        text=labels,
        textposition='middle center',
        textfont=dict(size=8),
        hoverinfo='text',
        showlegend=False
    ), row=1, col=1)

    # Add annotations for the main panel
    fig.add_annotation(
        x=1.5, y=5.5,
        text="<b>Topological Inputs</b>",
        showarrow=False, font=dict(size=10, color='#00CED1'),
        row=1, col=1
    )
    fig.add_annotation(
        x=-0.3, y=3,
        text="<b>Casimir</b>",
        showarrow=False, font=dict(size=8, color='#FFD700'),
        row=1, col=1
    )
    fig.add_annotation(
        x=1.5, y=0.5,
        text="<b>Final: √σ = 434.6±10 MeV</b><br>vs Obs: 440±30 MeV (0.17σ)",
        showarrow=True, arrowhead=2, ax=0, ay=-40,
        font=dict(size=9, color='#9370DB'),
        row=1, col=1
    )

    # ----- Panel 2: Scale hierarchy (bottom left) -----
    scales = ["ℓ_P", "R_stella", "1/√σ", "1/Λ_QCD", "1/M_P"]
    log_values = [np.log10(1.6e-35), np.log10(4.5e-16), np.log10(4.5e-16),
                  np.log10(1e-15), np.log10(8.2e-36)]

    fig.add_trace(go.Scatter(
        x=[1, 2, 3, 4, 5],
        y=[0, 19.4, 19.4, 18.6, 0.7],
        mode='markers+lines+text',
        marker=dict(size=15, color=['#9370DB', '#FFD700', '#90EE90', '#87CEEB', '#9370DB']),
        text=["ℓ_P", "R_stella", "1/√σ", "1/Λ_QCD", "1/M_P"],
        textposition='top center',
        line=dict(color='rgba(100,100,100,0.5)'),
        showlegend=False
    ), row=2, col=1)

    fig.add_annotation(
        x=2.5, y=10,
        text="<b>19 orders of magnitude!</b><br>from exp(128π/9)",
        showarrow=False, font=dict(size=9),
        row=2, col=1
    )

    # ----- Panel 3: NP corrections (bottom right) -----
    corrections = ["Gluon<br>Cond.", "Threshold", "Two-loop", "Instantons"]
    values = [-3.0, -3.0, -2.0, -1.6]
    corr_colors = ['#FF6B6B', '#FF8C69', '#FFA07A', '#FFB6C1']

    fig.add_trace(go.Bar(
        x=corrections,
        y=values,
        marker_color=corr_colors,
        text=[f"{v}%" for v in values],
        textposition='outside',
        showlegend=False
    ), row=2, col=2)

    fig.add_hline(y=-9.6, line_dash="dash", line_color="red",
                  annotation_text="Total: -9.6%", row=2, col=2)

    # Update layout
    fig.update_xaxes(showgrid=False, zeroline=False, showticklabels=False, row=1, col=1)
    fig.update_yaxes(showgrid=False, zeroline=False, showticklabels=False, row=1, col=1)
    fig.update_yaxes(title_text="log₁₀(scale/m)", row=2, col=1)
    fig.update_yaxes(title_text="Correction (%)", row=2, col=2)

    fig.update_layout(
        title=dict(
            text="<b>Bootstrap & QCD Scale Determination Chain</b><br>" +
                 "<sup>Group 1: Props 0.0.17j, 0.0.17q, 0.0.17y, 0.0.17z</sup>",
            x=0.5,
            font=dict(size=16)
        ),
        height=800,
        width=1000,
        showlegend=False,
        plot_bgcolor='white'
    )

    return fig


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("Creating Bootstrap & QCD Scale Determination visualizations...")

    # Create all visualizations
    fig1 = create_bootstrap_chain_visualization()
    fig2 = create_detailed_sankey()
    fig3 = create_equation_summary()
    fig4 = create_combined_visualization()

    # Save as HTML files
    output_dir = "../../verification/plots"

    fig1.write_html(f"{output_dir}/bootstrap_qcd_chain_flow.html")
    print(f"  → Saved: {output_dir}/bootstrap_qcd_chain_flow.html")

    fig2.write_html(f"{output_dir}/bootstrap_qcd_sankey.html")
    print(f"  → Saved: {output_dir}/bootstrap_qcd_sankey.html")

    fig3.write_html(f"{output_dir}/bootstrap_qcd_equations.html")
    print(f"  → Saved: {output_dir}/bootstrap_qcd_equations.html")

    fig4.write_html(f"{output_dir}/bootstrap_qcd_combined.html")
    print(f"  → Saved: {output_dir}/bootstrap_qcd_combined.html")

    print("\nVisualization complete!")
    print("\nKey results shown:")
    print(f"  • Topological inputs: (N_c, N_f, χ, |Z₃|) = (3, 3, 4, 3)")
    print(f"  • Bootstrap exponent: 128π/9 = {128*np.pi/9:.2f}")
    print(f"  • Hierarchy: R_stella/ℓ_P = exp(44.68) ≈ {np.exp(128*np.pi/9):.2e}")
    print(f"  • One-loop √σ: {sqrt_sigma_oneloop} MeV")
    print(f"  • NP corrections: -{delta_total*100:.1f}%")
    print(f"  • Corrected √σ: {sqrt_sigma_corrected} MeV")
    print(f"  • Observed √σ: {sqrt_sigma_observed} ± 30 MeV")
    print(f"  • Agreement: 0.17σ (excellent)")
