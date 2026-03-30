#!/usr/bin/env python3
"""
Figure: From Color Fields to Continuous Geometry
=================================================

Unified 2×3 panel figure telling the complete story:

  Row 1 (2D): Color fields construct the stella octangula
    (a) Three color fields χ_R, χ_G, χ_B          [Def 0.1.2, Def 0.1.3]
    (b) Additive superposition → T₊                [Thm 0.2.1]
    (c) T₊(RGB) ⊔ T₋(CMY) → ∂S                   [Thm 1.1.2, Def 0.1.1]

  Row 2 (3D): Discrete stella smooths to continuous geometry
    (d) t = 0: Discrete stella ∂S                  [Def 0.1.1, χ = 4]
    (e) t = 0.5: Inflating toward sphere            [Continuum limit]
    (f) t = 1: Continuous S² ⊔ S²                   [Sec 7: O → SO(3)]

Key mathematical content (all backed by proofs):
  χ_c(x) = a₀ P_c(x) e^{iφ_c}          Def 0.1.2 (phases 0, 2π/3, 4π/3)
  P_c(x) = 1/(|x - x_c|² + ε²)         Def 0.1.3 (axioms P1-P5)
  χ_total = Σ_c χ_c                     Thm 0.2.1 (superposition)
  I: r → −r  (T₊ ↔ T₋)                 Thm 1.1.2 (charge conjugation)
  ∂S = ∂T₊ ⊔ ∂T₋, χ = 4               Def 0.1.1 (boundary topology)
  v(t) = (1−t)v_flat + tRv̂              Spherification (visualization of
                                         spatial continuum limit O → SO(3))
  Z₃ center preserved ∀ t               Algebraic invariant of A₂ root system

Output:
  fig_fields_to_geometry.{png,pdf}

Author: Chiral Geometrogenesis Project
Date: 2026-03-18
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import FancyArrowPatch, Patch
from pathlib import Path

OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# COLOR CONSTANTS
# ============================================================================

C_RED   = np.array([1.0, 0.0, 0.0])
C_GREEN = np.array([0.0, 1.0, 0.0])
C_BLUE  = np.array([0.0, 0.0, 1.0])
C_CYAN    = np.array([0.0, 1.0, 1.0])
C_MAGENTA = np.array([1.0, 0.0, 1.0])
C_YELLOW  = np.array([1.0, 1.0, 0.0])
C_WHITE = np.array([1.0, 1.0, 1.0])
C_BLACK = np.array([0.0, 0.0, 0.0])

# 3D face colors — T₊ (saturated), T₋ (pastel)
FACE_COLORS_PLUS = [
    (0.91, 0.30, 0.24, 0.92),   # R
    (0.15, 0.68, 0.38, 0.92),   # G
    (0.20, 0.60, 0.86, 0.92),   # B
    (0.70, 0.70, 0.70, 0.45),   # W
]
FACE_COLORS_MINUS = [
    (0.95, 0.58, 0.55, 0.88),   # R̄
    (0.51, 0.88, 0.67, 0.88),   # Ḡ
    (0.52, 0.76, 0.91, 0.88),   # B̄
    (0.85, 0.85, 0.85, 0.45),   # W̄
]

# Gradient parameters
N = 600           # pixel resolution
EXTENT = 1.0
GRAD_FRAC = 0.40  # gradient spans 40% of canvas
ALPHA_GAMMA = 2.2 # perceptual gamma (Prop 0.1.3a: form-independent)
ANGLES_DEG = [90.0, -150.0, -30.0]  # R, G, B gradient directions

# ============================================================================
# ROW 1: 2D COLOR FIELD CONSTRUCTION
# ============================================================================

def _make_grid(n, extent):
    xs = np.linspace(-extent, extent, n)
    ys = np.linspace(-extent, extent, n)
    return np.meshgrid(xs, ys[::-1])


def create_gradient_layer(angle_deg, color_primary, color_secondary,
                          n=600, extent=1.0, grad_frac=GRAD_FRAC):
    """Create RGBA gradient layer.

    Physics: χ_c(x) = a₀ P_c(x) e^{iφ_c}  (Def 0.1.2)
    - Color ramp (white → primary) encodes the phase e^{iφ_c}
    - Opacity ramp (0 → 1) encodes the pressure P_c(x) (Def 0.1.3)
    - Gamma curve satisfies axioms (P1)-(P5): smooth, monotone, radial
    """
    angle_rad = np.deg2rad(angle_deg)
    dx, dy = np.cos(angle_rad), np.sin(angle_rad)

    X, Y = _make_grid(n, extent)
    proj = X * dx + Y * dy

    grad_half = grad_frac * extent
    t = np.clip((proj + grad_half) / (2.0 * grad_half), 0.0, 1.0)

    # Alpha: P_c(x) pressure function (Def 0.1.3)
    alpha = t ** ALPHA_GAMMA

    # Color: phase identification (Def 0.1.2)
    layer = np.zeros((n, n, 4))
    for ch in range(3):
        layer[:, :, ch] = color_secondary[ch] * (1 - t) + color_primary[ch] * t
    layer[:, :, 3] = alpha
    return layer


def linear_dodge_composite(layers):
    """Sequential Linear Dodge compositing.

    Implements χ_total = Σ_c χ_c  (Thm 0.2.1)
    """
    h, w = layers[0].shape[:2]
    canvas_premul = np.zeros((h, w, 3))
    canvas_alpha = np.zeros((h, w))

    for layer in layers:
        src_straight = layer[:, :, :3]
        src_alpha = layer[:, :, 3]

        safe = np.maximum(canvas_alpha, 1e-10)
        canvas_straight = np.clip(canvas_premul / safe[:, :, np.newaxis], 0, 1)

        blended = np.minimum(canvas_straight + src_straight, 1.0)

        alpha_s = src_alpha[:, :, np.newaxis]
        alpha_b = canvas_alpha[:, :, np.newaxis]
        new_premul = (alpha_s * (1 - alpha_b) * src_straight +
                      alpha_b * (1 - alpha_s) * canvas_straight +
                      alpha_s * alpha_b * blended)

        canvas_alpha = src_alpha + canvas_alpha * (1 - src_alpha)
        canvas_premul = np.clip(new_premul, 0, 1)

    return canvas_premul, canvas_alpha


def _checkerboard(n, square=16, c0=0.78, c1=0.92):
    rows = np.arange(n) // square
    cols = np.arange(n) // square
    mask = (rows[:, None] + cols[None, :]) % 2 == 0
    board = np.full((n, n, 3), c0)
    board[mask] = c1
    return board


def _on_checker(premul, alpha, n=600):
    checker = _checkerboard(n)
    return np.clip(premul + checker * (1 - alpha[:, :, np.newaxis]), 0, 1)


def stella_wireframe(ax, r=0.7):
    """Draw 2D wireframe of T₊ (solid) and T₋ (dashed)."""
    tp = np.array([[r * np.cos(np.pi/2 + i*2*np.pi/3),
                     r * np.sin(np.pi/2 + i*2*np.pi/3)] for i in range(3)])
    tm = -tp
    tp_c = np.vstack([tp, tp[0]])
    tm_c = np.vstack([tm, tm[0]])
    ax.plot(tp_c[:, 0], tp_c[:, 1], '-', color='white', lw=2.0, alpha=0.9)
    ax.plot(tm_c[:, 0], tm_c[:, 1], '--', color='white', lw=1.5, alpha=0.7)


def panel_a(ax):
    """(a) Three color fields overlaid on checkerboard.

    Shows χ_c = a₀ P_c(x) e^{iφ_c}  (Def 0.1.2, Def 0.1.3)
    Checkerboard reveals the alpha/pressure gradient structure.
    """
    layers = [create_gradient_layer(a, cp, C_WHITE, N, EXTENT)
              for a, cp in zip(ANGLES_DEG, [C_RED, C_GREEN, C_BLUE])]
    premul, alpha = linear_dodge_composite(layers)
    img = _on_checker(premul, alpha, N)
    ax.imshow(img, extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    ax.set_title(r'(a) $\chi_c = a_0\, P_c\, e^{i\phi_c}$',
                 fontsize=10, fontweight='bold')
    ax.text(0.5, -0.06, 'Def 0.1.2 + Def 0.1.3',
            transform=ax.transAxes, fontsize=8, ha='center',
            color='#444444', style='italic')
    ax.set_xticks([])
    ax.set_yticks([])
    return premul, alpha


def panel_b(ax, premul, alpha):
    """(b) Additive blend → T₊ on checkerboard.

    χ_total = Σ_c χ_c  (Thm 0.2.1)
    The triangular region where all three fields overlap = T₊.
    """
    img = _on_checker(premul, alpha, N)
    ax.imshow(img, extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    # Draw T₊ wireframe
    tp = np.array([[0.7*np.cos(np.pi/2 + i*2*np.pi/3),
                     0.7*np.sin(np.pi/2 + i*2*np.pi/3)] for i in range(3)])
    tp_c = np.vstack([tp, tp[0]])
    ax.plot(tp_c[:, 0], tp_c[:, 1], '-', color='white', lw=2.0, alpha=0.85)
    ax.set_title(r'(b) $\chi_{\rm total} = \sum_c \chi_c \;\to\; T_+$',
                 fontsize=10, fontweight='bold')
    ax.text(0.5, -0.06, 'Thm 0.2.1 (superposition)',
            transform=ax.transAxes, fontsize=8, ha='center',
            color='#444444', style='italic')
    ax.set_xticks([])
    ax.set_yticks([])


def panel_c(ax, premul_plus, alpha_plus):
    """(c) T₊(RGB) ⊔ T₋(CMY) → ∂S on black.

    Charge conjugation I: r → −r  (Thm 1.1.2)
    maps T₊ → T₋, R↔C, G↔M, B↔Y.
    ∂S = ∂T₊ ⊔ ∂T₋  (Def 0.1.1)
    """
    # Build T₋ layers with anti-colors at 180°-rotated angles (Thm 1.1.2)
    angles_minus = [a + 180 for a in ANGLES_DEG]
    layers_minus = [create_gradient_layer(a, cp, C_BLACK, N, EXTENT)
                    for a, cp in zip(angles_minus, [C_CYAN, C_MAGENTA, C_YELLOW])]

    # Build T₊ layers with pure colors on black
    layers_plus = [create_gradient_layer(a, cp, C_BLACK, N, EXTENT)
                   for a, cp in zip(ANGLES_DEG, [C_RED, C_GREEN, C_BLUE])]

    # Additive blend all 6 lobes (incoherent sum ρ = Σ|a_c|², Thm 0.2.1)
    stella_rgb = np.zeros((N, N, 3))
    for layer in layers_plus + layers_minus:
        stella_rgb += layer[:, :, :3] * layer[:, :, 3:4]
    stella_rgb = np.clip(stella_rgb, 0, 1)

    ax.imshow(stella_rgb, extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    ax.set_facecolor('black')
    stella_wireframe(ax, r=0.7)
    ax.set_title(r'(c) $\partial\mathcal{S} = \partial T_+\!\sqcup\!\partial T_-$',
                 fontsize=10, fontweight='bold')
    ax.text(0.5, -0.06, r'Def 0.1.1 + Thm 1.1.2: $\mathcal{I}\!: \mathbf{r}\!\to\!-\mathbf{r}$',
            transform=ax.transAxes, fontsize=8, ha='center',
            color='#444444', style='italic')
    ax.set_xticks([])
    ax.set_yticks([])


# ============================================================================
# ROW 2: 3D GEOMETRIC EMERGENCE
# ============================================================================

def stella_vertices():
    """T₊ and T₋ vertices on unit sphere (Def 0.1.1)."""
    s = 1.0 / np.sqrt(3)
    T_plus = np.array([
        [ s,  s,  s],   # R
        [ s, -s, -s],   # G
        [-s,  s, -s],   # B
        [-s, -s,  s],   # W
    ])
    T_minus = -T_plus
    return T_plus, T_minus


def tetra_faces():
    return [[1,2,3], [0,2,3], [0,1,3], [0,1,2]]


def subdivide_triangle(v0, v1, v2, n_sub):
    """Barycentric subdivision of a triangle into n_sub² sub-triangles."""
    vertices = []
    idx_map = {}
    for i in range(n_sub + 1):
        for j in range(n_sub + 1 - i):
            a, b = i / n_sub, j / n_sub
            c = 1.0 - a - b
            idx_map[(i, j)] = len(vertices)
            vertices.append(a * v0 + b * v1 + c * v2)

    faces = []
    for i in range(n_sub):
        for j in range(n_sub - i):
            faces.append([idx_map[(i,j)], idx_map[(i+1,j)], idx_map[(i,j+1)]])
            if i + j < n_sub - 1:
                faces.append([idx_map[(i+1,j)], idx_map[(i+1,j+1)], idx_map[(i,j+1)]])

    return np.array(vertices), np.array(faces)


def blend_to_sphere(vertices, t, R=1.0):
    """Spherification: v(t) = (1-t) v_flat + t R v̂

    Visualization of spatial continuum limit (G1 Sec 7):
    discrete O_h → continuous SO(3) as a → 0.
    """
    norms = np.maximum(np.linalg.norm(vertices, axis=1, keepdims=True), 1e-12)
    v_sphere = R * vertices / norms
    return (1 - t) * vertices + t * v_sphere


def render_3d_panel(ax, t, n_sub=10, title=None, subtitle=None):
    """Render 3D stella at blending parameter t."""
    T_plus, T_minus = stella_vertices()
    face_idx = tetra_faces()

    # Separate radii for disjoint union (∂T₊ ⊔ ∂T₋, Def 0.1.1)
    radii = [1.0, 0.90]

    triangles = []
    facecolors = []
    orig_edges = []

    for tetra, colors, R in [(T_plus, FACE_COLORS_PLUS, radii[0]),
                              (T_minus, FACE_COLORS_MINUS, radii[1])]:
        for fi, face in enumerate(face_idx):
            v0, v1, v2 = tetra[face[0]], tetra[face[1]], tetra[face[2]]
            verts, sub_faces = subdivide_triangle(v0, v1, v2, n_sub)
            verts_b = blend_to_sphere(verts, t, R=R)
            for sf in sub_faces:
                triangles.append(verts_b[sf])
                facecolors.append(colors[fi])

        # Original tetrahedron edges
        for i in range(4):
            for j in range(i + 1, 4):
                pts = np.array([tetra[i]*(1-s) + tetra[j]*s
                                for s in np.linspace(0, 1, 20)])
                orig_edges.append(blend_to_sphere(pts, t, R=R))

    # Subdivision mesh edges (fade fast)
    sub_alpha = max(0.0, (1 - t)**2) * 0.3
    sub_lw = max(0.05, (1 - t) * 0.4)

    coll = Poly3DCollection(triangles, facecolors=facecolors,
                            edgecolors=(0.2, 0.2, 0.2, sub_alpha),
                            linewidths=sub_lw, zsort='average')
    ax.add_collection3d(coll)

    # Bold original edges (dissolve with t)
    edge_alpha = max(0.0, 1 - t) * 0.9
    edge_lw = max(0.1, (1 - t)**0.5 * 2.2)
    for edge in orig_edges:
        ax.plot3D(edge[:,0], edge[:,1], edge[:,2],
                  color=(0.1, 0.1, 0.1, edge_alpha), linewidth=edge_lw, zorder=10)

    lim = 0.72
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.axis('off')
    ax.view_init(elev=20, azim=35)

    if title:
        ax.set_title(title, fontsize=10, fontweight='bold', pad=-4)
    if subtitle:
        # Place subtitle below the 3D axes
        ax.text2D(0.5, -0.04, subtitle, transform=ax.transAxes,
                  fontsize=7, ha='center', color='#555555', style='italic')


# ============================================================================
# MAIN FIGURE
# ============================================================================

def generate_figure():
    plt.rcParams.update({
        'font.size': 10,
        'font.family': 'serif',
        'mathtext.fontset': 'dejavuserif',
    })

    fig = plt.figure(figsize=(13, 8.5))

    # Use GridSpec: 2 rows, 3 columns
    # Row heights: top row shorter (2D images are square), bottom taller (3D needs space)
    gs = GridSpec(2, 3, figure=fig, height_ratios=[1, 1.1],
                  hspace=0.22, wspace=0.15)

    # ---- Row 1: 2D color field construction ----
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[0, 2])

    premul, alpha = panel_a(ax_a)
    panel_b(ax_b, premul, alpha)
    panel_c(ax_c, premul, alpha)

    # ---- Row 2: 3D geometric emergence ----
    ax_d = fig.add_subplot(gs[1, 0], projection='3d')
    ax_e = fig.add_subplot(gs[1, 1], projection='3d')
    ax_f = fig.add_subplot(gs[1, 2], projection='3d')

    render_3d_panel(ax_d, t=0.0, n_sub=8,
                    title=r'(d) $t\!=\!0$: Discrete $\partial\mathcal{S}$',
                    subtitle=r'Def 0.1.1: $\chi = 8 - 12 + 8 = 4$')

    render_3d_panel(ax_e, t=0.5, n_sub=10,
                    title=r'(e) $t\!=\!0.5$: Inflating',
                    subtitle=r'$\mathbf{v}(t) = (1\!-\!t)\,\mathbf{v}_{\rm flat} + t\,R\,\hat{\mathbf{v}}$')

    render_3d_panel(ax_f, t=1.0, n_sub=14,
                    title=r'(f) $t\!=\!1$: Continuous $S^2\!\sqcup\!S^2$',
                    subtitle=r'$O \to SO(3)$; $\mathbb{Z}_3$ preserved')

    # ---- Row labels (left margin) ----
    fig.text(0.015, 0.76,
             r'$\chi_c \to \partial\mathcal{S}$',
             fontsize=9, va='center', ha='center', color='#333333',
             fontweight='bold', rotation=90)
    fig.text(0.015, 0.32,
             r'$\partial\mathcal{S} \to S^2$',
             fontsize=9, va='center', ha='center', color='#333333',
             fontweight='bold', rotation=90)

    # Downward arrow between rows
    fig.text(0.015, 0.53, r'$\Downarrow$',
             fontsize=14, va='center', ha='center', color='#555555')

    # Master title
    fig.suptitle(
        r'From color fields to continuous geometry:'
        r'$\quad \chi_c \;\longrightarrow\; \partial\mathcal{S}'
        r' \;\longrightarrow\; S^2 \sqcup S^2$',
        fontsize=12, fontweight='bold', y=0.98,
    )

    # Color legend at bottom
    legend_patches = [
        Patch(facecolor='red',     label=r'$R$ ($\phi\!=\!0$)'),
        Patch(facecolor='green',   label=r'$G$ ($\phi\!=\!2\pi/3$)'),
        Patch(facecolor='blue',    label=r'$B$ ($\phi\!=\!4\pi/3$)'),
        Patch(facecolor='cyan',    edgecolor='gray', label=r'$\bar{R}$'),
        Patch(facecolor='magenta', edgecolor='gray', label=r'$\bar{G}$'),
        Patch(facecolor='yellow',  edgecolor='gray', label=r'$\bar{B}$'),
    ]
    fig.legend(handles=legend_patches, loc='lower center', ncol=6,
               fontsize=8, frameon=True, framealpha=0.9,
               bbox_to_anchor=(0.52, 0.003))

    # Manual spacing (tight_layout conflicts with 3D axes)
    gs.update(left=0.04, right=0.99, top=0.93, bottom=0.05)

    # Save
    png_path = OUTPUT_DIR / 'fig_fields_to_geometry.png'
    pdf_path = OUTPUT_DIR / 'fig_fields_to_geometry.pdf'
    plt.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")
    return png_path, pdf_path


def print_proof_backing():
    """Print the proof backing for each panel."""
    print("=" * 70)
    print("Unified Figure: From Color Fields to Continuous Geometry")
    print("=" * 70)
    print()
    print("Panel  | Content                          | Proof Backing")
    print("-------|----------------------------------|---------------------------")
    print("(a)    | Three color fields χ_c overlaid  | Def 0.1.2 (phases)")
    print("       |                                  | Def 0.1.3 (pressure P_c)")
    print("(b)    | Additive blend → T₊              | Thm 0.2.1 (superposition)")
    print("(c)    | T₊(RGB) ⊔ T₋(CMY) → ∂S          | Thm 1.1.2 (conjugation)")
    print("       |                                  | Def 0.1.1 (∂S topology)")
    print("(d)    | t=0: discrete stella             | Def 0.1.1 (χ = 4)")
    print("(e)    | t=0.5: inflating                 | Spherification formula")
    print("(f)    | t=1: smooth S² ⊔ S²              | Sec 7: O → SO(3)")
    print("       |                                  | Z₃ = Λ_cow/Λ_root (A₂)")
    print()
    print("Key formulas:")
    print("  χ_c(x) = a₀ P_c(x) e^{iφ_c}           (Def 0.1.2)")
    print("  P_c(x) = 1/(|x - x_c|² + ε²)          (Def 0.1.3)")
    print("  χ_total = Σ_c χ_c                      (Thm 0.2.1)")
    print("  I: r → −r  maps T₊ ↔ T₋                (Thm 1.1.2)")
    print("  ∂S = ∂T₊ ⊔ ∂T₋, χ = 4                  (Def 0.1.1)")
    print("  v(t) = (1-t)v_flat + tRv̂                (visualization)")
    print("  Z₃ = Z(SU(3)) preserved ∀ t             (algebraic)")
    print("=" * 70)


if __name__ == "__main__":
    print_proof_backing()
    generate_figure()
