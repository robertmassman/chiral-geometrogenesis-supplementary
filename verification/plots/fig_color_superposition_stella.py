#!/usr/bin/env python3
"""
Color Field Superposition → Stella Octangula Visualization
==========================================================

Demonstrates that three RGB color gradients, rotated 120° apart and
additively blended, produce a triangular region (T₊). Duplicating
and rotating 180° yields T₋, and screen-blending the two recovers
the stella octangula boundary pattern ∂S = ∂T₊ ⊔ ∂T₋.
T₊ lobes (RGB) and T₋ lobes (CMY) are additively blended on black,
representing incoherent energy sum ρ = Σ|a_c|² (Thm 0.2.1).
Anti-colors C/M/Y come from charge conjugation (Thm 1.1.2).

Key physics:
- Three color fields χ_R, χ_G, χ_B with phases {0, 2π/3, 4π/3} (Def 0.1.2)
- Pressure functions P_c(x) as amplitude modulation (Def 0.1.3)
- Total field superposition χ_total = Σ χ_c (Thm 0.2.1)
- Charge conjugation T₋ = −T₊ (Thm 1.1.2)
- Stella boundary ∂S = ∂T₊ ⊔ ∂T₋ (Def 0.1.1)

Proof Documents:
  docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md
  docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md
  docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md

Output: verification/plots/fig_color_superposition_stella.{png,pdf}
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import os

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PLOT_DIR = os.path.join(SCRIPT_DIR, "plots")
os.makedirs(PLOT_DIR, exist_ok=True)

# ---------------------------------------------------------------------------
# rcParams — publication quality, sans-serif
# ---------------------------------------------------------------------------
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# ---------------------------------------------------------------------------
# Project color constants
# ---------------------------------------------------------------------------
C_RED   = np.array([1.0, 0.0, 0.0])
C_GREEN = np.array([0.0, 1.0, 0.0])
C_BLUE  = np.array([0.0, 0.0, 1.0])

# Anti-colors (charge conjugation: Thm 1.1.2)
C_CYAN    = np.array([0.0, 1.0, 1.0])   # R̄
C_MAGENTA = np.array([1.0, 0.0, 1.0])   # Ḡ
C_YELLOW  = np.array([1.0, 1.0, 0.0])   # B̄

# Secondary color at gradient tails: WHITE
# Photoshop gradient editor shows color ramp: primary → white,
# with a separate opacity ramp: 100% → 0%.
C_WHITE = np.array([1.0, 1.0, 1.0])
C_BLACK = np.array([0.0, 0.0, 0.0])

# Gradient direction angles: each points from the canvas edge TOWARD the
# corresponding vertex of the equilateral triangle.  For a centred
# upward-pointing triangle these are the same as the inward normals:
#   90°   → toward top vertex        (Red)
#  -150°  → toward lower-left vertex (Green)
#   -30°  → toward lower-right vertex (Blue)
ANGLES_DEG = [90.0, -150.0, -30.0]

# Canvas parameters
N = 800          # pixel resolution
EXTENT = 1.0     # coordinate range [-EXTENT, EXTENT]
GRAD_FRAC = 0.40 # gradient spans 40% of canvas height, centered
R_TRI = 0.7      # circumradius of wireframe triangle

# Alpha curve exponent — models Photoshop "Smooth" interpolation.
# Justified by Prop 0.1.3a (pressure function form-independence):
# the physics depends only on axioms (P1)–(P7) (smooth, monotone,
# radial), not the specific functional form.  A perceptual gamma
# curve α = t^γ satisfies all axioms and matches the Photoshop
# gradient editor's non-linear opacity ramp.
ALPHA_GAMMA = 2.2


# ===========================================================================
# Core operations
# ===========================================================================

def _make_grid(N, extent):
    """Create coordinate grid with y increasing upward."""
    xs = np.linspace(-extent, extent, N)
    ys = np.linspace(-extent, extent, N)
    return np.meshgrid(xs, ys[::-1])


def create_gradient_layer(angle_deg, color_primary, color_secondary,
                          N=800, extent=1.0, grad_frac=GRAD_FRAC):
    """Create an RGBA gradient layer matching Photoshop setup.

    Replicates the Photoshop gradient tool with *two independent ramps*:
      - Colour bar:  white → primary  (e.g. white → red)
      - Opacity bar:  0 % → 100 %
    both varying linearly along the projection direction *angle_deg*.

    The gradient is centred on the canvas and spans *grad_frac* of the
    canvas height (default 40%).  Outside the gradient, values clamp:
      - Beyond the primary end:   alpha = 1, colour = primary (opaque)
      - Beyond the secondary end: alpha = 0, colour = white   (transparent)

    Three such gradients at 120° apart, additively blended (Photoshop
    "Linear Dodge / Add"), produce the triangular overlap pattern.
    This is the 2-D analog of pressure-function superposition (Def 0.1.3).
    """
    angle_rad = np.deg2rad(angle_deg)
    dx, dy = np.cos(angle_rad), np.sin(angle_rad)

    X, Y = _make_grid(N, extent)
    proj = X * dx + Y * dy

    # Gradient centred on canvas, spanning grad_frac of canvas height.
    # Same drag distance for all angles (matches Photoshop tool behavior).
    grad_half = grad_frac * extent
    t = (proj + grad_half) / (2.0 * grad_half)
    t = np.clip(t, 0.0, 1.0)

    # Alpha: opaque at vertex end (t=1), transparent at far end (t=0).
    # Gamma curve models the "Smooth" interpolation method (Photoshop)
    # and satisfies pressure-function axioms (P1)–(P7) per Prop 0.1.3a.
    alpha = t ** ALPHA_GAMMA

    # Colour: secondary at far end (t=0) → primary at vertex end (t=1)
    layer = np.zeros((N, N, 4))
    for ch in range(3):
        layer[:, :, ch] = color_secondary[ch] * (1.0 - t) + color_primary[ch] * t
    layer[:, :, 3] = alpha

    return layer


def linear_dodge_composite(layers):
    """Sequential Linear Dodge (Add) compositing matching Photoshop.

    Each layer is composited onto the running canvas using the full
    Porter-Duff formula with the Linear Dodge blend function
    B(Cb, Cs) = min(Cb + Cs, 1).

    This differs from a simple premultiplied sum because the straight
    colour values clip at each step, which matters for colour→white
    gradients where channels overlap.

    Implements χ_total = Σ_c χ_c  (Thm 0.2.1).

    Returns: (premul_rgb, alpha) — premultiplied RGB and composite alpha.
    """
    h, w = layers[0].shape[:2]
    canvas_premul = np.zeros((h, w, 3))
    canvas_alpha = np.zeros((h, w))

    for layer in layers:
        src_straight = layer[:, :, :3]          # straight colour
        src_alpha = layer[:, :, 3]              # source alpha

        # Recover straight canvas colour (safe division)
        safe = np.maximum(canvas_alpha, 1e-10)
        canvas_straight = canvas_premul / safe[:, :, np.newaxis]
        canvas_straight = np.clip(canvas_straight, 0.0, 1.0)

        # Linear Dodge blend on straight colours
        blended = np.minimum(canvas_straight + src_straight, 1.0)

        # Full compositing (premultiplied output)
        αs = src_alpha[:, :, np.newaxis]
        αb = canvas_alpha[:, :, np.newaxis]
        new_premul = (αs * (1.0 - αb) * src_straight +
                      αb * (1.0 - αs) * canvas_straight +
                      αs * αb * blended)

        # Alpha: standard Porter-Duff "over"
        new_alpha = src_alpha + canvas_alpha * (1.0 - src_alpha)

        canvas_premul = np.clip(new_premul, 0.0, 1.0)
        canvas_alpha = new_alpha

    return canvas_premul, canvas_alpha


def rotate_180(img):
    """180° rotation: x ↦ −x.  Maps T₊ → T₋ (charge conjugation)."""
    return img[::-1, ::-1, :].copy()



def stella_wireframe(ax, r=0.7):
    """Draw 2-D projected wireframe of T₊ and T₋ over an image axis."""
    tp = np.array([
        [r * np.cos(np.pi / 2 + i * 2 * np.pi / 3),
         r * np.sin(np.pi / 2 + i * 2 * np.pi / 3)]
        for i in range(3)
    ])
    tm = -tp

    tp_closed = np.vstack([tp, tp[0]])
    tm_closed = np.vstack([tm, tm[0]])

    ax.plot(tp_closed[:, 0], tp_closed[:, 1], '-', color='white',
            lw=2.5, alpha=0.9, label=r'$T_+$')
    ax.plot(tm_closed[:, 0], tm_closed[:, 1], '--', color='white',
            lw=2.0, alpha=0.7, label=r'$T_-$')


# ===========================================================================
# Build layers (shared)
# ===========================================================================

def _build_layers():
    colors_pri = [C_RED, C_GREEN, C_BLUE]
    return [create_gradient_layer(a, cp, C_WHITE, N, EXTENT)
            for a, cp in zip(ANGLES_DEG, colors_pri)]


# ===========================================================================
# Panel rendering
# ===========================================================================

def panel_single_gradient(ax, layer, color_primary, label, angle_deg):
    """Show the actual gradient layer (color→white with alpha fade)
    composited on a checkerboard, with start/end markers."""
    rgb = layer[:, :, :3]       # actual color ramp (primary → white)
    alpha = layer[:, :, 3:4]    # opacity ramp (1 → 0)
    checker = _checkerboard(N)
    final = rgb * alpha + checker * (1.0 - alpha)
    ax.imshow(np.clip(final, 0, 1), extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])

    # Draw gradient start/end markers
    angle_rad = np.deg2rad(angle_deg)
    dx, dy = np.cos(angle_rad), np.sin(angle_rad)
    grad_half = GRAD_FRAC * EXTENT
    sx, sy = grad_half * dx,  grad_half * dy   # start (α=1, opaque)
    ex, ey = -grad_half * dx, -grad_half * dy  # end   (α=0, transparent)
    ax.plot([sx, ex], [sy, ey], '-', color='white', lw=1.5, alpha=0.9)
    ax.plot(sx, sy, 'o', color='white', ms=7, mew=1.5, mfc=color_primary, zorder=5)
    ax.plot(ex, ey, 'o', color='white', ms=7, mew=1.5, mfc='none', zorder=5)

    ax.set_title(label, fontsize=11, fontweight='bold')
    ax.set_xlabel('x')
    ax.set_ylabel('y')


def _checkerboard(N, square=16, c0=0.78, c1=0.92):
    """Gray checkerboard for transparency display.

    Default tones match Photoshop.  Pass c0/c1 for higher contrast.
    """
    rows = np.arange(N) // square
    cols = np.arange(N) // square
    mask = (rows[:, None] + cols[None, :]) % 2 == 0
    board = np.full((N, N, 3), c0)
    board[mask] = c1
    return board


def _on_checker(premul, alpha, ax, title):
    """Composite premultiplied RGB + alpha onto checkerboard and display."""
    checker = _checkerboard(N)
    final = premul + checker * (1.0 - alpha[:, :, np.newaxis])
    ax.imshow(np.clip(final, 0, 1), extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    ax.set_title(title, fontsize=11, fontweight='bold')
    ax.set_xlabel('x')
    ax.set_ylabel('y')


def panel_a(ax, premul, alpha):
    """(a) Three color fields with Linear Dodge on checkerboard."""
    _on_checker(premul, alpha, ax,
                r'(a) Three color fields $\chi_R,\,\chi_G,\,\chi_B$')


def panel_b(ax, premul, alpha):
    """(b) Linear Dodge blend → T₊ triangle on checkerboard."""
    _on_checker(premul, alpha, ax,
                r'(b) Additive blend $\chi_{\mathrm{total}} = \sum_c \chi_c \;\to\; T_+$')


def panel_c(ax, premul_plus, alpha_plus):
    """(c) 180°-rotated copy → T₋ on checkerboard."""
    premul_minus = rotate_180(premul_plus)
    alpha_minus = alpha_plus[::-1, ::-1].copy()
    _on_checker(premul_minus, alpha_minus, ax,
                r'(c) 180° rotation $\to T_-$ (charge conjugation)')
    return premul_minus, alpha_minus


def panel_d(ax, premul_plus, alpha_plus, premul_minus, alpha_minus):
    """(d) Stella projection: T₊(RGB) background + T₋(CMY) foreground.

    Physics: ∂S = ∂T₊ ⊔ ∂T₋ with 3D projection geometry:
      - T₊ faces dominate the outer silhouette (broader RGB)
      - T₋ faces peek through the gaps (narrower CMY lobes)

    Chiral selection ⟨Q⟩ > 0 (Thm 2.2.4) makes T₊ the dominant
    tetrahedron, justifying it as the background (broader coverage).

    Charge conjugation (Thm 1.1.2): R↔C, G↔M, B↔Y.
    Energy: incoherent sum ρ = Σ_c |a_c|² (Thm 0.2.1).
    """
    # Build T₋ layers with anti-colors (CMY) at 180°-rotated angles
    angles_minus = [a + 180.0 for a in ANGLES_DEG]
    colors_minus = [C_CYAN, C_MAGENTA, C_YELLOW]
    layers_minus = [create_gradient_layer(a, cp, C_BLACK, N, EXTENT)
                    for a, cp in zip(angles_minus, colors_minus)]

    # Build T₊ layers with pure colors on black
    colors_plus = [C_RED, C_GREEN, C_BLUE]
    layers_plus = [create_gradient_layer(a, cp, C_BLACK, N, EXTENT)
                   for a, cp in zip(ANGLES_DEG, colors_plus)]

    # Additive blend all 6 lobes on black
    stella_rgb = np.zeros((N, N, 3))
    for layer in layers_plus + layers_minus:
        stella_rgb += layer[:, :, :3] * layer[:, :, 3:4]
    stella_rgb = np.clip(stella_rgb, 0.0, 1.0)

    ax.imshow(stella_rgb, extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    ax.set_facecolor('black')
    ax.set_title(
        r'(d) $T_+(RGB) \sqcup T_-(CMY) \to \partial\mathcal{S}$',
        fontsize=11, fontweight='bold')
    ax.set_xlabel('x')
    ax.set_ylabel('y')

    # Compute alpha envelope for panel_f
    stella_alpha = 1.0 - (1.0 - alpha_plus) * (1.0 - alpha_minus)
    stella_premul = stella_rgb  # already on black, premul = straight
    return stella_premul, stella_alpha


def panel_e(ax):
    """(e) Physics correspondence table."""
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')
    ax.set_title('(e) Physics correspondence', fontsize=11, fontweight='bold')

    rows = [
        ('Graphical Operation',        'Framework'),
        ('RGB gradients (120° apart)',  r'$\chi_R, \chi_G, \chi_B$ (Def 0.1.2)'),
        ('Opacity fade',               r'$P_c(x)$ pressure (Def 0.1.3)'),
        ('120° rotation angles',       r'Phases $\{0, 2\pi/3, 4\pi/3\}$'),
        ('Additive blend',             r'$\chi_{\mathrm{total}} = \sum \chi_c$ (Thm 0.2.1)'),
        ('180° rotation',              r'Charge conj. $T_- = -T_+$ (Thm 1.1.2)'),
        ('T₊(RGB) + T₋(CMY) layered',  r'$\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ (Def 0.1.1)'),
    ]

    y0 = 0.92
    dy = 0.12
    for i, (left, right) in enumerate(rows):
        y = y0 - i * dy
        weight = 'bold' if i == 0 else 'normal'
        size = 10 if i == 0 else 9.5
        ax.text(0.02, y, left,  fontsize=size, fontweight=weight,
                va='center', ha='left', family='sans-serif')
        ax.text(0.55, y, right, fontsize=size, fontweight=weight,
                va='center', ha='left', family='sans-serif')
    ax.plot([0.02, 0.98], [y0 - 0.5 * dy, y0 - 0.5 * dy],
            '-', color='gray', lw=0.5)


def panel_f(ax, stella_premul, stella_alpha):
    """(f) Stella wireframe overlaid on 6-lobe stella."""
    ax.imshow(stella_premul, extent=[-EXTENT, EXTENT, -EXTENT, EXTENT])
    ax.set_facecolor('black')
    ax.set_title('(f) Wireframe overlay verification',
                 fontsize=11, fontweight='bold')
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    stella_wireframe(ax, r=R_TRI)
    ax.legend(loc='lower right', fontsize=9, framealpha=0.7)


# ===========================================================================
# Main
# ===========================================================================

def main():
    fig = plt.figure(figsize=(16, 16), facecolor='white')
    gs = GridSpec(3, 3, figure=fig, hspace=0.30, wspace=0.25)

    # Row 0: individual gradients (R→M, G→Y, B→C)
    ax_r = fig.add_subplot(gs[0, 0])
    ax_g = fig.add_subplot(gs[0, 1])
    ax_b = fig.add_subplot(gs[0, 2])

    # Row 1: composite operations
    ax_a = fig.add_subplot(gs[1, 0])
    ax_b2 = fig.add_subplot(gs[1, 1])
    ax_c = fig.add_subplot(gs[1, 2])

    # Row 2: stella construction
    ax_d = fig.add_subplot(gs[2, 0])
    ax_e = fig.add_subplot(gs[2, 1])
    ax_f = fig.add_subplot(gs[2, 2])

    layers = _build_layers()   # [R, G, B]

    # Compute Linear Dodge composite once (shared by panels a–d)
    premul_plus, alpha_plus = linear_dodge_composite(layers)

    # Row 0: individual color fields (gradient on checkerboard)
    panel_single_gradient(ax_r, layers[0], C_RED,   r'$\chi_R$ (Red)',   ANGLES_DEG[0])
    panel_single_gradient(ax_g, layers[1], C_GREEN, r'$\chi_G$ (Green)', ANGLES_DEG[1])
    panel_single_gradient(ax_b, layers[2], C_BLUE,  r'$\chi_B$ (Blue)',  ANGLES_DEG[2])

    # Row 1 — all on checkerboard
    panel_a(ax_a, premul_plus, alpha_plus)
    panel_b(ax_b2, premul_plus, alpha_plus)
    premul_minus, alpha_minus = panel_c(ax_c, premul_plus, alpha_plus)

    # Row 2 — stella construction
    stella_premul, stella_alpha = panel_d(ax_d, premul_plus, alpha_plus,
                                          premul_minus, alpha_minus)
    panel_e(ax_e)
    panel_f(ax_f, stella_premul, stella_alpha)

    fig.suptitle(
        'Color Field Superposition → Stella Octangula',
        fontsize=14, fontweight='bold', y=0.98
    )

    base = os.path.join(PLOT_DIR, "fig_color_superposition_stella")
    fig.savefig(base + ".png", dpi=300, bbox_inches='tight', facecolor='white')
    fig.savefig(base + ".pdf", bbox_inches='tight', facecolor='white')
    print(f"Saved: {base}.png")
    print(f"Saved: {base}.pdf")
    plt.close('all')


if __name__ == "__main__":
    main()
