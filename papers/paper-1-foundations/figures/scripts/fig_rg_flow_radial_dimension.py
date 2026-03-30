#!/usr/bin/env python3
"""
Figure: RG Flow as a Curve in Coupling Space

Visualizes the argument from Proposition embedding-dim that confinement
contributes exactly one radial direction:
  - The SU(3) weight space is 2D (Cartan subalgebra, rank 2)
  - The β-function β(α_s) = μ dα_s/dμ is a single function of one variable
  - RG flow traces a 1D curve, not a 2D surface → exactly +1 radial direction

Panel (a): 3D view — weight diagram as horizontal plane, RG flow curve
           rising orthogonally, showing it adds exactly one dimension
Panel (b): The running coupling α_s(μ) — one-loop QCD with asymptotic
           freedom, marking the confinement scale R_conf = ℏc/√σ

Output: fig_rg_flow_radial_dimension.pdf
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from pathlib import Path
from matplotlib.patches import FancyArrowPatch
from mpl_toolkits.mplot3d import proj3d

# Output directory (parent of scripts folder = figures folder)
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)


# ── QCD running coupling (one-loop, matching formula) ────────────────────
# Uses the formula from coupling-constants.md and verification scripts:
#   1/α_s(μ) = 1/α_s(μ₀) + (b₀/(2π)) ln(μ/μ₀)
# where b₀ = 11 - 2n_f/3  (Prop 0.0.40 §C2, Peskin & Schroeder convention)
#
# Reference values (PDG 2024, coupling-constants.md):
#   α_s(M_Z) = 0.1180 ± 0.0009
#   Flavor thresholds: m_c = 1.27 GeV, m_b = 4.18 GeV

ALPHA_S_MZ = 0.1180   # PDG 2024 (coupling-constants.md)
M_Z = 91.2            # GeV

# Threshold masses (PDG 2024, alpha_s_two_loop_running.py)
M_CHARM = 1.27   # GeV
M_BOTTOM = 4.18  # GeV


def alpha_s_one_loop_matching(mu_arr, mu_ref, alpha_ref, n_f):
    """One-loop running via matching formula (coupling-constants.md §2.1).

    1/α_s(μ) = 1/α_s(μ_ref) + (b₀/(2π)) ln(μ/μ_ref)
    b₀ = 11 - 2n_f/3
    """
    b0 = 11.0 - 2.0 * n_f / 3.0
    alpha_inv = 1.0 / alpha_ref + (b0 / (2.0 * np.pi)) * np.log(mu_arr / mu_ref)
    result = np.where(alpha_inv > 0, 1.0 / alpha_inv, np.nan)
    return result


# ── Panel (a): 3D Weight Space + Radial RG Direction ─────────────────────

def plot_3d_weight_plus_rg(ax):
    """3D view: 2D weight space as base, RG flow curve rising orthogonally."""

    # ── Weight diagram in the z=0 plane ──
    # SU(3) fundamental weights
    w_R = np.array([0.5, 1 / (2 * np.sqrt(3))])
    w_G = np.array([-0.5, 1 / (2 * np.sqrt(3))])
    w_B = np.array([0, -1 / np.sqrt(3)])
    w_Rbar, w_Gbar, w_Bbar = -w_R, -w_G, -w_B

    weights_fund = [w_R, w_G, w_B]
    weights_anti = [w_Rbar, w_Gbar, w_Bbar]

    # Draw fundamental triangle (blue, in z=0 plane)
    tri_fund = np.array([list(w) + [0] for w in weights_fund + [weights_fund[0]]])
    ax.plot(tri_fund[:, 0], tri_fund[:, 1], tri_fund[:, 2],
            'b-', linewidth=2, alpha=0.7)

    # Draw anti-fundamental triangle (red, dashed)
    tri_anti = np.array([list(w) + [0] for w in weights_anti + [weights_anti[0]]])
    ax.plot(tri_anti[:, 0], tri_anti[:, 1], tri_anti[:, 2],
            'r--', linewidth=2, alpha=0.7)

    # Fill triangles as semi-transparent surfaces
    verts_fund = [[list(w) + [0] for w in weights_fund]]
    poly_fund = Poly3DCollection(verts_fund, alpha=0.12, facecolor='blue',
                                  edgecolor='none')
    ax.add_collection3d(poly_fund)

    verts_anti = [[list(w) + [0] for w in weights_anti]]
    poly_anti = Poly3DCollection(verts_anti, alpha=0.08, facecolor='red',
                                  edgecolor='none')
    ax.add_collection3d(poly_anti)

    # Plot weight vertices
    colors_f = ['#e74c3c', '#27ae60', '#3498db']
    for w, c in zip(weights_fund, colors_f):
        ax.scatter(w[0], w[1], 0, c=c, s=100, edgecolor='black',
                   linewidth=1, zorder=5)
    colors_a = ['#c0392b', '#1e8449', '#2874a6']
    for w, c in zip(weights_anti, colors_a):
        ax.scatter(w[0], w[1], 0, c=c, s=80, marker='s', edgecolor='black',
                   linewidth=1, zorder=5)

    # Origin
    ax.scatter(0, 0, 0, c='gold', s=120, marker='*', edgecolor='black',
               linewidth=1.5, zorder=6)

    # ── Semi-transparent gray plane to emphasize the 2D weight space ──
    plane_size = 0.85
    xx = np.array([[-plane_size, plane_size, plane_size, -plane_size]])
    yy = np.array([[-plane_size, -plane_size, plane_size, plane_size]])
    zz = np.zeros_like(xx)
    plane_verts = [list(zip(xx[0], yy[0], zz[0]))]
    plane_poly = Poly3DCollection(plane_verts, alpha=0.06, facecolor='gray',
                                   edgecolor='gray', linewidth=0.5,
                                   linestyle=':')
    ax.add_collection3d(plane_poly)

    # ── RG flow curve (the single radial direction) ──
    # Parameterize as z = energy scale, x = y = 0 (at origin of weight space)
    # The curve α_s(μ) lives along a single line orthogonal to the plane.
    # We show it as a bold curve at the origin, going upward.

    # Energy scale from confinement to UV
    z_vals = np.linspace(0.0, 2.0, 200)

    # Map z to a mock coupling that shows asymptotic freedom
    # Use a smooth curve: strong at z=0 (IR), weak at z→∞ (UV)
    # α_s ~ 1/(b₀ ln(μ/Λ)) shape
    alpha_curve = 0.7 / (1.0 + 1.5 * z_vals)  # smooth monotonic decrease

    # Plot the RG flow curve as a bold line at origin, going up
    # Small x-displacement proportional to α_s to show it's truly a curve
    x_curve = alpha_curve * 0.6  # coupling gives slight x-offset for visibility
    y_curve = np.zeros_like(z_vals)

    ax.plot(x_curve, y_curve, z_vals, color='#8B0000', linewidth=3.5,
            zorder=10, label='RG flow (1D curve)')

    # Arrow at the UV end (asymptotic freedom direction)
    ax.quiver(x_curve[-1], y_curve[-1], z_vals[-1],
              x_curve[-1] - x_curve[-2], 0,
              z_vals[-1] - z_vals[-2],
              color='#8B0000', arrow_length_ratio=0.6, linewidth=2)

    # ── Mark confinement scale ──
    z_conf = 0.0  # confinement at the base
    ax.scatter(x_curve[0], 0, z_conf, c='#8B0000', s=100, marker='D',
               edgecolor='black', linewidth=1.5, zorder=10)
    ax.text(x_curve[0] + 0.15, 0.05, z_conf + 0.35,
            r'$\Lambda_{\mathrm{QCD}}$',
            fontsize=11, color='#8B0000', fontweight='bold')

    # ── Dashed projection line from curve to base ──
    for z_mark in [0.5, 1.0, 1.5]:
        idx = np.argmin(np.abs(z_vals - z_mark))
        ax.plot([x_curve[idx], 0], [0, 0], [z_mark, z_mark],
                'k:', linewidth=0.8, alpha=0.4)
        ax.plot([0, 0], [0, 0], [0, z_mark],
                'k:', linewidth=0.8, alpha=0.3)

    # ── Annotations ──
    # Label the 2D plane
    ax.text(-0.10, -0.75, -0.15, r'$\mathfrak{h}^*$ (2D weight space)',
            fontsize=10, color='#333333', style='italic')

    # Label the radial direction
    ax.text(-0.15, -0.3, 2.25, r'$\mu$ (energy scale)',
            fontsize=10, color='#8B0000', fontweight='bold')

    # Label "curve, not surface"
    ax.text(0.45, -0.15, 1.0,
            'curve\n(not surface)',
            fontsize=9, color='#8B0000', style='italic',
            ha='left', va='center')

    # ── Axis settings ──
    ax.set_xlabel(r'$h_1^*$', fontsize=11, labelpad=5)
    ax.set_ylabel(r'$h_2^*$', fontsize=11, labelpad=5)
    ax.set_zlabel(r'$r \sim 1/\mu$', fontsize=11, labelpad=5)

    ax.set_xlim([-0.9, 0.9])
    ax.set_ylim([-0.9, 0.9])
    ax.set_zlim([-0.1, 2.2])

    ax.set_box_aspect([1, 1, 1.3])
    ax.view_init(elev=22, azim=-55)

    ax.set_title('(a) RG flow adds one radial direction to color space\n'
                 '2 (weight) + 1 (radial) = 3',
                 fontsize=11, fontweight='bold', pad=10)


# ── Panel (b): Running coupling α_s(μ) ──────────────────────────────────

def plot_running_coupling(ax):
    """Plot the QCD running coupling showing it's a single curve."""

    # Energy scale in GeV
    mu = np.linspace(0.5, 100, 500)

    # Build composite running with threshold matching
    # (same approach as verification/Phase2/alpha_s_two_loop_running.py)
    # Run down from M_Z with n_f=5, then match at thresholds
    alpha_at_mb = alpha_s_one_loop_matching(
        np.array([M_BOTTOM]), M_Z, ALPHA_S_MZ, n_f=5)[0]
    alpha_at_mc = alpha_s_one_loop_matching(
        np.array([M_CHARM]), M_BOTTOM, alpha_at_mb, n_f=4)[0]

    # Compute α_s(μ) in each flavor regime
    alpha_5 = alpha_s_one_loop_matching(mu, M_Z, ALPHA_S_MZ, n_f=5)
    alpha_4 = alpha_s_one_loop_matching(mu, M_BOTTOM, alpha_at_mb, n_f=4)
    alpha_3 = alpha_s_one_loop_matching(mu, M_CHARM, alpha_at_mc, n_f=3)

    # Composite: select appropriate n_f for each μ
    alpha_composite = np.copy(alpha_3)
    alpha_composite[mu > M_CHARM] = alpha_4[mu > M_CHARM]
    alpha_composite[mu > M_BOTTOM] = alpha_5[mu > M_BOTTOM]

    # Plot
    ax.plot(mu, alpha_composite, color='#8B0000', linewidth=2.5,
            label=r'$\alpha_s(\mu)$ (one-loop)')

    # Shade confinement region
    ax.axvspan(0, 0.5, color='#FFE0E0', alpha=0.5)
    # Λ_MS^(5) = 210 MeV (PDG 2024, Prop 0.0.40 §C3)
    Lambda_QCD_5 = 0.210
    ax.axvline(x=Lambda_QCD_5, color='gray', linestyle='--', linewidth=1, alpha=0.7)
    ax.text(0.23, 0.85, r'$\Lambda_{\overline{MS}}^{(5)}$',
            fontsize=10, color='gray', transform=ax.get_yaxis_transform())

    # Mark confinement scale: √σ = ℏc/R_stella (Physical-Constants-and-Data.md)
    # R_stella = 0.44847 fm, ℏc = 197.327 MeV·fm → √σ = 440.0 MeV
    mu_conf = 0.1973270 / 0.44847  # ℏc/R_stella in GeV ≈ 0.440 GeV
    ax.axvline(x=mu_conf, color='#e74c3c', linestyle=':', linewidth=1.5, alpha=0.8)
    ax.annotate(r'$\sqrt{\sigma} = \hbar c / R_{\mathrm{stella}}$',
                xy=(mu_conf, 0.6), xytext=(1.5, 0.7),
                fontsize=9, color='#e74c3c',
                arrowprops=dict(arrowstyle='->', color='#e74c3c', lw=1.2))

    # Mark M_Z reference point (PDG 2024, coupling-constants.md §2)
    ax.scatter(M_Z, ALPHA_S_MZ, c='black', s=60, zorder=5, edgecolor='black')
    ax.annotate(r'$\alpha_s(M_Z) = 0.1180$',
                xy=(M_Z, ALPHA_S_MZ), xytext=(40, 0.25),
                fontsize=9,
                arrowprops=dict(arrowstyle='->', color='black', lw=1))

    # Asymptotic freedom arrow
    ax.annotate('', xy=(90, 0.08), xytext=(5, 0.08),
                arrowprops=dict(arrowstyle='->', color='#27ae60',
                                lw=2, alpha=0.6))
    ax.text(30, 0.04, 'Asymptotic freedom', fontsize=9, color='#27ae60',
            ha='center', style='italic')

    # Strong coupling arrow
    ax.annotate('', xy=(0.5, 0.75), xytext=(3, 0.75),
                arrowprops=dict(arrowstyle='->', color='#e74c3c',
                                lw=2, alpha=0.6))
    ax.text(1.2, 0.82, 'Confinement', fontsize=9, color='#e74c3c',
            ha='center', style='italic')

    ax.set_xlabel(r'Energy scale $\mu$ (GeV)', fontsize=11)
    ax.set_ylabel(r'$\alpha_s(\mu)$', fontsize=11)
    ax.set_title(r'(b) $\beta(\alpha_s) = \mu\,d\alpha_s/d\mu$: one function of one variable'
                 '\n'
                 r'$\Rightarrow$ one radial direction',
                 fontsize=11, fontweight='bold')

    ax.set_xscale('log')
    ax.set_xlim(0.4, 120)
    ax.set_ylim(0, 1.0)
    ax.grid(True, alpha=0.3, which='both')
    ax.legend(loc='upper center', fontsize=9)


# ── Main ─────────────────────────────────────────────────────────────────

def main():
    """Generate the RG flow radial dimension figure."""

    fig = plt.figure(figsize=(14, 6))

    # Panel (a): 3D
    ax1 = fig.add_subplot(1, 2, 1, projection='3d')
    plot_3d_weight_plus_rg(ax1)

    # Panel (b): 2D running coupling
    ax2 = fig.add_subplot(1, 2, 2)
    plot_running_coupling(ax2)

    fig.suptitle(
        r'RG Flow Contributes Exactly One Radial Direction',
        fontsize=13, fontweight='bold', y=1.02)

    plt.tight_layout(rect=[0, 0, 1, 0.98])

    # Save
    for ext in ['pdf', 'png']:
        filepath = output_dir / f'fig_rg_flow_radial_dimension.{ext}'
        fig.savefig(filepath, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    plt.close()
    print("Done!")


if __name__ == "__main__":
    main()
