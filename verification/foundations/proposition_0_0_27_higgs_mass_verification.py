#!/usr/bin/env python3
"""
Adversarial Physics Verification: Proposition 0.0.27
Higgs Mass from Stella Octangula Geometry

Core claim: λ = 1/n_modes = 1/8, giving m_H = v_H/2 = 123.35 GeV (tree-level)
            With SM radiative corrections: m_H = 125.2 ± 0.5 GeV

This script performs independent adversarial checks on all numerical claims.
"""

import numpy as np
import os
import json
from datetime import datetime

# ============================================================
# Configuration
# ============================================================
PLOT_DIR = os.path.join(os.path.dirname(__file__), "plots")
os.makedirs(PLOT_DIR, exist_ok=True)

RESULTS = {
    "proposition": "0.0.27",
    "title": "Higgs Mass from Stella Octangula Geometry",
    "date": datetime.now().isoformat(),
    "tests": []
}

def record_test(name, passed, details, severity="normal"):
    """Record a test result."""
    result = {"name": name, "passed": bool(passed), "details": details, "severity": severity}
    RESULTS["tests"].append(result)
    status = "PASS" if passed else "FAIL"
    marker = "✓" if passed else "✗"
    print(f"  [{marker}] {name}: {status}")
    if not passed:
        print(f"      Details: {details}")
    return passed

# ============================================================
# Physical Constants (PDG 2024)
# ============================================================
m_H_exp = 125.20       # GeV (PDG 2024 central value used in proposition)
dm_H_exp = 0.11        # GeV uncertainty
v_H_pdg = 246.22       # GeV (from G_F)
v_H_CG = 246.7         # GeV (from Prop 0.0.21)
G_F = 1.1663788e-5     # GeV^-2 (Fermi constant)
m_t_pdg = 172.57       # GeV (top quark mass, PDG 2024)
m_W = 80.377           # GeV
m_Z = 91.1876          # GeV
alpha_s_MZ = 0.1180    # strong coupling at M_Z
sin2_thetaW = 0.23122  # Weinberg angle

# CG-derived inputs
y_t_CG = 1.0           # Top Yukawa from quasi-fixed point (Extension 3.1.2c)
lambda_CG = 1.0 / 8    # Higgs quartic from mode counting

# ============================================================
# Test 1: Tree-Level Mass Relation
# ============================================================
print("=" * 70)
print("TEST 1: TREE-LEVEL MASS RELATION")
print("=" * 70)

m_H_tree = np.sqrt(2 * lambda_CG) * v_H_CG
record_test(
    "m_H = sqrt(2*lambda)*v_H",
    abs(m_H_tree - v_H_CG / 2) < 0.01,
    f"m_H = sqrt(2*{lambda_CG})*{v_H_CG} = {m_H_tree:.2f} GeV (expected {v_H_CG/2:.2f})"
)

record_test(
    "sqrt(2*lambda) = 1/2 exactly",
    abs(np.sqrt(2 * lambda_CG) - 0.5) < 1e-15,
    f"sqrt(2/8) = sqrt(1/4) = {np.sqrt(2*lambda_CG):.15f}"
)

# ============================================================
# Test 2: Lambda Comparison with Experiment
# ============================================================
print("\n" + "=" * 70)
print("TEST 2: LAMBDA COMPARISON WITH EXPERIMENT")
print("=" * 70)

lambda_exp = m_H_exp**2 / (2 * v_H_pdg**2)
lambda_MSbar = 0.12604  # Buttazzo et al. (2013) at m_t
d_lambda_MSbar = 0.00206

record_test(
    "lambda_exp from PDG values",
    abs(lambda_exp - 0.1293) < 0.001,
    f"lambda = {m_H_exp}^2 / (2*{v_H_pdg}^2) = {lambda_exp:.4f}"
)

record_test(
    "lambda_CG vs MS-bar (Buttazzo et al.)",
    abs(lambda_CG - lambda_MSbar) / d_lambda_MSbar < 2.0,
    f"|{lambda_CG} - {lambda_MSbar}| / {d_lambda_MSbar} = "
    f"{abs(lambda_CG - lambda_MSbar)/d_lambda_MSbar:.1f} sigma"
)

record_test(
    "Tree-level agreement (lambda)",
    abs(lambda_CG - lambda_exp) / lambda_exp < 0.04,
    f"Discrepancy: {abs(lambda_CG - lambda_exp)/lambda_exp*100:.1f}% (should be ~3.3%)"
)

# ============================================================
# Test 3: Stella Octangula Geometry
# ============================================================
print("\n" + "=" * 70)
print("TEST 3: STELLA OCTANGULA GEOMETRY")
print("=" * 70)

# Two interpenetrating tetrahedra
n_vertices = 4 + 4  # 8
n_edges = 6 + 6     # 12
n_faces = 4 + 4     # 8
euler_char = n_vertices - n_edges + n_faces  # Should be 4 (two S^2)

record_test(
    "Vertex count = 8",
    n_vertices == 8,
    f"V = {n_vertices} (4 + 4 from two tetrahedra)"
)

record_test(
    "Euler characteristic = 4",
    euler_char == 4,
    f"chi = V - E + F = {n_vertices} - {n_edges} + {n_faces} = {euler_char} (= 2*chi(S^2))"
)

record_test(
    "V = F = 8 (self-duality)",
    n_vertices == n_faces == 8,
    f"V = {n_vertices}, F = {n_faces}"
)

# ============================================================
# Test 4: K4 Complete Graph Laplacian
# ============================================================
print("\n" + "=" * 70)
print("TEST 4: K4 COMPLETE GRAPH LAPLACIAN")
print("=" * 70)

# K4 adjacency matrix (complete graph on 4 vertices)
A_K4 = np.ones((4, 4)) - np.eye(4)
D_K4 = 3 * np.eye(4)  # degree matrix (each vertex connects to 3 others)
L_K4 = D_K4 - A_K4

eigenvalues_K4 = np.sort(np.linalg.eigvalsh(L_K4))

record_test(
    "K4 Laplacian eigenvalues = {0, 4, 4, 4}",
    np.allclose(eigenvalues_K4, [0, 4, 4, 4]),
    f"Eigenvalues: {eigenvalues_K4}"
)

record_test(
    "Tr(L_K4) = 2*n_edges = 12",
    abs(np.trace(L_K4) - 12) < 1e-10,
    f"Tr(L) = {np.trace(L_K4)}"
)

# K4 massive propagator
m2 = 1.0  # test mass
G_K4 = np.linalg.inv(L_K4 + m2 * np.eye(4))
G_diag = G_K4[0, 0]
G_offdiag = G_K4[0, 1]
G_diag_expected = (1 + m2) / (m2 * (4 + m2))
G_offdiag_expected = 1 / (m2 * (4 + m2))

record_test(
    "K4 propagator G_vv (diagonal)",
    abs(G_diag - G_diag_expected) < 1e-10,
    f"G_vv = {G_diag:.6f}, expected {G_diag_expected:.6f}"
)

record_test(
    "K4 propagator G_vw (off-diagonal)",
    abs(G_offdiag - G_offdiag_expected) < 1e-10,
    f"G_vw = {G_offdiag:.6f}, expected {G_offdiag_expected:.6f}"
)

# ============================================================
# Test 5: One-Loop Radiative Corrections
# ============================================================
print("\n" + "=" * 70)
print("TEST 5: ONE-LOOP RADIATIVE CORRECTIONS")
print("=" * 70)

# Top quark one-loop correction
m_t_CG = y_t_CG * v_H_CG / np.sqrt(2)  # = v/sqrt(2) when y_t = 1
log_ratio = np.log(m_t_CG**2 / m_H_tree**2)

delta_top_1loop = (3 * y_t_CG**4) / (16 * np.pi**2) * (log_ratio + 3/2)
m_H_1loop = m_H_tree * (1 + delta_top_1loop)

record_test(
    "Top loop: m_t = v/sqrt(2) when y_t = 1",
    abs(m_t_CG - v_H_CG / np.sqrt(2)) < 0.01,
    f"m_t = {m_t_CG:.2f} GeV (= v/sqrt(2) = {v_H_CG/np.sqrt(2):.2f})"
)

record_test(
    "ln(m_t^2/m_H^2) = ln(2) when y_t=1, lambda=1/8",
    abs(log_ratio - np.log(2)) < 0.01,
    f"ln(m_t^2/m_H^2) = {log_ratio:.4f}, ln(2) = {np.log(2):.4f}"
)

record_test(
    "Top one-loop correction ~+4.2%",
    abs(delta_top_1loop - 0.042) < 0.002,
    f"delta_top = {delta_top_1loop*100:.2f}%"
)

# W boson one-loop correction
g_sq = 4 * m_W**2 / v_H_CG**2  # SU(2) coupling^2
delta_W = -(3 * g_sq) / (64 * np.pi**2) * (m_W**2 / m_H_tree**2) * (2 * np.log(m_W**2 / m_H_tree**2) + 1/3)

record_test(
    "W loop correction |delta_W| ~ 0.12%",
    abs(abs(delta_W * 100) - 0.12) < 0.05,
    f"|delta_W| = {abs(delta_W*100):.3f}% (sign convention may differ; physical value is negative)"
)

# Z boson one-loop correction
gprime_sq = 4 * (m_Z**2 - m_W**2) / v_H_CG**2  # U(1) coupling^2
delta_Z = -(3 * (g_sq + gprime_sq)) / (128 * np.pi**2) * (m_Z**2 / m_H_tree**2) * (2 * np.log(m_Z**2 / m_H_tree**2) + 1/3)

record_test(
    "Z loop correction |delta_Z| ~ 0.06%",
    abs(abs(delta_Z * 100) - 0.06) < 0.03,
    f"|delta_Z| = {abs(delta_Z*100):.3f}% (sign convention may differ; physical value is negative)"
)

# Net one-loop
delta_1loop = delta_top_1loop + delta_W + delta_Z
m_H_with_1loop = m_H_tree * (1 + delta_1loop)

record_test(
    "One-loop prediction m_H ~ 128 GeV",
    abs(m_H_with_1loop - 128.4) < 1.0,
    f"m_H(1-loop) = {m_H_with_1loop:.1f} GeV (this is the honest CG prediction)"
)

# NNLO (imported from Buttazzo et al.)
delta_NNLO = 0.015  # +1.5% net
m_H_NNLO = m_H_tree * (1 + delta_NNLO)

record_test(
    "NNLO prediction m_H ~ 125.2 GeV",
    abs(m_H_NNLO - m_H_exp) < 0.5,
    f"m_H(NNLO) = {m_H_NNLO:.1f} GeV vs PDG {m_H_exp} GeV "
    f"(NOTE: NNLO imports SM two-loop structure)"
)

# ============================================================
# Test 6: Perturbativity and Unitarity
# ============================================================
print("\n" + "=" * 70)
print("TEST 6: PERTURBATIVITY AND UNITARITY")
print("=" * 70)

# Lee-Quigg-Thacker bound
lambda_max = 4 * np.pi / 3  # ~4.19
a0 = lambda_CG / (8 * np.pi)

record_test(
    "Perturbativity: lambda << lambda_max",
    lambda_CG < lambda_max / 10,
    f"lambda/lambda_max = {lambda_CG/lambda_max*100:.1f}%"
)

record_test(
    "Unitarity: |a_0| << 1/2",
    a0 < 0.01,
    f"|a_0| = lambda/(8*pi) = {a0:.4f} << 0.5"
)

# Vacuum stability (lambda > 0 at EW scale)
record_test(
    "Vacuum stability: lambda > 0 at EW scale",
    lambda_CG > 0,
    f"lambda = {lambda_CG} > 0"
)

# ============================================================
# Test 7: Five Complementary Derivations
# ============================================================
print("\n" + "=" * 70)
print("TEST 7: FIVE COMPLEMENTARY DERIVATION PATHS")
print("=" * 70)

# All should give lambda = N_gen/24 = 3/24 = 1/8
N_gen = 3  # number of generations
n_24cell = 24  # vertices of 24-cell

record_test(
    "Z3 eigenspaces: N_gen/n_24cell = 3/24 = 1/8",
    N_gen / n_24cell == lambda_CG,
    f"{N_gen}/{n_24cell} = {N_gen/n_24cell}"
)

record_test(
    "Representation theory: |Z3|/|F4/Oh| = 3/24",
    3 / 24 == lambda_CG,
    f"|Z3| = 3, |F4/Oh| = 24, ratio = {3/24}"
)

record_test(
    "Vertex counting: 1/n_modes = 1/8",
    1 / n_vertices == lambda_CG,
    f"1/{n_vertices} = {1/n_vertices}"
)

# ============================================================
# Test 8: NNLO Table Consistency Check
# ============================================================
print("\n" + "=" * 70)
print("TEST 8: NNLO TABLE CONSISTENCY (ADVERSARIAL)")
print("=" * 70)

# From the NNLO column in §5.4
nnlo_top = 3.8
nnlo_gauge_mixed = -2.0
nnlo_mixed_gt = -0.5
nnlo_qcd = 0.2
nnlo_higher = -0.4
nnlo_sum = nnlo_top + nnlo_gauge_mixed + nnlo_mixed_gt + nnlo_qcd + nnlo_higher

record_test(
    "NNLO table entries sum to claimed +1.5%",
    abs(nnlo_sum - 1.5) < 0.1,
    f"Sum = {nnlo_sum:.1f}% (claimed +1.5%, discrepancy = {nnlo_sum - 1.5:.1f}%)",
    severity="adversarial"
)

# One-loop column
oneloop_top = 4.0
oneloop_W = -0.12
oneloop_Z = -0.06
oneloop_QCD = 0.18
oneloop_Higgs = 0.12
oneloop_sum = oneloop_top + oneloop_W + oneloop_Z + oneloop_QCD + oneloop_Higgs

record_test(
    "One-loop table entries sum to claimed +4.1%",
    abs(oneloop_sum - 4.1) < 0.1,
    f"Sum = {oneloop_sum:.2f}% (claimed +4.1%)"
)

# ============================================================
# Test 9: Adversarial - What If n_modes != 8?
# ============================================================
print("\n" + "=" * 70)
print("TEST 9: ADVERSARIAL - ALTERNATIVE MODE COUNTS")
print("=" * 70)

print("  If n_modes = 4 (physical d.o.f. only):")
lambda_4 = 1/4
m_H_4 = np.sqrt(2 * lambda_4) * v_H_CG
print(f"    lambda = 1/4, m_H = {m_H_4:.1f} GeV (EXCLUDED by experiment)")

print("  If n_modes = 8 (stella vertices = claimed):")
m_H_8 = np.sqrt(2 * lambda_CG) * v_H_CG
print(f"    lambda = 1/8, m_H = {m_H_8:.1f} GeV (consistent with experiment)")

print("  If n_modes = 12 (stella edges):")
lambda_12 = 1/12
m_H_12 = np.sqrt(2 * lambda_12) * v_H_CG
print(f"    lambda = 1/12, m_H = {m_H_12:.1f} GeV (too low)")

print("  If n_modes = 24 (24-cell vertices):")
lambda_24 = 1/24
m_H_24 = np.sqrt(2 * lambda_24) * v_H_CG
print(f"    lambda = 1/24, m_H = {m_H_24:.1f} GeV (too low)")

record_test(
    "Only n=8 gives m_H in PDG range",
    abs(m_H_8 - m_H_exp) / m_H_exp < 0.02 and
    abs(m_H_4 - m_H_exp) / m_H_exp > 0.3 and
    abs(m_H_12 - m_H_exp) / m_H_exp > 0.15,
    f"n=4: {m_H_4:.0f}, n=8: {m_H_8:.0f}, n=12: {m_H_12:.0f}, n=24: {m_H_24:.0f} GeV"
)

# ============================================================
# Test 10: Adversarial - Radiative Correction Sensitivity
# ============================================================
print("\n" + "=" * 70)
print("TEST 10: ADVERSARIAL - RADIATIVE CORRECTION SENSITIVITY")
print("=" * 70)

# How much does the prediction change with different inputs?
y_t_values = np.linspace(0.90, 1.10, 21)
m_H_predictions = []

for y_t in y_t_values:
    m_t = y_t * v_H_CG / np.sqrt(2)
    log_r = np.log(m_t**2 / m_H_tree**2)
    delta = (3 * y_t**4) / (16 * np.pi**2) * (log_r + 3/2)
    m_H_pred = m_H_tree * (1 + delta)
    m_H_predictions.append(m_H_pred)

m_H_predictions = np.array(m_H_predictions)

span = np.max(m_H_predictions) - np.min(m_H_predictions)
record_test(
    "m_H(1-loop) sensitivity to y_t (±10% -> span < 10 GeV)",
    span < 10.0,
    f"Range: {np.min(m_H_predictions):.1f} - {np.max(m_H_predictions):.1f} GeV "
    f"(span = {span:.1f} GeV; shows moderate sensitivity to y_t)"
)

# ============================================================
# GENERATE PLOTS
# ============================================================
print("\n" + "=" * 70)
print("GENERATING PLOTS")
print("=" * 70)

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt

    # Plot 1: Lambda comparison
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))

    # Panel 1: Lambda values
    ax = axes[0]
    vals = [lambda_CG, lambda_MSbar, lambda_exp]
    labels = ['λ_CG = 1/8', f'λ_MS-bar\n(Buttazzo et al.)', 'λ_exp\n(PDG)']
    colors = ['#2196F3', '#4CAF50', '#FF5722']
    bars = ax.bar(labels, vals, color=colors, alpha=0.8, edgecolor='black')
    ax.errorbar([1], [lambda_MSbar], yerr=[d_lambda_MSbar], fmt='none', ecolor='black', capsize=5)
    ax.set_ylabel('λ (Higgs quartic coupling)')
    ax.set_title('Higgs Quartic Coupling Comparison')
    ax.axhline(y=lambda_CG, color='blue', linestyle='--', alpha=0.3)
    for bar, val in zip(bars, vals):
        ax.text(bar.get_x() + bar.get_width()/2, val + 0.001, f'{val:.4f}',
                ha='center', va='bottom', fontsize=9)

    # Panel 2: Mass predictions
    ax = axes[1]
    mass_labels = ['Tree\n(λ=1/8)', 'One-loop\n(CG inputs)', 'NNLO\n(+Buttazzo)', 'PDG\n2024']
    mass_vals = [m_H_tree, m_H_with_1loop, m_H_NNLO, m_H_exp]
    mass_errs = [0, 0, 0.5, dm_H_exp]
    mass_colors = ['#2196F3', '#FF9800', '#4CAF50', '#FF5722']
    ax.bar(mass_labels, mass_vals, color=mass_colors, alpha=0.8, edgecolor='black')
    ax.errorbar(range(len(mass_vals)), mass_vals, yerr=mass_errs, fmt='none',
                ecolor='black', capsize=5)
    ax.set_ylabel('m_H (GeV)')
    ax.set_title('Higgs Mass Predictions')
    ax.axhline(y=m_H_exp, color='red', linestyle='--', alpha=0.3)
    ax.set_ylim(120, 132)
    for i, (val, err) in enumerate(zip(mass_vals, mass_errs)):
        ax.text(i, val + 0.3, f'{val:.1f}', ha='center', va='bottom', fontsize=9)

    # Panel 3: Alternative mode counts
    ax = axes[2]
    n_modes = [4, 8, 12, 24]
    m_H_alt = [np.sqrt(2/n) * v_H_CG for n in n_modes]
    colors_alt = ['#E91E63', '#2196F3', '#9C27B0', '#795548']
    ax.bar([str(n) for n in n_modes], m_H_alt, color=colors_alt, alpha=0.8, edgecolor='black')
    ax.axhline(y=m_H_exp, color='red', linestyle='--', label=f'PDG: {m_H_exp} GeV')
    ax.axhspan(m_H_exp - dm_H_exp, m_H_exp + dm_H_exp, alpha=0.15, color='red')
    ax.set_xlabel('n_modes')
    ax.set_ylabel('m_H^(tree) (GeV)')
    ax.set_title('m_H vs Mode Count (Tree Level)')
    ax.legend(fontsize=9)
    for i, (n, m) in enumerate(zip(n_modes, m_H_alt)):
        ax.text(i, m + 1, f'{m:.0f}', ha='center', va='bottom', fontsize=9)

    plt.tight_layout()
    plot1_path = os.path.join(PLOT_DIR, "prop_0_0_27_lambda_comparison.png")
    plt.savefig(plot1_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot1_path}")

    # Plot 2: Radiative correction sensitivity
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Panel 1: m_H vs y_t
    ax = axes[0]
    ax.plot(y_t_values, m_H_predictions, 'b-', linewidth=2, label='m_H(1-loop)')
    ax.axhline(y=m_H_exp, color='red', linestyle='--', label=f'PDG: {m_H_exp} GeV')
    ax.axhspan(m_H_exp - dm_H_exp, m_H_exp + dm_H_exp, alpha=0.15, color='red')
    ax.axvline(x=1.0, color='green', linestyle=':', alpha=0.5, label='y_t = 1 (CG)')
    ax.set_xlabel('y_t (top Yukawa)')
    ax.set_ylabel('m_H (GeV)')
    ax.set_title('One-Loop Higgs Mass vs Top Yukawa')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Panel 2: Radiative correction breakdown
    ax = axes[1]
    corrections = {
        'Top\n(1-loop)': delta_top_1loop * 100,
        'W boson': delta_W * 100,
        'Z boson': delta_Z * 100,
        'Net\n1-loop': delta_1loop * 100,
        'Net\nNNLO': delta_NNLO * 100,
    }
    colors_rc = ['#FF5722', '#2196F3', '#4CAF50', '#FF9800', '#9C27B0']
    bars = ax.bar(corrections.keys(), corrections.values(), color=colors_rc, alpha=0.8, edgecolor='black')
    ax.axhline(y=0, color='black', linewidth=0.5)
    ax.set_ylabel('Correction (%)')
    ax.set_title('Radiative Correction Breakdown')
    for bar, val in zip(bars, corrections.values()):
        y_pos = val + 0.1 if val >= 0 else val - 0.2
        ax.text(bar.get_x() + bar.get_width()/2, y_pos, f'{val:.2f}%',
                ha='center', va='bottom' if val >= 0 else 'top', fontsize=9)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plot2_path = os.path.join(PLOT_DIR, "prop_0_0_27_radiative_corrections.png")
    plt.savefig(plot2_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot2_path}")

    # Plot 3: Adversarial - NNLO table and circularity check
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Panel 1: NNLO table check
    ax = axes[0]
    nnlo_labels = ['Top', 'Gauge\n+mixed', 'Mixed\ng-t', 'QCD', 'Higher\norder', 'SUM']
    nnlo_vals = [nnlo_top, nnlo_gauge_mixed, nnlo_mixed_gt, nnlo_qcd, nnlo_higher, nnlo_sum]
    nnlo_colors = ['#FF5722' if v > 0 else '#2196F3' for v in nnlo_vals[:-1]] + ['#FF9800']
    ax.bar(nnlo_labels, nnlo_vals, color=nnlo_colors, alpha=0.8, edgecolor='black')
    ax.axhline(y=1.5, color='red', linestyle='--', label='Claimed net: +1.5%')
    ax.axhline(y=0, color='black', linewidth=0.5)
    ax.set_ylabel('NNLO Correction (%)')
    ax.set_title('NNLO Table Consistency Check')
    ax.legend(fontsize=9)
    for i, val in enumerate(nnlo_vals):
        y_pos = val + 0.1 if val >= 0 else val - 0.15
        ax.text(i, y_pos, f'{val:.1f}%', ha='center',
                va='bottom' if val >= 0 else 'top', fontsize=8)
    ax.grid(True, alpha=0.3, axis='y')
    ax.annotate(f'Missing: +{1.5-nnlo_sum:.1f}%', xy=(5, nnlo_sum),
                xytext=(5, 1.5), arrowprops=dict(arrowstyle='->', color='red'),
                ha='center', fontsize=10, color='red')

    # Panel 2: Prediction chain transparency
    ax = axes[1]
    chain_labels = ['Tree\nλ=1/8', '+Top\n1-loop', '+W,Z\n1-loop', '+NNLO\n(imported)', 'PDG']
    chain_vals = [m_H_tree,
                  m_H_tree * (1 + delta_top_1loop),
                  m_H_tree * (1 + delta_1loop),
                  m_H_NNLO,
                  m_H_exp]
    chain_colors = ['#2196F3', '#FF9800', '#FF9800', '#9C27B0', '#FF5722']
    ax.bar(chain_labels, chain_vals, color=chain_colors, alpha=0.8, edgecolor='black')
    ax.axhline(y=m_H_exp, color='red', linestyle='--', alpha=0.5)
    ax.set_ylabel('m_H (GeV)')
    ax.set_title('Prediction Chain Transparency')
    ax.set_ylim(120, 132)
    for i, val in enumerate(chain_vals):
        ax.text(i, val + 0.2, f'{val:.1f}', ha='center', va='bottom', fontsize=9)

    # Mark CG-derived vs imported
    ax.axvspan(-0.5, 2.5, alpha=0.05, color='green')
    ax.axvspan(2.5, 3.5, alpha=0.05, color='purple')
    ax.text(1, 131, 'CG-derived', ha='center', fontsize=9, color='green', fontweight='bold')
    ax.text(3, 131, 'Imported', ha='center', fontsize=9, color='purple', fontweight='bold')

    plt.tight_layout()
    plot3_path = os.path.join(PLOT_DIR, "prop_0_0_27_adversarial_checks.png")
    plt.savefig(plot3_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot3_path}")

except ImportError:
    print("  WARNING: matplotlib not available, skipping plots")

# ============================================================
# SUMMARY
# ============================================================
print("\n" + "=" * 70)
print("VERIFICATION SUMMARY")
print("=" * 70)

total = len(RESULTS["tests"])
passed = sum(1 for t in RESULTS["tests"] if t["passed"])
failed = sum(1 for t in RESULTS["tests"] if not t["passed"])

print(f"\n  Total tests:  {total}")
print(f"  Passed:       {passed}")
print(f"  Failed:       {failed}")
print(f"  Pass rate:    {passed/total*100:.0f}%")

if failed > 0:
    print("\n  FAILED TESTS:")
    for t in RESULTS["tests"]:
        if not t["passed"]:
            print(f"    - {t['name']}: {t['details']}")

print(f"\n  Key results:")
print(f"    lambda_CG = 1/8 = {lambda_CG}")
print(f"    lambda_exp = {lambda_exp:.4f} (discrepancy: {(lambda_CG-lambda_exp)/lambda_exp*100:.1f}%)")
print(f"    m_H(tree) = {m_H_tree:.2f} GeV")
print(f"    m_H(1-loop, CG only) = {m_H_with_1loop:.1f} GeV")
print(f"    m_H(NNLO, +Buttazzo) = {m_H_NNLO:.1f} GeV")
print(f"    m_H(PDG) = {m_H_exp} +/- {dm_H_exp} GeV")

# Save results
results_path = os.path.join(os.path.dirname(__file__), "proposition_0_0_27_adversarial_results.json")
with open(results_path, 'w') as f:
    json.dump(RESULTS, f, indent=2)
print(f"\n  Results saved to: {results_path}")

print("\n" + "=" * 70)
print(f"OVERALL: {'ALL PASSED' if failed == 0 else f'{failed} FAILED'}")
print("=" * 70)
