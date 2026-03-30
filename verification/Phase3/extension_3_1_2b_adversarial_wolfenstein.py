#!/usr/bin/env python3
"""
Adversarial Physics Verification: Extension 3.1.2b — Complete Wolfenstein Parameters

Multi-agent verification identified critical issues in the proof. This script
performs independent numerical verification of all claimed formulas, checks
internal consistency, quantifies the look-elsewhere effect, and generates
diagnostic plots.

Date: 2026-03-29
Target: docs/proofs/Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md
"""

import numpy as np
import json
import os
import sys

# ============================================================
# Configuration
# ============================================================

PHI = (1 + np.sqrt(5)) / 2  # Golden ratio

# PDG 2024 reference values (CKM global fit)
PDG = {
    'lambda': {'value': 0.22500, 'error': 0.00067, 'source': 'PDG 2024 CKM fit'},
    'A': {'value': 0.826, 'error': 0.015, 'source': 'PDG 2024 global fit'},
    'A_exclusive': {'value': 0.839, 'error': 0.011, 'source': 'PDG 2024 from |V_cb|=0.0422'},
    'rho_bar': {'value': 0.1581, 'error': 0.0092, 'source': 'PDG 2024'},
    'eta_bar': {'value': 0.3548, 'error': 0.0072, 'source': 'PDG 2024'},
    'beta_deg': {'value': 22.2, 'error': 0.7, 'source': 'PDG 2024 direct (sin2beta)'},
    'gamma_deg': {'value': 65.5, 'error': 3.4, 'source': 'PDG 2024 direct (B->DK)'},
    'J': {'value': 3.08e-5, 'error': 0.15e-5, 'source': 'PDG 2024'},
    'Vcb': {'value': 0.0408, 'error': 0.0014, 'source': 'PDG 2024 exclusive'},
    'Vcb_inclusive': {'value': 0.0422, 'error': 0.0008, 'source': 'PDG 2024 inclusive'},
}

PLOTS_DIR = os.path.join(os.path.dirname(__file__), 'plots')
os.makedirs(PLOTS_DIR, exist_ok=True)

results = {'tests': [], 'summary': {}}


def record_test(name, passed, details):
    """Record a test result."""
    results['tests'].append({
        'name': name,
        'passed': passed,
        'details': details
    })
    status = "PASS" if passed else "FAIL"
    print(f"  [{status}] {name}")
    if not passed:
        print(f"         {details}")


# ============================================================
# TEST 1: Numerical Formula Verification
# ============================================================
print("=" * 70)
print("TEST 1: Independent Numerical Verification of All Formulas")
print("=" * 70)

# 1a: lambda = (1/phi^3) * sin(72 deg)
lambda_geom = (1 / PHI**3) * np.sin(np.radians(72))
lambda_claimed = 0.2245
record_test(
    "lambda = (1/phi^3)*sin(72deg)",
    abs(lambda_geom - lambda_claimed) < 0.0001,
    f"Computed: {lambda_geom:.6f}, Claimed: {lambda_claimed}, Diff: {abs(lambda_geom - lambda_claimed):.6f}"
)

# 1b: A = sin(36 deg) / sin(45 deg)
A_geom = np.sin(np.radians(36)) / np.sin(np.radians(45))
A_claimed = 0.8313
record_test(
    "A = sin(36deg)/sin(45deg)",
    abs(A_geom - A_claimed) < 0.0001,
    f"Computed: {A_geom:.6f}, Claimed: {A_claimed}, Diff: {abs(A_geom - A_claimed):.6f}"
)

# 1c: Algebraic identity: A = sqrt((5-sqrt(5))/4)
A_algebraic = np.sqrt((5 - np.sqrt(5)) / 4)
record_test(
    "A = sqrt((5-sqrt(5))/4) identity",
    abs(A_geom - A_algebraic) < 1e-12,
    f"sin(36)/sin(45) = {A_geom:.10f}, sqrt((5-sqrt5)/4) = {A_algebraic:.10f}"
)

# 1d: beta = 36 deg / phi
beta_geom = 36.0 / PHI
beta_claimed = 22.25
record_test(
    "beta = 36deg/phi",
    abs(beta_geom - 22.2492) < 0.001,
    f"Computed: {beta_geom:.4f} deg, Claimed: {beta_claimed} deg (rounded)"
)

# 1e: gamma = arccos(1/3) - 5 deg
gamma_geom = np.degrees(np.arccos(1/3)) - 5.0
gamma_claimed = 65.53
record_test(
    "gamma = arccos(1/3) - 5deg",
    abs(gamma_geom - 65.5288) < 0.001,
    f"Computed: {gamma_geom:.4f} deg, Claimed: {gamma_claimed} deg"
)

# 1f: rho_bar and eta_bar from beta, gamma
beta_rad = np.radians(beta_geom)
gamma_rad = np.radians(gamma_geom)
tan_beta = np.tan(beta_rad)
tan_gamma = np.tan(gamma_rad)
rho_bar_geom = tan_beta / (tan_beta + tan_gamma)
eta_bar_geom = rho_bar_geom * tan_gamma

record_test(
    "rho_bar = tan(beta)/(tan(beta)+tan(gamma))",
    True,
    f"Computed: {rho_bar_geom:.5f}, Claimed: 0.159, PDG: {PDG['rho_bar']['value']}"
)
record_test(
    "eta_bar = rho_bar * tan(gamma)",
    True,
    f"Computed: {eta_bar_geom:.5f}, Claimed: 0.348, PDG: {PDG['eta_bar']['value']}"
)

# 1g: Check claimed vs actual rho_bar/eta_bar
record_test(
    "rho_bar claimed value accuracy",
    abs(rho_bar_geom - 0.159) > 0.001,
    f"Proof claims 0.159, actual formula gives {rho_bar_geom:.5f} — "
    f"difference = {abs(rho_bar_geom - 0.159):.5f} (favorable rounding detected)"
)
record_test(
    "eta_bar claimed value accuracy",
    abs(eta_bar_geom - 0.348) > 0.001,
    f"Proof claims 0.348, actual formula gives {eta_bar_geom:.5f} — "
    f"difference = {abs(eta_bar_geom - 0.348):.5f} (favorable rounding detected)"
)


# ============================================================
# TEST 2: PDG Comparison with Correct Uncertainties
# ============================================================
print()
print("=" * 70)
print("TEST 2: Comparison with PDG 2024 Values (sigma deviations)")
print("=" * 70)

comparisons = {
    'lambda': (lambda_geom, PDG['lambda']),
    'A (vs global fit)': (A_geom, PDG['A']),
    'A (vs exclusive)': (A_geom, PDG['A_exclusive']),
    'beta': (beta_geom, PDG['beta_deg']),
    'gamma': (gamma_geom, PDG['gamma_deg']),
    'rho_bar': (rho_bar_geom, PDG['rho_bar']),
    'eta_bar': (eta_bar_geom, PDG['eta_bar']),
}

print(f"\n  {'Parameter':<20} {'Geometric':>10} {'PDG':>10} {'Error':>8} {'Deviation':>10} {'Within 2σ':>10}")
print(f"  {'-'*20} {'-'*10} {'-'*10} {'-'*8} {'-'*10} {'-'*10}")

max_sigma = 0
for name, (geom_val, pdg) in comparisons.items():
    sigma = abs(geom_val - pdg['value']) / pdg['error']
    pct_err = abs(geom_val - pdg['value']) / pdg['value'] * 100
    within = sigma < 2.0
    max_sigma = max(max_sigma, sigma)
    print(f"  {name:<20} {geom_val:10.5f} {pdg['value']:10.5f} {pdg['error']:8.5f} {sigma:8.2f}σ {'YES' if within else 'NO':>10}")
    record_test(
        f"PDG comparison: {name}",
        within,
        f"{sigma:.2f}σ deviation, {pct_err:.2f}% error"
    )

results['summary']['max_sigma_deviation'] = max_sigma


# ============================================================
# TEST 3: Internal Consistency Checks
# ============================================================
print()
print("=" * 70)
print("TEST 3: Internal Consistency Checks")
print("=" * 70)

# 3a: Does the proof use consistent A value?
A_old = 0.823  # Used in §7, §8, §9
A_new = A_geom  # 0.8313, the "breakthrough"
record_test(
    "A value consistency (old vs new)",
    False,
    f"Proof uses A={A_old} (old formula) in §7-9 but claims A={A_new:.4f} "
    f"(new formula) in §5. Difference: {abs(A_old - A_new):.4f} = {abs(A_old-A_new)/A_new*100:.1f}%"
)

# 3b: Jarlskog invariant consistency
J_with_old_A = A_old**2 * lambda_geom**6 * PDG['eta_bar']['value']
J_with_new_A = A_new**2 * lambda_geom**6 * eta_bar_geom
J_claimed_sec8 = 3.0e-5
J_claimed_sec10 = 3.08e-5

record_test(
    "J consistency (§8 vs §10)",
    False,
    f"§8 claims J=3.0e-5 (using A=0.823), §10 claims J=3.08e-5 (source unclear). "
    f"With new A: J={J_with_new_A:.3e}, With old A: J={J_with_old_A:.3e}"
)

# 3c: PDG A value consistency within proof
record_test(
    "PDG A consistency within proof",
    False,
    f"§1.3 cites A=0.826±0.015, §5.1 cites A=0.839±0.011. "
    f"These differ by {abs(0.826-0.839):.3f}, which is {abs(0.826-0.839)/0.015:.1f}σ of the quoted error"
)

# 3d: PDG beta consistency within proof
record_test(
    "PDG beta consistency within proof",
    False,
    f"§6.2 cites β=22.2°±0.7°, §10.2 summary cites β=22.9° (no error). "
    f"These differ by 0.7°, which is 1.0σ of the quoted error"
)

# 3e: V_cb consistency
Vcb_sec2 = 0.0408
Vcb_sec5 = 0.0422
record_test(
    "|V_cb| consistency within proof",
    False,
    f"§2.3 uses |V_cb|={Vcb_sec2}, §5.1 uses |V_cb|={Vcb_sec5}. "
    f"Difference: {abs(Vcb_sec2-Vcb_sec5):.4f} (inclusive vs exclusive tension)"
)

# 3f: Unitarity triangle closure
alpha_geom = 180.0 - beta_geom - gamma_geom
record_test(
    "Unitarity triangle angle sum",
    abs(alpha_geom + beta_geom + gamma_geom - 180.0) < 1e-10,
    f"α={alpha_geom:.4f}° + β={beta_geom:.4f}° + γ={gamma_geom:.4f}° = "
    f"{alpha_geom + beta_geom + gamma_geom:.4f}°"
)

# 3g: CKM unitarity check with geometric values
# Construct approximate CKM matrix from Wolfenstein params
lam = lambda_geom
A_val = A_geom
rho_val = rho_bar_geom / (1 - lam**2/2)  # Unbar
eta_val = eta_bar_geom / (1 - lam**2/2)

V = np.array([
    [1 - lam**2/2, lam, A_val*lam**3*(rho_val - 1j*eta_val)],
    [-lam, 1 - lam**2/2, A_val*lam**2],
    [A_val*lam**3*(1 - rho_val - 1j*eta_val), -A_val*lam**2, 1.0]
], dtype=complex)

# V V^dagger should be ~ identity
VVdag = V @ V.conj().T
unitarity_dev = np.max(np.abs(VVdag - np.eye(3)))
record_test(
    "CKM unitarity (V V† ≈ I)",
    unitarity_dev < 0.05,
    f"Max deviation from identity: {unitarity_dev:.6f} "
    f"(expected O(λ⁴) ≈ {lam**4:.6f})"
)


# ============================================================
# TEST 4: Look-Elsewhere Effect / Numerology Assessment
# ============================================================
print()
print("=" * 70)
print("TEST 4: Look-Elsewhere Effect Analysis")
print("=" * 70)

# Define "special" angles and constants used in geometric formulas
special_angles = [5, 10, 15, 18, 20, 24, 30, 36, 40, 45, 54, 60, 72, 90, 108, 120]
special_constants = [PHI, 1/PHI, PHI**2, 1/PHI**2, PHI**3, 1/PHI**3,
                     np.sqrt(2), np.sqrt(3), np.sqrt(5), np.pi,
                     1/3, 2/3, 1/np.sqrt(2), 1/np.sqrt(3)]

# Count how many sin(a)/sin(b) formulas match A to within 1%
target_A = PDG['A']['value']
matches_A = []
for a in special_angles:
    for b in special_angles:
        if a != b and np.sin(np.radians(b)) != 0:
            val = np.sin(np.radians(a)) / np.sin(np.radians(b))
            if abs(val - target_A) / target_A < 0.01:  # 1% match
                matches_A.append((a, b, val))

# Count how many angle/constant formulas match beta to within 1%
target_beta = PDG['beta_deg']['value']
matches_beta = []
for a in special_angles:
    for c in special_constants:
        if c != 0:
            val = a / c
            if abs(val - target_beta) / target_beta < 0.02:  # 2% match
                matches_beta.append((a, f"const={c:.4f}", val))

# Count how many arccos(x) +/- angle formulas match gamma to within 1%
target_gamma = PDG['gamma_deg']['value']
matches_gamma = []
test_values = [1/3, 1/2, 1/np.sqrt(2), 1/np.sqrt(3), 2/3, np.sqrt(2)/2, np.sqrt(3)/2]
for x in test_values:
    if abs(x) <= 1:
        base = np.degrees(np.arccos(x))
        for a in special_angles:
            for sign in [1, -1]:
                val = base + sign * a
                if 0 < val < 180 and abs(val - target_gamma) / target_gamma < 0.02:
                    matches_gamma.append((f"arccos({x:.4f}){'+' if sign>0 else '-'}{a}deg", val))

print(f"\n  Formulas matching A={target_A} to within 1% (sin(a)/sin(b)):")
print(f"  Found {len(matches_A)} matches out of {len(special_angles)**2} candidates")
for a, b, val in matches_A:
    print(f"    sin({a}°)/sin({b}°) = {val:.5f} ({abs(val-target_A)/target_A*100:.2f}% off)")

print(f"\n  Formulas matching beta={target_beta}° to within 2% (angle/constant):")
print(f"  Found {len(matches_beta)} matches")
for angle, desc, val in matches_beta[:10]:
    print(f"    {angle}°/{desc} -> {val:.4f}° ({abs(val-target_beta)/target_beta*100:.2f}% off)")

print(f"\n  Formulas matching gamma={target_gamma}° to within 2% (arccos(x)±angle):")
print(f"  Found {len(matches_gamma)} matches")
for desc, val in matches_gamma[:10]:
    print(f"    {desc} = {val:.4f}° ({abs(val-target_gamma)/target_gamma*100:.2f}% off)")

total_candidates = len(special_angles)**2 + len(special_angles)*len(special_constants) + len(test_values)*len(special_angles)*2
n_A = len(matches_A)
n_beta = len(matches_beta)
n_gamma = len(matches_gamma)

record_test(
    "Look-elsewhere: sin(a)/sin(b) matches for A",
    n_A <= 1,
    f"Found {n_A} formulas matching A to 1% out of {len(special_angles)**2} candidates"
)
record_test(
    "Look-elsewhere: angle/const matches for beta",
    n_beta <= 1,
    f"Found {n_beta} formulas matching beta to 2%"
)
record_test(
    "Look-elsewhere: arccos(x)±angle matches for gamma",
    n_gamma <= 1,
    f"Found {n_gamma} formulas matching gamma to 2%"
)

results['summary']['look_elsewhere'] = {
    'A_matches': n_A,
    'beta_matches': n_beta,
    'gamma_matches': n_gamma,
    'total_search_space': total_candidates
}


# ============================================================
# TEST 5: Random Target Test (Can we match arbitrary values?)
# ============================================================
print()
print("=" * 70)
print("TEST 5: Random Target Test — Can geometric formulas match any value?")
print("=" * 70)

np.random.seed(42)
n_random = 100
random_targets = np.random.uniform(0.1, 1.0, n_random)
matches_per_target = []

for target in random_targets:
    count = 0
    for a in special_angles:
        for b in special_angles:
            if a != b and np.sin(np.radians(b)) != 0:
                val = np.sin(np.radians(a)) / np.sin(np.radians(b))
                if abs(val - target) / target < 0.01:
                    count += 1
    matches_per_target.append(count)

avg_matches = np.mean(matches_per_target)
frac_with_match = np.mean(np.array(matches_per_target) > 0)

print(f"\n  For {n_random} random targets in [0.1, 1.0]:")
print(f"  Average sin(a)/sin(b) matches per target (1% tolerance): {avg_matches:.2f}")
print(f"  Fraction with at least one match: {frac_with_match:.1%}")

record_test(
    "Random target test: are geometric matches special?",
    frac_with_match < 0.5,
    f"{frac_with_match:.1%} of random targets have sin(a)/sin(b) matches at 1% — "
    f"{'formula is NOT special' if frac_with_match > 0.5 else 'formula has some selectivity'}"
)


# ============================================================
# TEST 6: Geometric Claim Verification
# ============================================================
print()
print("=" * 70)
print("TEST 6: Geometric Claim Verification")
print("=" * 70)

# 6a: arccos(1/3) — is it the dihedral angle or edge-face angle?
dihedral_tetra = np.degrees(np.arccos(1/3))
edge_face_angle = np.degrees(np.arctan(np.sqrt(2)))  # Actual edge-face angle

record_test(
    "arccos(1/3) = tetrahedron dihedral angle",
    abs(dihedral_tetra - 70.5288) < 0.001,
    f"arccos(1/3) = {dihedral_tetra:.4f}° — this is the DIHEDRAL angle, "
    f"NOT the 'edge-face angle' ({edge_face_angle:.4f}°) as claimed in §6.4"
)

# 6b: 36°/φ golden section identity
golden_section_check = beta_geom * PHI
record_test(
    "Golden section: 36° = beta * phi",
    abs(golden_section_check - 36.0) < 1e-10,
    f"beta * phi = {golden_section_check:.10f}° (should be exactly 36°)"
)

# 6c: Verify 36-72-72 is golden triangle, NOT golden gnomon
# Golden triangle: 36-72-72 (isoceles, acute)
# Golden gnomon: 36-36-108 (isoceles, obtuse)
print(f"\n  Terminology check:")
print(f"  36°-72°-72° triangle = golden TRIANGLE (not 'golden gnomon' as stated in §6.3)")
print(f"  36°-36°-108° triangle = golden GNOMON")
record_test(
    "Golden gnomon terminology",
    False,
    "Proof calls 36°-72°-72° the 'golden gnomon' — it is actually the 'golden triangle'"
)


# ============================================================
# TEST 7: Corrected Summary Table
# ============================================================
print()
print("=" * 70)
print("TEST 7: Corrected Summary Table (all values recomputed)")
print("=" * 70)

# Recompute everything self-consistently with A = sin(36)/sin(45)
J_corrected = A_geom**2 * lambda_geom**6 * eta_bar_geom

print(f"\n  {'Parameter':<12} {'Geometric':>12} {'Proof claimed':>14} {'PDG 2024':>12} {'True % err':>12} {'Proof % err':>12}")
print(f"  {'-'*12} {'-'*12} {'-'*14} {'-'*12} {'-'*12} {'-'*12}")

corrections = [
    ('lambda', lambda_geom, 0.2245, PDG['lambda']['value']),
    ('A', A_geom, 0.8313, PDG['A']['value']),
    ('beta (deg)', beta_geom, 22.25, PDG['beta_deg']['value']),
    ('gamma (deg)', gamma_geom, 65.53, PDG['gamma_deg']['value']),
    ('rho_bar', rho_bar_geom, 0.159, PDG['rho_bar']['value']),
    ('eta_bar', eta_bar_geom, 0.348, PDG['eta_bar']['value']),
    ('J (x1e5)', J_corrected*1e5, 3.08, PDG['J']['value']*1e5),
]

for name, geom, claimed, pdg in corrections:
    true_pct = abs(geom - pdg) / pdg * 100
    proof_pct = abs(claimed - pdg) / pdg * 100
    print(f"  {name:<12} {geom:12.5f} {claimed:14.4f} {pdg:12.5f} {true_pct:11.2f}% {proof_pct:11.2f}%")


# ============================================================
# PLOT GENERATION
# ============================================================
print()
print("=" * 70)
print("Generating diagnostic plots...")
print("=" * 70)

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyBboxPatch

    # ---- PLOT 1: Parameter comparison with PDG ----
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Extension 3.1.2b: Wolfenstein Parameters vs PDG 2024\n'
                 '(Adversarial Verification)', fontsize=14, fontweight='bold')

    params_plot = [
        ('λ', lambda_geom, PDG['lambda']['value'], PDG['lambda']['error'], '(1/φ³)sin(72°)'),
        ('A', A_geom, PDG['A']['value'], PDG['A']['error'], 'sin(36°)/sin(45°)'),
        ('β (deg)', beta_geom, PDG['beta_deg']['value'], PDG['beta_deg']['error'], '36°/φ'),
        ('γ (deg)', gamma_geom, PDG['gamma_deg']['value'], PDG['gamma_deg']['error'], 'arccos(1/3)−5°'),
        ('ρ̄', rho_bar_geom, PDG['rho_bar']['value'], PDG['rho_bar']['error'], 'tan(β)/(tan(β)+tan(γ))'),
        ('η̄', eta_bar_geom, PDG['eta_bar']['value'], PDG['eta_bar']['error'], 'ρ̄·tan(γ)'),
    ]

    for ax, (name, geom, pdg_val, pdg_err, formula) in zip(axes.flat, params_plot):
        sigma = abs(geom - pdg_val) / pdg_err
        color = 'green' if sigma < 1 else ('orange' if sigma < 2 else 'red')

        ax.errorbar(pdg_val, 0.5, xerr=pdg_err, fmt='ko', capsize=5, markersize=8, label='PDG 2024')
        ax.errorbar(pdg_val, 0.5, xerr=2*pdg_err, fmt='none', capsize=3, color='gray', alpha=0.5)
        ax.axvline(geom, color=color, linewidth=2, linestyle='--', label=f'Geometric: {geom:.5f}')
        ax.set_title(f'{name}\n{formula}', fontsize=11)
        ax.set_xlabel(f'Value ({sigma:.2f}σ deviation)')
        ax.set_yticks([])
        ax.legend(fontsize=8, loc='upper right')

    plt.tight_layout()
    plot1_path = os.path.join(PLOTS_DIR, 'extension_3_1_2b_wolfenstein_pdg_comparison.png')
    plt.savefig(plot1_path, dpi=150)
    plt.close()
    print(f"  Saved: {plot1_path}")

    # ---- PLOT 2: Unitarity Triangle ----
    fig, ax = plt.subplots(1, 1, figsize=(10, 7))
    ax.set_title('Unitarity Triangle: Geometric vs PDG 2024', fontsize=14, fontweight='bold')

    # PDG triangle
    pdg_rho = PDG['rho_bar']['value']
    pdg_eta = PDG['eta_bar']['value']
    pdg_triangle = plt.Polygon(
        [(0, 0), (1, 0), (pdg_rho, pdg_eta)],
        fill=False, edgecolor='blue', linewidth=2, linestyle='-', label='PDG 2024'
    )
    ax.add_patch(pdg_triangle)

    # Geometric triangle
    geom_triangle = plt.Polygon(
        [(0, 0), (1, 0), (rho_bar_geom, eta_bar_geom)],
        fill=False, edgecolor='red', linewidth=2, linestyle='--', label='Geometric'
    )
    ax.add_patch(geom_triangle)

    # PDG error ellipse (approximate)
    theta_ell = np.linspace(0, 2*np.pi, 100)
    ell_x = pdg_rho + PDG['rho_bar']['error'] * np.cos(theta_ell)
    ell_y = pdg_eta + PDG['eta_bar']['error'] * np.sin(theta_ell)
    ax.plot(ell_x, ell_y, 'b-', alpha=0.3, linewidth=1)
    ax.fill(ell_x, ell_y, alpha=0.1, color='blue')

    # Mark vertices
    ax.plot(0, 0, 'ko', markersize=8)
    ax.plot(1, 0, 'ko', markersize=8)
    ax.plot(pdg_rho, pdg_eta, 'bo', markersize=8)
    ax.plot(rho_bar_geom, eta_bar_geom, 'r^', markersize=10)

    # Angle labels
    ax.annotate(f'β={beta_geom:.2f}°', xy=(0, 0), xytext=(0.05, 0.05), fontsize=10)
    ax.annotate(f'γ={gamma_geom:.2f}°', xy=(rho_bar_geom, eta_bar_geom),
                xytext=(rho_bar_geom-0.05, eta_bar_geom+0.02), fontsize=10)
    ax.annotate(f'α={alpha_geom:.2f}°', xy=(1, 0), xytext=(0.85, 0.03), fontsize=10)

    ax.set_xlim(-0.1, 1.15)
    ax.set_ylim(-0.05, 0.5)
    ax.set_xlabel('ρ̄', fontsize=12)
    ax.set_ylabel('η̄', fontsize=12)
    ax.legend(fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    plot2_path = os.path.join(PLOTS_DIR, 'extension_3_1_2b_unitarity_triangle.png')
    plt.savefig(plot2_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot2_path}")

    # ---- PLOT 3: Look-Elsewhere Effect ----
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    fig.suptitle('Look-Elsewhere Effect Analysis', fontsize=14, fontweight='bold')

    # Histogram of matches per random target
    ax1.hist(matches_per_target, bins=range(max(matches_per_target)+2),
             color='steelblue', edgecolor='black', alpha=0.7, align='left')
    ax1.axvline(n_A, color='red', linewidth=2, linestyle='--',
                label=f'A target matches: {n_A}')
    ax1.set_xlabel('Number of sin(a)/sin(b) matches (1% tolerance)')
    ax1.set_ylabel('Count (out of 100 random targets)')
    ax1.set_title('Distribution of matches for random targets')
    ax1.legend()

    # Sigma deviations for all parameters (skip duplicate A)
    param_names = ['λ', 'A (fit)', 'A (excl.)', 'β', 'γ', 'ρ̄', 'η̄']
    sigmas = []
    for name, (geom_val, pdg) in comparisons.items():
        sigmas.append(abs(geom_val - pdg['value']) / pdg['error'])

    colors = ['green' if s < 1 else ('orange' if s < 2 else 'red') for s in sigmas]
    bars = ax2.barh(param_names, sigmas, color=colors, edgecolor='black', alpha=0.7)
    ax2.axvline(1.0, color='gray', linestyle='--', alpha=0.5, label='1σ')
    ax2.axvline(2.0, color='gray', linestyle=':', alpha=0.5, label='2σ')
    ax2.set_xlabel('Deviation from PDG (σ)')
    ax2.set_title('All parameters: deviation from PDG 2024')
    ax2.legend()

    plt.tight_layout()
    plot3_path = os.path.join(PLOTS_DIR, 'extension_3_1_2b_look_elsewhere.png')
    plt.savefig(plot3_path, dpi=150)
    plt.close()
    print(f"  Saved: {plot3_path}")

    # ---- PLOT 4: Internal Consistency Dashboard ----
    fig, ax = plt.subplots(figsize=(12, 6))
    ax.set_title('Internal Consistency: Values of A Used in the Proof', fontsize=14, fontweight='bold')

    A_values = [
        ('A (new formula)\nsin(36°)/sin(45°)', A_geom, 'green'),
        ('A (old formula)\n1/(2λ^{1/3})', 0.823, 'orange'),
        ('PDG global fit', 0.826, 'blue'),
        ('PDG from |V_cb|=0.0422', 0.839, 'blue'),
        ('PDG from |V_cb|=0.0408', 0.0408/lambda_geom**2, 'purple'),
    ]

    y_pos = range(len(A_values))
    for i, (label, val, col) in enumerate(A_values):
        ax.barh(i, val, color=col, alpha=0.6, edgecolor='black')
        ax.text(val + 0.005, i, f'{val:.4f}', va='center', fontsize=10)

    ax.set_yticks(y_pos)
    ax.set_yticklabels([label for label, _, _ in A_values])
    ax.set_xlabel('Value of A')
    ax.set_xlim(0.75, 0.9)
    ax.axvline(PDG['A']['value'], color='blue', linestyle='--', alpha=0.3)
    ax.axvspan(PDG['A']['value'] - PDG['A']['error'],
               PDG['A']['value'] + PDG['A']['error'],
               alpha=0.1, color='blue', label=f'PDG ±1σ')
    ax.legend()
    ax.grid(axis='x', alpha=0.3)

    plot4_path = os.path.join(PLOTS_DIR, 'extension_3_1_2b_A_consistency.png')
    plt.savefig(plot4_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot4_path}")

except ImportError:
    print("  matplotlib not available — skipping plots")


# ============================================================
# FINAL SUMMARY
# ============================================================
print()
print("=" * 70)
print("FINAL SUMMARY")
print("=" * 70)

n_pass = sum(1 for t in results['tests'] if t['passed'])
n_fail = sum(1 for t in results['tests'] if not t['passed'])
n_total = len(results['tests'])

print(f"\n  Tests passed: {n_pass}/{n_total}")
print(f"  Tests failed: {n_fail}/{n_total}")
print(f"  Max sigma deviation from PDG: {max_sigma:.2f}σ")

print(f"\n  CRITICAL ISSUES:")
print(f"  1. A value used inconsistently (0.823 vs 0.8313) throughout document")
print(f"  2. PDG reference values cited inconsistently (A: 0.826 vs 0.839)")
print(f"  3. ρ̄ and η̄ favorably rounded (0.159/0.348 vs actual 0.157/0.345)")
print(f"  4. arccos(1/3) mislabeled as 'edge-face angle' (it's the dihedral angle)")
print(f"  5. 'Golden gnomon' terminology wrong (should be 'golden triangle')")
print(f"  6. Look-elsewhere effect: {n_A} sin/sin formulas match A at 1%")

print(f"\n  CORRECTED VALUES (from formulas):")
print(f"  λ  = {lambda_geom:.6f}  (vs claimed 0.2245)")
print(f"  A  = {A_geom:.6f}   (vs claimed 0.8313)")
print(f"  β  = {beta_geom:.4f}°  (vs claimed 22.25°)")
print(f"  γ  = {gamma_geom:.4f}°  (vs claimed 65.53°)")
print(f"  ρ̄  = {rho_bar_geom:.5f}  (vs claimed 0.159)")
print(f"  η̄  = {eta_bar_geom:.5f}  (vs claimed 0.348)")
print(f"  J  = {J_corrected:.3e}  (vs claimed 3.08e-5)")

results['summary']['tests_passed'] = n_pass
results['summary']['tests_failed'] = n_fail
results['summary']['corrected_values'] = {
    'lambda': lambda_geom,
    'A': float(A_geom),
    'beta_deg': beta_geom,
    'gamma_deg': gamma_geom,
    'rho_bar': rho_bar_geom,
    'eta_bar': eta_bar_geom,
    'J': J_corrected,
}

# Save results
results_path = os.path.join(os.path.dirname(__file__),
                            'extension_3_1_2b_adversarial_wolfenstein_results.json')
with open(results_path, 'w') as f:
    json.dump(results, f, indent=2, default=str)
print(f"\n  Results saved to: {results_path}")

print(f"\n  VERDICT: {'PARTIAL — numerical formulas correct, but internal inconsistencies must be resolved'}")
