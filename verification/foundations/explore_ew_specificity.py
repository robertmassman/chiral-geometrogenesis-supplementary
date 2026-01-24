#!/usr/bin/env python3
"""
Explore why the electroweak hierarchy formula is EW-specific.

This script quantitatively demonstrates the five reasons the formula
works for electroweak but fails for QCD:
1. Weak vs strong coupling
2. Gentle vs violent RG flow (small vs large Δa)
3. Spontaneous vs dynamical symmetry breaking
4. Dilaton interpretation (Higgs proxy)
5. CFT-like vs confined IR endpoint
"""

import numpy as np

# =============================================================================
# Physical constants
# =============================================================================

v_H_observed = 246.22  # GeV (PDG 2024)
sqrt_sigma = 0.440  # GeV (FLAG 2024)
Lambda_QCD = 0.220  # GeV (approximate Λ_QCD)
M_W = 80.4  # GeV
M_Z = 91.2  # GeV

# Coupling constants
alpha_s_Mz = 0.118  # Strong coupling at M_Z
alpha_2_Mw = 0.034  # Weak coupling at M_W
alpha_1_Mw = 0.010  # U(1) coupling at M_W

print("=" * 70)
print("EW-SPECIFICITY ANALYSIS")
print("Why the formula works for EW but fails for QCD")
print("=" * 70)

# =============================================================================
# Section 1: The Formula Applied to Both Sectors
# =============================================================================

print("\n" + "=" * 70)
print("1. APPLYING THE FORMULA TO EW AND QCD")
print("=" * 70)

# Central charge coefficients
a_scalar = 1/360
a_fermion = 11/720
a_vector = 62/360

# Electroweak parameters
dim_adj_EW = 4  # SU(2)×U(1)
Delta_a_EW = 1/120  # Effective value from Prop 0.0.21

# QCD parameters
dim_adj_QCD = 8  # SU(3)
# QCD Δa: 8 gluons + quarks
# Naive: Δa_QCD = 8 × (62/360) + contributions from quarks
Delta_a_QCD_naive = 8 * a_vector + 3 * 6 * a_fermion  # 8 gluons + 3 light quarks (6 Weyl each)
Delta_a_QCD_estimate = 1.6  # Literature estimate for full flow

print("\nElectroweak sector:")
print(f"  dim(adj_EW) = {dim_adj_EW}")
print(f"  Δa_EW = {Delta_a_EW:.6f} = 1/120")
print(f"  α_W(M_W) = {alpha_2_Mw}")

print("\nQCD sector:")
print(f"  dim(adj_QCD) = {dim_adj_QCD}")
print(f"  Δa_QCD (naive) = {Delta_a_QCD_naive:.4f}")
print(f"  Δa_QCD (estimate) = {Delta_a_QCD_estimate}")
print(f"  α_s(M_Z) = {alpha_s_Mz}")

# Apply the formula
def hierarchy_formula(dim_adj, Delta_a, reference_scale):
    """Compute predicted VEV using the unified formula."""
    exponent = 1/dim_adj + 1/(2 * np.pi**2 * Delta_a)
    ratio = np.exp(exponent)
    vev = reference_scale * ratio
    return exponent, ratio, vev

# Electroweak
exp_EW, ratio_EW, vev_EW = hierarchy_formula(dim_adj_EW, Delta_a_EW, sqrt_sigma)
print(f"\n--- Formula predictions ---")
print(f"\nElectroweak (from √σ = {sqrt_sigma} GeV):")
print(f"  Exponent = 1/{dim_adj_EW} + 1/(2π²×{Delta_a_EW:.4f}) = {exp_EW:.4f}")
print(f"  Predicted ratio = exp({exp_EW:.4f}) = {ratio_EW:.2f}")
print(f"  Predicted v_H = {vev_EW:.2f} GeV")
print(f"  Observed v_H = {v_H_observed} GeV")
print(f"  Agreement: {100*(1 - abs(vev_EW - v_H_observed)/v_H_observed):.2f}%")

# QCD - try to predict Λ_QCD from √σ
exp_QCD, ratio_QCD, Lambda_QCD_pred = hierarchy_formula(dim_adj_QCD, Delta_a_QCD_estimate, sqrt_sigma)
print(f"\nQCD (from √σ = {sqrt_sigma} GeV, using Δa = {Delta_a_QCD_estimate}):")
print(f"  Exponent = 1/{dim_adj_QCD} + 1/(2π²×{Delta_a_QCD_estimate}) = {exp_QCD:.4f}")
print(f"  Predicted ratio = exp({exp_QCD:.4f}) = {ratio_QCD:.2f}")
print(f"  Predicted Λ_QCD = {Lambda_QCD_pred:.4f} GeV")
print(f"  Observed Λ_QCD ≈ {Lambda_QCD} GeV")
print(f"  Observed ratio Λ_QCD/√σ = {Lambda_QCD/sqrt_sigma:.2f}")
print(f"  Formula gives wrong answer by factor of {ratio_QCD/(Lambda_QCD/sqrt_sigma):.1f}")

# =============================================================================
# Section 2: The Δa Sensitivity
# =============================================================================

print("\n" + "=" * 70)
print("2. THE Δa SENSITIVITY")
print("=" * 70)

# The key term is 1/(2π²Δa)
def central_charge_term(Delta_a):
    return 1/(2 * np.pi**2 * Delta_a)

print("\nThe exponential term 1/(2π²Δa):")
print(f"\n{'Δa':<15} {'1/(2π²Δa)':<15} {'exp(term)':<15} {'Physical?':<20}")
print("-" * 65)

delta_a_values = [
    (1/120, "EW (empirical)"),
    (0.01, "EW-like"),
    (0.1, "Moderate"),
    (0.5, "Large"),
    (1.0, "Very large"),
    (1.6, "QCD estimate"),
    (2.0, "Extreme"),
]

for da, label in delta_a_values:
    term = central_charge_term(da)
    exp_term = np.exp(term)
    if exp_term > 1e6:
        exp_str = f"{exp_term:.2e}"
    else:
        exp_str = f"{exp_term:.2f}"
    physical = "✓ Creates hierarchy" if da < 0.1 else "✗ No hierarchy"
    print(f"{da:<15.4f} {term:<15.4f} {exp_str:<15} {physical:<20}")

print("\nConclusion: The formula only creates large hierarchies for SMALL Δa.")
print(f"EW has Δa = 1/120 ≈ 0.008 → exp({central_charge_term(1/120):.2f}) ≈ 437")
print(f"QCD has Δa ≈ 1.6 → exp({central_charge_term(1.6):.4f}) ≈ 1.03")

# =============================================================================
# Section 3: Coupling Strength Comparison
# =============================================================================

print("\n" + "=" * 70)
print("3. COUPLING STRENGTH: WEAK VS STRONG")
print("=" * 70)

print("\nElectroweak couplings (at M_W ≈ 80 GeV):")
print(f"  α_2 = g₂²/(4π) ≈ {alpha_2_Mw}")
print(f"  α_1 = g₁²/(4π) ≈ {alpha_1_Mw}")
print(f"  Combined: weak coupling → perturbation theory VALID")

print("\nQCD coupling:")
print(f"  α_s(M_Z = 91 GeV) ≈ {alpha_s_Mz}")
print(f"  α_s(2 GeV) ≈ {0.30}")
print(f"  α_s(Λ_QCD ≈ 220 MeV) → ∞")
print(f"  At confinement scale: perturbation theory FAILS")

# Estimate running of α_s
def alpha_s_running(mu_GeV, Lambda_QCD_MeV=220, n_f=3):
    """One-loop running of α_s."""
    Lambda_GeV = Lambda_QCD_MeV / 1000
    if mu_GeV < Lambda_GeV:
        return float('inf')
    b0 = (33 - 2*n_f) / (12 * np.pi)
    return 1 / (b0 * np.log(mu_GeV / Lambda_GeV))

print("\nα_s running (one-loop approximation):")
scales = [91.2, 10, 2, 1, 0.5, 0.3]
for mu in scales:
    alpha = alpha_s_running(mu)
    status = "OK" if alpha < 1 else "FAILS" if alpha < 10 else "→∞"
    print(f"  α_s({mu} GeV) = {alpha:.3f} [{status}]")

print("\nConclusion: EW is perturbative everywhere; QCD becomes non-perturbative at Λ_QCD.")

# =============================================================================
# Section 4: Symmetry Breaking Mechanism
# =============================================================================

print("\n" + "=" * 70)
print("4. SYMMETRY BREAKING MECHANISM")
print("=" * 70)

print("""
ELECTROWEAK: Spontaneous Symmetry Breaking (Higgs mechanism)
─────────────────────────────────────────────────────────────
- Higgs potential: V(H) = μ²|H|² + λ|H|⁴
- Classical minimum at |H| = v/√2 where v = √(-μ²/λ)
- The VEV v is a FREE PARAMETER (set by μ², λ)
- Goldstone bosons are "eaten" by W±, Z
- Higgs field serves as DILATON PROXY

QCD: Dynamical Symmetry Breaking (Confinement)
─────────────────────────────────────────────────────────────
- NO classical potential with a VEV
- Confinement is NON-PERTURBATIVE (instantons, monopoles, etc.)
- Λ_QCD emerges from DIMENSIONAL TRANSMUTATION
- The scale is set by: Λ_QCD = μ × exp(-1/(2b₀α_s(μ)))
- There is NO HIGGS-LIKE FIELD in QCD

Key difference: EW has a scalar VEV → dilaton interpretation possible
               QCD has no scalar VEV → dilaton interpretation fails
""")

# =============================================================================
# Section 5: IR Endpoint Comparison
# =============================================================================

print("\n" + "=" * 70)
print("5. IR ENDPOINT: CFT-LIKE VS CONFINED")
print("=" * 70)

print("""
ELECTROWEAK IR (below M_W, M_Z, M_H):
─────────────────────────────────────
- Massive W±, Z, H DECOUPLE (their effects suppressed by 1/M²)
- Only PHOTON survives as massless gauge boson
- The IR is effectively QED: a FREE FIELD THEORY
- Central charge a_IR is well-defined: a_γ = 62/360

QCD IR (below Λ_QCD):
─────────────────────
- Quarks and gluons are CONFINED (cannot be isolated)
- Physical states are HADRONS (pions, protons, ...)
- Chiral symmetry is spontaneously broken (pions are Goldstones)
- The IR is STRONGLY INTERACTING, not a CFT
- Central charge a_IR is ILL-DEFINED in the confined phase
""")

# Compute central charges
a_photon = a_vector
a_EW_UV = 4 * a_vector + 4 * a_scalar  # 4 EW gauge bosons + Higgs doublet (4 real)
a_EW_IR = a_vector  # Just photon

print("Electroweak central charges:")
print(f"  a_UV (massless EW) = 4 × {a_vector:.5f} + 4 × {a_scalar:.5f} = {a_EW_UV:.5f}")
print(f"  a_IR (photon only) = {a_EW_IR:.5f}")
print(f"  Δa_EW (naive) = {a_EW_UV - a_EW_IR:.5f}")
print(f"  Note: Prop 0.0.21 uses Δa_EW = 1/120 = 0.00833 (effective value)")

# =============================================================================
# Section 6: The 2π² = 16π²/(2×dim) Structure
# =============================================================================

print("\n" + "=" * 70)
print("6. THE EW-SPECIFIC NORMALIZATION")
print("=" * 70)

sixteen_pi_sq = 16 * np.pi**2
two_pi_sq = 2 * np.pi**2

print(f"\nStandard trace anomaly normalization: 16π² = {sixteen_pi_sq:.2f}")
print(f"Formula uses: 2π² = {two_pi_sq:.2f}")
print(f"Ratio: 16π²/2π² = 8")

print("\nThe factor of 8 = 2 × dim(adj_EW) = 2 × 4:")
print(f"  → 2π² = 16π² / (2 × dim_EW) for dim_EW = 4")

print("\nWhat about other gauge groups?")
gauge_groups = {
    "SU(2)×U(1) (EW)": 4,
    "SU(3) (QCD)": 8,
    "SU(5) (GUT)": 24,
    "SO(10)": 45,
}

print(f"\n{'Gauge Group':<25} {'dim(adj)':<10} {'16π²/(2×dim)':<15} {'vs 2π²':<10}")
print("-" * 60)
for name, dim in gauge_groups.items():
    norm = sixteen_pi_sq / (2 * dim)
    ratio = norm / two_pi_sq
    match = "✓" if abs(ratio - 1) < 0.01 else ""
    print(f"{name:<25} {dim:<10} {norm:<15.4f} {ratio:.4f}× {match}")

print("\nConclusion: The 2π² normalization is EW-SPECIFIC (dim = 4 only).")

# =============================================================================
# Section 7: Summary Table
# =============================================================================

print("\n" + "=" * 70)
print("7. SUMMARY: EW vs QCD")
print("=" * 70)

print("""
Feature                    Electroweak             QCD
═══════════════════════════════════════════════════════════════════════
Coupling in IR             Weak (α~0.03)           Strong (α→∞)
Δa magnitude               Small (1/120)           Large (~1.6)
exp(1/(2π²Δa))             437 ✓                   1.03 ✗
Breaking mechanism         Spontaneous (Higgs)     Dynamical (confine)
Dilaton proxy              Higgs field ✓           None ✗
IR endpoint                CFT (photon) ✓          Confined ✗
Normalization (2×dim)      8 (works) ✓             16 (doesn't match) ✗
Formula prediction         v_H = 247 GeV ✓         Λ = 0.51 GeV ✗
Observed                   v_H = 246 GeV           Λ_QCD ≈ 0.22 GeV
Agreement                  0.2% ✓                  ~100% error ✗
═══════════════════════════════════════════════════════════════════════
""")

print("CONCLUSION:")
print("The formula is EW-specific because the electroweak sector uniquely satisfies")
print("ALL requirements: weak coupling, small Δa, Higgs mechanism, CFT-like IR,")
print("and dim(adj) = 4 for the 2π² normalization.")

print("\n" + "=" * 70)
