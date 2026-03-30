#!/usr/bin/env python3
"""
INVESTIGATION: Path A Holographic Saturation Rescaling Analysis
================================================================

Tests whether the holographic saturation condition (I_stella = I_gravity)
from Prop 0.0.30 breaks the projective ambiguity under uniform rescaling
of all dimensionful quantities.

Key question: Under a → λa, l_P → λl_P, A → λ²A, does the saturation
condition I_stella = I_gravity still hold? If yes, it cannot determine
the absolute scale.

Related Documents:
- Prop 0.0.30: Holographic Saturation from Thermodynamic Equilibrium
- Prop 0.0.17v: Holographic Scale from Self-Consistency
- Thm 5.2.5: Bekenstein-Hawking Coefficient Derivation
- Research: docs/proofs/supporting/Research-Absolute-Scale-Determination-Paths.md

Investigation Date: 2026-03-29
"""

import numpy as np
import json
from datetime import datetime

# ==============================================================================
# PHYSICAL CONSTANTS (CODATA 2018 / PDG 2024)
# ==============================================================================

HBAR = 1.054571817e-34      # J·s
C = 299792458               # m/s
G_NEWTON = 6.67430e-11      # m³/(kg·s²)
K_B = 1.380649e-23          # J/K

L_PLANCK = np.sqrt(HBAR * G_NEWTON / C**3)  # 1.616255e-35 m
M_PLANCK_KG = np.sqrt(HBAR * C / G_NEWTON)  # 2.176434e-8 kg
T_PLANCK = np.sqrt(HBAR * C**5 / (G_NEWTON * K_B**2))  # 1.416784e32 K

# Framework parameters
N_C = 3                     # Number of colors
SQRT_SIGMA_GEV = 0.440      # String tension (GeV)
HBAR_C_GEV_FM = 0.197327    # ℏc in GeV·fm
R_STELLA_FM = HBAR_C_GEV_FM / SQRT_SIGMA_GEV  # 0.44847 fm

print("=" * 70)
print("INVESTIGATION: PATH A HOLOGRAPHIC SATURATION RESCALING")
print("=" * 70)
print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
print()

results = {
    "date": datetime.now().isoformat(),
    "investigation": "Path A Holographic Saturation Rescaling",
    "tests": [],
    "overall_status": None
}

# ==============================================================================
# TEST 1: I_stella homogeneity under rescaling
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 1: I_stella HOMOGENEITY UNDER RESCALING")
print("=" * 70)
print()
print("I_stella = (2 ln 3 / √3 a²) × A")
print("Under a → λa, A → λ²A:")
print("  I_stella → (2 ln 3 / √3 (λa)²) × λ²A = (2 ln 3 / √3 a²) × A")
print("  → degree 0 (invariant)")
print()

def I_stella(A, a):
    """Information capacity of stella boundary.

    N_sites = A / (√3/4 × a²) sites, each carrying ln(3) nats.
    I_stella = N_sites × ln(3) = (4 ln 3 / √3 a²) × A

    From Prop 0.0.17v: using the specific lattice tiling,
    I_stella = (2 ln 3 / √3 a²) × A
    """
    return (2 * np.log(3) / (np.sqrt(3) * a**2)) * A

# Reference values
a_ref = 1.0  # arbitrary reference lattice spacing
A_ref = 100.0  # arbitrary reference area
I_ref = I_stella(A_ref, a_ref)

lambdas = [0.01, 0.1, 0.5, 1.0, 2.0, 10.0, 100.0]
test1_results = []

print(f"{'λ':>10} {'I_stella(λ²A, λa)':>25} {'I_ref':>25} {'Ratio':>15}")
print("-" * 75)

for lam in lambdas:
    A_scaled = lam**2 * A_ref
    a_scaled = lam * a_ref
    I_scaled = I_stella(A_scaled, a_scaled)
    ratio = I_scaled / I_ref
    test1_results.append({
        "lambda": lam,
        "I_scaled": I_scaled,
        "I_ref": I_ref,
        "ratio": ratio,
        "invariant": abs(ratio - 1.0) < 1e-14
    })
    print(f"{lam:>10.3f} {I_scaled:>25.10f} {I_ref:>25.10f} {ratio:>15.2e}")

test1_pass = all(r["invariant"] for r in test1_results)
print(f"\n✅ I_stella is homogeneous degree 0: {test1_pass}")

results["tests"].append({
    "name": "I_stella homogeneity",
    "claim": "I_stella is homogeneous degree 0 under (a,A) → (λa, λ²A)",
    "passed": test1_pass,
    "details": test1_results
})

# ==============================================================================
# TEST 2: I_gravity homogeneity under rescaling
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 2: I_gravity HOMOGENEITY UNDER RESCALING")
print("=" * 70)
print()
print("I_gravity = A / (4 l_P²)")
print("Under A → λ²A, l_P → λl_P:")
print("  I_gravity → λ²A / (4 λ²l_P²) = A / (4 l_P²)")
print("  → degree 0 (invariant)")
print()

def I_gravity(A, l_P):
    """Bekenstein-Hawking entropy bound."""
    return A / (4 * l_P**2)

l_P_ref = 1.0  # arbitrary reference Planck length
I_grav_ref = I_gravity(A_ref, l_P_ref)

test2_results = []
print(f"{'λ':>10} {'I_gravity(λ²A, λl_P)':>25} {'I_ref':>25} {'Ratio':>15}")
print("-" * 75)

for lam in lambdas:
    A_scaled = lam**2 * A_ref
    l_P_scaled = lam * l_P_ref
    I_scaled = I_gravity(A_scaled, l_P_scaled)
    ratio = I_scaled / I_grav_ref
    test2_results.append({
        "lambda": lam,
        "I_scaled": I_scaled,
        "I_ref": I_grav_ref,
        "ratio": ratio,
        "invariant": abs(ratio - 1.0) < 1e-14
    })
    print(f"{lam:>10.3f} {I_scaled:>25.10f} {I_grav_ref:>25.10f} {ratio:>15.2e}")

test2_pass = all(r["invariant"] for r in test2_results)
print(f"\n✅ I_gravity is homogeneous degree 0: {test2_pass}")

results["tests"].append({
    "name": "I_gravity homogeneity",
    "claim": "I_gravity is homogeneous degree 0 under (l_P,A) → (λl_P, λ²A)",
    "passed": test2_pass,
    "details": test2_results
})

# ==============================================================================
# TEST 3: Saturation condition I_stella = I_gravity preserved under rescaling
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 3: SATURATION CONDITION PRESERVED UNDER RESCALING")
print("=" * 70)
print()
print("If I_stella(A₀, a₀) = I_gravity(A₀, l_P₀) at some (A₀, a₀, l_P₀),")
print("then I_stella(λ²A₀, λa₀) = I_gravity(λ²A₀, λl_P₀) for ALL λ > 0.")
print("→ The solution set is a ray, not a point.")
print()

# Find a/l_P ratio from saturation condition
# I_stella = I_gravity → (2 ln 3 / √3 a²) A = A / (4 l_P²)
# → a² / l_P² = 8 ln 3 / √3
a_over_lP_squared = 8 * np.log(3) / np.sqrt(3)
a_over_lP = np.sqrt(a_over_lP_squared)

print(f"Saturation condition: a/l_P = √(8 ln 3 / √3) = {a_over_lP:.6f}")
print(f"  a² / l_P² = 8 ln 3 / √3 = {a_over_lP_squared:.6f}")
print()

# Set reference values satisfying saturation
l_P_0 = 1.616255e-35  # actual Planck length (m)
a_0 = a_over_lP * l_P_0
A_0 = 1e-10  # arbitrary area (m²)

test3_results = []
print(f"{'λ':>10} {'I_stella':>20} {'I_gravity':>20} {'|Δ|/I':>15} {'Match':>8}")
print("-" * 73)

for lam in lambdas:
    A_s = lam**2 * A_0
    a_s = lam * a_0
    l_P_s = lam * l_P_0

    Is = I_stella(A_s, a_s)
    Ig = I_gravity(A_s, l_P_s)
    rel_diff = abs(Is - Ig) / max(abs(Is), abs(Ig)) if max(abs(Is), abs(Ig)) > 0 else 0
    match = rel_diff < 1e-14

    test3_results.append({
        "lambda": lam,
        "I_stella": Is,
        "I_gravity": Ig,
        "relative_diff": rel_diff,
        "match": match
    })
    print(f"{lam:>10.3f} {Is:>20.6e} {Ig:>20.6e} {rel_diff:>15.2e} {'✅' if match else '❌':>8}")

test3_pass = all(r["match"] for r in test3_results)
print(f"\n✅ Saturation preserved under rescaling: {test3_pass}")

results["tests"].append({
    "name": "Saturation preserved under rescaling",
    "claim": "I_stella = I_gravity is preserved for all λ > 0",
    "passed": test3_pass,
    "details": test3_results
})

# ==============================================================================
# TEST 4: Planck temperature covariance
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 4: PLANCK TEMPERATURE COVARIANCE UNDER RESCALING")
print("=" * 70)
print()
print("T_P = √(ℏc⁵ / Gk_B²)")
print("Under G → G(λ), where G = ℏc/(8πf_χ²) and f_χ → f_χ/λ:")
print("  G → λ²G → T_P → T_P/λ")
print("  T_P is NOT absolute — it scales with λ.")
print()

# In the framework: G = ℏc / (8π f_χ²)
# f_χ has dimensions of mass (GeV), so under rescaling f_χ → f_χ/λ:
# G → ℏc / (8π (f_χ/λ)²) = λ² × ℏc / (8π f_χ²) = λ² G
# T_P = √(ℏc⁵ / (G k_B²)) → T_P / λ

# Alternatively: l_P = √(ℏG/c³), so l_P → λ l_P
# T_P = M_P c² / k_B where M_P = √(ℏc/G), so M_P → M_P/λ, T_P → T_P/λ

test4_results = []
T_P_ref = T_PLANCK

print(f"T_Planck (observed) = {T_P_ref:.6e} K")
print()
print(f"{'λ':>10} {'T_P(λ)':>20} {'T_P_ref/λ':>20} {'Ratio':>15}")
print("-" * 65)

for lam in lambdas:
    # Under rescaling: G → λ²G
    G_scaled = lam**2 * G_NEWTON
    T_P_scaled = np.sqrt(HBAR * C**5 / (G_scaled * K_B**2))
    T_P_expected = T_P_ref / lam
    ratio = T_P_scaled / T_P_expected if T_P_expected != 0 else float('inf')

    test4_results.append({
        "lambda": lam,
        "T_P_scaled": T_P_scaled,
        "T_P_expected": T_P_expected,
        "ratio": ratio,
        "covariant": abs(ratio - 1.0) < 1e-14
    })
    print(f"{lam:>10.3f} {T_P_scaled:>20.6e} {T_P_expected:>20.6e} {ratio:>15.2e}")

test4_pass = all(r["covariant"] for r in test4_results)
print(f"\n✅ T_P transforms as λ⁻¹ (covariant, not absolute): {test4_pass}")

results["tests"].append({
    "name": "Planck temperature covariance",
    "claim": "T_P transforms as T_P/λ under G → λ²G (not absolute)",
    "passed": test4_pass,
    "details": test4_results
})

# ==============================================================================
# TEST 5: Minimality principle (η = 1) is scale-invariant
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 5: MINIMALITY PRINCIPLE SCALE INVARIANCE")
print("=" * 70)
print()
print("Prop 0.0.30 selects η = I_stella/I_gravity = 1 (saturation).")
print("Under rescaling: η → η (both numerator and denominator degree 0).")
print("The condition η = 1 is itself dimensionless and scale-invariant.")
print()

test5_results = []
print(f"{'λ':>10} {'η(λ)':>20} {'|η - 1|':>20}")
print("-" * 50)

for lam in lambdas:
    A_s = lam**2 * A_0
    a_s = lam * a_0
    l_P_s = lam * l_P_0

    eta = I_stella(A_s, a_s) / I_gravity(A_s, l_P_s)

    test5_results.append({
        "lambda": lam,
        "eta": eta,
        "deviation_from_1": abs(eta - 1.0),
        "invariant": abs(eta - 1.0) < 1e-14
    })
    print(f"{lam:>10.3f} {eta:>20.15f} {abs(eta - 1.0):>20.2e}")

test5_pass = all(r["invariant"] for r in test5_results)
print(f"\n✅ η = 1 is scale-invariant: {test5_pass}")

results["tests"].append({
    "name": "Minimality principle scale invariance",
    "claim": "η = I_stella/I_gravity = 1 is preserved under rescaling",
    "passed": test5_pass,
    "details": test5_results
})

# ==============================================================================
# TEST 6: What the saturation DOES determine (the ratio a/l_P)
# ==============================================================================

print("\n" + "=" * 70)
print("TEST 6: WHAT SATURATION DETERMINES — THE RATIO a/l_P")
print("=" * 70)
print()

# From I_stella = I_gravity:
# (2 ln 3 / √3 a²) A = A / (4 l_P²)
# → a/l_P = √(8 ln 3 / √3) ≈ 2.253

ratio_theory = np.sqrt(8 * np.log(3) / np.sqrt(3))
print(f"Theoretical: a/l_P = √(8 ln 3 / √3) = {ratio_theory:.6f}")
print()

# Verify with actual framework values
# From Prop 0.0.17r: a² = (8 ln 3 / √3) l_P²
a_squared_over_lP_squared = 8 * np.log(3) / np.sqrt(3)
print(f"a²/l_P² = 8 ln 3 / √3 = {a_squared_over_lP_squared:.6f}")
print(f"a/l_P = {np.sqrt(a_squared_over_lP_squared):.6f}")
print()

# This ratio is preserved under rescaling (both scale the same way)
test6_results = []
print(f"{'λ':>10} {'a(λ)/l_P(λ)':>20} {'Theory':>20} {'Match':>10}")
print("-" * 60)

for lam in lambdas:
    a_s = lam * a_0
    l_P_s = lam * l_P_0
    ratio_computed = a_s / l_P_s
    match = abs(ratio_computed - ratio_theory) / ratio_theory < 1e-14

    test6_results.append({
        "lambda": lam,
        "ratio_computed": ratio_computed,
        "ratio_theory": ratio_theory,
        "match": match
    })
    print(f"{lam:>10.3f} {ratio_computed:>20.10f} {ratio_theory:>20.10f} {'✅' if match else '❌':>10}")

test6_pass = all(r["match"] for r in test6_results)
print(f"\n✅ Ratio a/l_P is the ONLY content of saturation: {test6_pass}")

results["tests"].append({
    "name": "Ratio a/l_P determination",
    "claim": "Saturation determines a/l_P = √(8ln3/√3) and nothing more",
    "passed": test6_pass,
    "ratio_value": ratio_theory
})

# ==============================================================================
# SUMMARY
# ==============================================================================

print("\n" + "=" * 70)
print("SUMMARY: PATH A SATURATION RESCALING ANALYSIS")
print("=" * 70)
print()

all_passed = all(t["passed"] for t in results["tests"])
results["overall_status"] = "PASSED" if all_passed else "FAILED"

for t in results["tests"]:
    status = "✅ PASS" if t["passed"] else "❌ FAIL"
    print(f"  {status}: {t['name']}")
    print(f"         {t['claim']}")

print()
print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("The holographic saturation condition (Prop 0.0.30) does NOT break")
print("the projective ambiguity:")
print()
print("  1. I_stella and I_gravity are both homogeneous degree 0")
print("  2. Their ratio η = 1 is dimensionless and scale-invariant")
print("  3. T_P is covariant (transforms as λ⁻¹), not absolute")
print("  4. The ONLY content of saturation is the ratio a/l_P = √(8ln3/√3)")
print()
print("The saturation condition answers 'why equality?' (minimality principle)")
print("but NOT 'what scale?' — consistent with the negative result that one")
print("experimental input is irreducible.")
print()
print(f"Overall status: {results['overall_status']}")

# Save results
output_path = "verification/foundations/investigation_path_a_saturation_rescaling_results.json"
with open(output_path, "w") as f:
    json.dump(results, f, indent=2, default=str)
print(f"\nResults saved to {output_path}")

if __name__ == "__main__":
    pass
