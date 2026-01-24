#!/usr/bin/env python3
"""
Explore the origin of the exp(1/Δa) functional form in the hierarchy formula.

The unified formula:
    v_H = √σ × exp(1/dim + 1/(2π²Δa))

Why does the hierarchy take this specific exponential form?

This script investigates several candidate derivations:
1. RG flow integration with β-function
2. Dilaton effective action
3. Instanton-like contributions
4. Coleman-Weinberg potential analogy
5. Dimensional transmutation
"""

import numpy as np

print("=" * 70)
print("INVESTIGATING THE exp(1/Δa) FUNCTIONAL FORM")
print("=" * 70)

# Physical constants
v_H_observed = 246.22  # GeV
sqrt_sigma = 0.440  # GeV
Delta_a_EW = 1/120
dim_EW = 4

# The observed ratio
ln_ratio = np.log(v_H_observed / sqrt_sigma)
print(f"\nObserved: ln(v_H/√σ) = ln({v_H_observed}/{sqrt_sigma}) = {ln_ratio:.4f}")

# The formula prediction
formula_exponent = 1/dim_EW + 1/(2 * np.pi**2 * Delta_a_EW)
print(f"Formula:  1/dim + 1/(2π²Δa) = 1/{dim_EW} + 120/(2π²) = {formula_exponent:.4f}")
print(f"Match: {100*abs(ln_ratio - formula_exponent)/ln_ratio:.2f}% difference")

# =============================================================================
# Section 1: RG Flow Integration Approach
# =============================================================================

print("\n" + "=" * 70)
print("1. RG FLOW INTEGRATION APPROACH")
print("=" * 70)

print("""
In QFT, scale hierarchies often arise from RG running. Consider:

The β-function for a coupling g determines how g runs with scale μ:
    dg/d(ln μ) = β(g)

For asymptotically free theories, β(g) = -b₀g³/(16π²) + O(g⁵)

Integrating gives:
    g²(μ) = g²(Λ) / [1 + (b₀g²(Λ)/(8π²))ln(μ/Λ)]

The confinement/symmetry breaking scale emerges when g → ∞:
    Λ_IR = Λ_UV × exp(-8π²/(b₀g²(Λ_UV)))

This is DIMENSIONAL TRANSMUTATION: an exponential hierarchy from RG running.
""")

# For EW, the relevant β-function coefficient
b0_SU2 = 19/6  # SU(2) with Higgs doublet + leptons (approximate)
g2_weak = np.sqrt(4 * np.pi * 0.034)  # g₂ at weak scale

print("For SU(2) weak interactions:")
print(f"  b₀ ≈ {b0_SU2:.3f}")
print(f"  g₂(M_W) ≈ {g2_weak:.3f}")

# What exponent would dimensional transmutation give?
dim_trans_exp = 8 * np.pi**2 / (b0_SU2 * g2_weak**2)
print(f"\nDimensional transmutation exponent: 8π²/(b₀g²) = {dim_trans_exp:.1f}")
print(f"Formula exponent: {formula_exponent:.2f}")
print(f"These don't match — dimensional transmutation is NOT the mechanism.")

# =============================================================================
# Section 2: Central Charge Flow and Dilaton Action
# =============================================================================

print("\n" + "=" * 70)
print("2. DILATON EFFECTIVE ACTION APPROACH")
print("=" * 70)

print("""
The Komargodski-Schwimmer proof of the a-theorem uses a dilaton effective action:

    S_eff[τ] = ∫d⁴x √g [f² (∂τ)² + Δa·(∂τ)⁴/τ⁴ + Δc·W²τ² + ...]

where τ = e^(-σ) is the dilaton (Goldstone of broken scale invariance).

The key insight: The dilaton couples to the trace anomaly coefficients.

For a Higgs-like scalar acquiring a VEV, the dilaton-Higgs mixing gives:
    τ ∝ H/v

The VEV is determined by minimizing an effective potential that depends on
the anomaly coefficients. This could give:

    v ∝ Λ_UV × exp(const/Δa)

if the anomaly coefficient appears in the denominator of the exponent.
""")

# The formula has 1/(2π²Δa) in the exponent
# If Δa = c(scalar) = 1/120, then:
coeff = 1/(2 * np.pi**2 * Delta_a_EW)
print(f"The formula term: 1/(2π²Δa) = 1/(2π² × 1/120) = 120/(2π²) = {coeff:.3f}")

# This is approximately 6.08
# Compare to other natural combinations
print("\nComparing to natural combinations:")
print(f"  1/(2π²Δa) = {coeff:.4f}")
print(f"  1/(16π²Δa) = {1/(16*np.pi**2*Delta_a_EW):.4f}")
print(f"  120 = 1/Δa")
print(f"  120/(2π²) ≈ 6.08")
print(f"  120/(16π²) ≈ 0.76")

# =============================================================================
# Section 3: The Specific Structure 1/(2π²Δa)
# =============================================================================

print("\n" + "=" * 70)
print("3. WHY 2π² AND NOT 16π²?")
print("=" * 70)

print("""
Standard trace anomaly normalization uses 16π²:
    ⟨Tᵘμ⟩ = (1/16π²)[a E₄ - c W²]

But our formula uses 2π². From the earlier analysis:
    2π² = 16π²/(2×dim_EW) = 16π²/8

This suggests the formula arises from:
    - Standard anomaly with 16π² normalization
    - Divided by (2 × dim_EW) = 8 for the specific EW structure

The full exponent structure:
    exp(1/dim + 1/(2π²Δa)) = exp(1/dim + 2×dim/(16π²Δa))

For dim = 4:
    = exp(1/4 + 8/(16π²Δa))
    = exp(1/4 + 1/(2π²Δa))
""")

# Verify this structure
exp_form1 = 1/dim_EW + 1/(2 * np.pi**2 * Delta_a_EW)
exp_form2 = 1/dim_EW + 2*dim_EW/(16 * np.pi**2 * Delta_a_EW)
print(f"Form 1: 1/dim + 1/(2π²Δa) = {exp_form1:.4f}")
print(f"Form 2: 1/dim + 2dim/(16π²Δa) = {exp_form2:.4f}")
print(f"These are identical: {np.isclose(exp_form1, exp_form2)}")

# =============================================================================
# Section 4: Instanton-Like Contribution
# =============================================================================

print("\n" + "=" * 70)
print("4. INSTANTON-LIKE CONTRIBUTION")
print("=" * 70)

print("""
Instantons contribute non-perturbatively with action:
    S_inst = 8π²/g²

giving amplitudes ~ exp(-S_inst) = exp(-8π²/g²)

If we identify:
    g² ↔ Δa × (some factor)

we might get exp(const/Δa) structure.

For the formula to work:
    1/(2π²Δa) = 8π²/g²_eff

Solving: g²_eff = 16π⁴ × Δa = 16π⁴/120 ≈ 12.9
         g_eff ≈ 3.6

This is a strong coupling! The 'instanton' interpretation would require
g_eff ~ 3.6, which is between weak (g~0.6) and strong (g~1-3 at GeV).
""")

g_eff_sq = 16 * np.pi**4 * Delta_a_EW
g_eff = np.sqrt(g_eff_sq)
print(f"Effective coupling from instanton interpretation:")
print(f"  g²_eff = 16π⁴ × Δa = {g_eff_sq:.2f}")
print(f"  g_eff = {g_eff:.2f}")
print(f"\nThis doesn't correspond to a known SM coupling.")

# =============================================================================
# Section 5: Coleman-Weinberg Analogy
# =============================================================================

print("\n" + "=" * 70)
print("5. COLEMAN-WEINBERG ANALOGY")
print("=" * 70)

print("""
The Coleman-Weinberg mechanism generates a VEV from quantum corrections:

    V_eff(φ) = λφ⁴/4 + (β_λ/64π²)φ⁴[ln(φ²/μ²) - 25/6]

For massless scalar QED, the VEV is determined by:
    v² ∝ μ² × exp(-16π²/3e⁴)

where e is the gauge coupling.

The exponential structure exp(-const/coupling⁴) differs from our
exp(+const/Δa) = exp(+const × 120).

However, there's a conceptual similarity:
- Both generate exponential hierarchies
- Both involve 16π² (or 2π² = 16π²/8) factors
- Both relate to loop effects (β-functions, anomalies)
""")

# =============================================================================
# Section 6: The Key Insight: Anomaly-Driven Hierarchy
# =============================================================================

print("\n" + "=" * 70)
print("6. ANOMALY-DRIVEN HIERARCHY")
print("=" * 70)

print("""
PROPOSED DERIVATION:

The central claim is that the Higgs VEV is determined by anomaly matching
between the UV (unbroken EW) and IR (broken EW) theories.

1. The trace anomaly in 4D:
   ⟨Tᵘμ⟩ = (1/16π²)[a E₄ - c W²]

2. The flow from UV to IR changes the central charges:
   Δa = a_UV - a_IR
   Δc = c_UV - c_IR

3. For the physical Higgs: Δa_eff = c(Higgs) = 1/120

4. The dilaton-Higgs identification relates:
   - The Higgs VEV v to the scale of conformal breaking
   - The dilaton decay constant f to the UV scale

5. The anomaly matching condition constrains:
   v/Λ ∝ exp(const/Δa_eff)

where the exponential arises from integrating the trace anomaly
over the RG flow.

The specific form exp(1/(2π²Δa)) arises from:
- The standard 16π² normalization of the anomaly
- The factor of 8 = 2×dim for the EW structure
- The definition Δa_eff = c(physical Higgs) = 1/120
""")

# =============================================================================
# Section 7: Verifying the Complete Formula
# =============================================================================

print("\n" + "=" * 70)
print("7. VERIFYING THE COMPLETE FORMULA STRUCTURE")
print("=" * 70)

print("""
The unified formula:
    v_H = √σ × exp(1/dim + 1/(2π²Δa))

can be rewritten as:
    ln(v_H/√σ) = 1/dim + 2×dim/(16π²Δa)

For dim=4, Δa=1/120:
    ln(v_H/√σ) = 1/4 + 8×120/(16π²)
               = 0.25 + 960/(16π²)
               = 0.25 + 6.08
               = 6.33
""")

# Component breakdown
term1 = 1/dim_EW
term2 = 2*dim_EW * (1/Delta_a_EW) / (16 * np.pi**2)
total = term1 + term2

print(f"Term 1 (gauge structure): 1/dim = 1/{dim_EW} = {term1:.4f}")
print(f"Term 2 (anomaly flow): 2×dim/(16π²Δa) = 8×120/(16π²) = {term2:.4f}")
print(f"Total exponent: {total:.4f}")
print(f"Predicted v_H = {sqrt_sigma} × exp({total:.4f}) = {sqrt_sigma * np.exp(total):.2f} GeV")
print(f"Observed v_H = {v_H_observed} GeV")

# =============================================================================
# Section 8: Summary and Open Questions
# =============================================================================

print("\n" + "=" * 70)
print("8. SUMMARY")
print("=" * 70)

print("""
THE FUNCTIONAL FORM exp(1/Δa):

The exponential structure exp(const/Δa) is characteristic of:
1. Anomaly-driven scale generation
2. Non-perturbative effects (instantons, tunneling)
3. RG flow integration over many decades

For the EW hierarchy formula, the specific form appears to arise from:

    exp(1/(2π²Δa)) = exp(2×dim/(16π²Δa))

where:
- 16π² is the standard trace anomaly normalization
- 2×dim = 8 is an EW-specific factor
- Δa = c(physical Higgs) = 1/120 is the effective central charge flow

This gives: exp(8×120/(16π²)) = exp(6.08) ≈ 437

Combined with exp(1/dim) = exp(0.25) ≈ 1.28:
    Total ratio ≈ 437 × 1.28 ≈ 561

And: √σ × 561 ≈ 0.44 × 561 ≈ 247 GeV ✓

OPEN QUESTIONS:
1. Can we derive the 2×dim factor from first principles?
2. What is the exact mechanism that produces 1/Δa in the exponent?
3. Is there a path integral derivation of this formula?
""")

print("\n" + "=" * 70)
