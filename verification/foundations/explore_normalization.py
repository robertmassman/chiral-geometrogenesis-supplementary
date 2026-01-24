#!/usr/bin/env python3
"""
Explore the 2π² normalization and its connection to gauge dimension.

Key finding: 2π² = 16π² / 8 = 16π² / (2 × dim(adj_EW))

This suggests the formula can be rewritten with standard trace anomaly
normalization (16π²) plus an explicit factor of 2×dim.
"""

import numpy as np

# =============================================================================
# Physical constants
# =============================================================================

v_H_observed = 246.22  # GeV (PDG 2024)
sqrt_sigma = 0.440  # GeV (FLAG 2024)
dim_adj_EW = 4  # dim(su(2)) + dim(u(1)) = 3 + 1
Delta_a_EW = 1/120

# Standard normalization
sixteen_pi_sq = 16 * np.pi**2  # Standard trace anomaly: (4π)² ≈ 157.91
two_pi_sq = 2 * np.pi**2  # Our formula uses this ≈ 19.74

print("=" * 70)
print("NORMALIZATION ANALYSIS")
print("=" * 70)

# =============================================================================
# Section 1: Observed Ratio and Required Normalization
# =============================================================================

print("\n" + "=" * 70)
print("1. OBSERVED RATIO AND REQUIRED NORMALIZATION")
print("=" * 70)

observed_ratio = v_H_observed / sqrt_sigma
ln_observed = np.log(observed_ratio)

print(f"\nObserved: v_H/√σ = {v_H_observed}/{sqrt_sigma} = {observed_ratio:.2f}")
print(f"ln(ratio) = {ln_observed:.4f}")

# What normalization gives the right answer?
# ln(ratio) = 1/dim + 120/norm
# 6.327 = 0.25 + 120/norm
# norm = 120 / (6.327 - 0.25) = 120 / 6.077 = 19.75

required_norm = 120 / (ln_observed - 1/dim_adj_EW)
print(f"\nRequired normalization (with 1/dim term):")
print(f"  norm = 120 / (ln_observed - 1/dim) = {required_norm:.4f}")
print(f"  Compare to 2π² = {two_pi_sq:.4f}")
print(f"  Match: {100*two_pi_sq/required_norm:.2f}%")

# =============================================================================
# Section 2: The Factor of 8
# =============================================================================

print("\n" + "=" * 70)
print("2. THE FACTOR OF 8")
print("=" * 70)

factor = sixteen_pi_sq / two_pi_sq
print(f"\n16π² / 2π² = {sixteen_pi_sq:.2f} / {two_pi_sq:.2f} = {factor:.1f}")

print(f"\nPossible interpretations of 8:")
print(f"  - 2 × dim(adj_EW) = 2 × {dim_adj_EW} = {2*dim_adj_EW}")
print(f"  - dim(adj_QCD) = 8")
print(f"  - χ(S⁴) × 4 = 2 × 4 = 8")
print(f"  - 8 vertices of tetrahedron")

# =============================================================================
# Section 3: Reformulated Formula
# =============================================================================

print("\n" + "=" * 70)
print("3. REFORMULATED FORMULA WITH STANDARD 16π² NORMALIZATION")
print("=" * 70)

# Original formula:
# ln(v/√σ) = 1/dim + 120/(2π²)
#          = 1/dim + 120 × 8 / (16π²)
#          = 1/dim + 960 / (16π²)
#          = 1/dim + (2 × dim × 120) / (16π²)  [since 2×dim = 8]
#          = 1/dim + (2 × dim) / (16π² × Δa)

# Reformulated:
# ln(v/√σ) = 1/dim + (2 × dim) / (16π² × Δa)

print("\nOriginal formula:")
print("  ln(v_H/√σ) = 1/dim(adj) + 1/(2π² × Δa)")

print("\nReformulated with standard 16π²:")
print("  ln(v_H/√σ) = 1/dim(adj) + (2 × dim(adj)) / (16π² × Δa)")

# Verify numerically
term1 = 1/dim_adj_EW
term2_original = 1/(two_pi_sq * Delta_a_EW)
term2_reformulated = (2 * dim_adj_EW) / (sixteen_pi_sq * Delta_a_EW)

print(f"\nNumerical verification:")
print(f"  Term 1: 1/dim = 1/{dim_adj_EW} = {term1:.4f}")
print(f"  Term 2 (original): 1/(2π² × Δa) = {term2_original:.4f}")
print(f"  Term 2 (reformulated): (2 × dim)/(16π² × Δa) = {term2_reformulated:.4f}")
print(f"  Agreement: {100*term2_reformulated/term2_original:.4f}%")

total_exponent = term1 + term2_original
predicted_ratio = np.exp(total_exponent)
predicted_v_H = sqrt_sigma * predicted_ratio

print(f"\nTotal exponent: {total_exponent:.4f}")
print(f"Predicted ratio: {predicted_ratio:.2f}")
print(f"Predicted v_H: {predicted_v_H:.2f} GeV")
print(f"Observed v_H: {v_H_observed} GeV")
print(f"Agreement: {100*(1 - abs(predicted_v_H - v_H_observed)/v_H_observed):.2f}%")

# =============================================================================
# Section 4: Alternative Factorization
# =============================================================================

print("\n" + "=" * 70)
print("4. ALTERNATIVE FACTORIZATION")
print("=" * 70)

# Can we write: ln(v/√σ) = (1/dim) × [1 + 2×dim²/(16π²×Δa)]?

bracket_term = 1 + (2 * dim_adj_EW**2) / (sixteen_pi_sq * Delta_a_EW)
alt_exponent = (1/dim_adj_EW) * bracket_term

print("\nAlternative form:")
print("  ln(v_H/√σ) = (1/dim) × [1 + 2×dim²/(16π²×Δa)]")
print(f"\nNumerical check:")
print(f"  Bracket term = 1 + 2×{dim_adj_EW}²/(16π²×1/120)")
print(f"              = 1 + {2*dim_adj_EW**2}×120/16π²")
print(f"              = 1 + {2*dim_adj_EW**2 * 120/sixteen_pi_sq:.4f}")
print(f"              = {bracket_term:.4f}")
print(f"  (1/dim) × bracket = (1/{dim_adj_EW}) × {bracket_term:.4f} = {alt_exponent:.4f}")
print(f"  Compare to ln(observed) = {ln_observed:.4f}")
print(f"  Agreement: {100*(1 - abs(alt_exponent - ln_observed)/ln_observed):.2f}%")

# =============================================================================
# Section 5: Comparison of Normalizations
# =============================================================================

print("\n" + "=" * 70)
print("5. COMPARISON OF DIFFERENT NORMALIZATIONS")
print("=" * 70)

normalizations = {
    "2π²": two_pi_sq,
    "π²": np.pi**2,
    "4π²": 4 * np.pi**2,
    "16π² (standard)": sixteen_pi_sq,
    "8π²": 8 * np.pi**2,
}

print(f"\n{'Normalization':<20} {'Value':<10} {'Exponent':<12} {'Ratio':<12} {'Error':<10}")
print("-" * 64)

for name, norm in normalizations.items():
    exponent = 1/dim_adj_EW + 120/norm
    ratio = np.exp(exponent)
    error = 100 * (ratio - observed_ratio) / observed_ratio
    print(f"{name:<20} {norm:<10.2f} {exponent:<12.4f} {ratio:<12.2f} {error:+.1f}%")

# =============================================================================
# Section 6: Testing the 2×dim Connection
# =============================================================================

print("\n" + "=" * 70)
print("6. TESTING: DOES 16π²/(2×dim) WORK FOR OTHER GAUGE GROUPS?")
print("=" * 70)

# If 2π² = 16π²/(2×dim), then for different gauge groups:

gauge_groups = {
    "SU(2)×U(1) (EW)": 4,
    "SU(3) (QCD)": 8,
    "SU(5) (GUT)": 24,
    "SO(10)": 45,
}

print(f"\n{'Gauge Group':<20} {'dim(adj)':<10} {'16π²/(2×dim)':<15} {'Compare to 2π²':<15}")
print("-" * 60)

for name, dim in gauge_groups.items():
    effective_norm = sixteen_pi_sq / (2 * dim)
    ratio_to_2pi2 = effective_norm / two_pi_sq
    print(f"{name:<20} {dim:<10} {effective_norm:<15.4f} {ratio_to_2pi2:.4f}×")

print("\nNote: Only for dim=4 (EW) does 16π²/(2×dim) = 2π² exactly.")
print("This suggests the 2π² normalization is EW-specific!")

# =============================================================================
# Section 7: What Does This Mean?
# =============================================================================

print("\n" + "=" * 70)
print("7. SUMMARY")
print("=" * 70)

print("""
FINDINGS:

1. The 2π² normalization can be written as:
   2π² = 16π² / 8 = 16π² / (2 × dim(adj_EW))

2. The formula can be rewritten with standard 16π² normalization:
   ln(v_H/√σ) = 1/dim + (2 × dim) / (16π² × Δa)
              = 1/4 + 8 / (16π² × 1/120)
              = 0.25 + 6.08 = 6.33 ✓

3. Alternatively, factoring out 1/dim:
   ln(v_H/√σ) = (1/dim) × [1 + 2×dim² / (16π² × Δa)]

4. The 2π² = 16π²/(2×dim) relationship is SPECIFIC to the EW sector
   (dim = 4). It would give different normalizations for other gauge groups.

5. This may explain why the formula fails for QCD: the normalization
   is inherently tied to dim(adj_EW) = 4.

OPEN QUESTIONS:

1. Why does the factor of 2 appear in 2×dim?
   - Euler characteristic χ(S⁴) = 2?
   - Dilaton kinetic normalization?
   - Complex vs real d.o.f. in Higgs doublet?

2. Is the 16π² / (2×dim) structure derivable from the dilaton
   effective action?

3. Does this explain the EW-specificity of the formula?
""")

print("=" * 70)
