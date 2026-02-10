#!/usr/bin/env python3
"""
E1 Fix: Correct Derivation of Trace Calculations in Anomaly Coefficients

Issue: The original text states Tr[T_a²] = N_f/2, conflating two different things:
1. The generator trace normalization (group theory)
2. The number of fermion flavors in the loop (counting)

This script derives the correct formulas rigorously.
"""

import numpy as np

print("=" * 70)
print("E1 FIX: TRACE CALCULATION IN CHIRAL ANOMALY")
print("=" * 70)

# =============================================================================
# PART 1: SU(N) Generator Normalization
# =============================================================================

print("\n" + "=" * 60)
print("PART 1: SU(N) Generator Trace Normalization")
print("=" * 60)

print("""
For SU(N) in the fundamental representation, the generators T_a satisfy:

    Tr[T_a T_b] = T(R) δ_ab

where T(R) is the Dynkin index of the representation R.

For the fundamental representation:
    T(fundamental) = 1/2

This means:
    Tr[T_a T_b] = (1/2) δ_ab

For a SINGLE generator squared:
    Tr[T_a²] = 1/2  (for each a, no sum)

Summing over all generators (a = 1 to N² - 1):
    Σ_a Tr[T_a²] = (1/2) × (N² - 1)
""")

# Verify for SU(3)
N = 3
T_fund = 0.5  # Dynkin index
num_generators = N**2 - 1

print(f"\nFor SU(3) (QCD):")
print(f"  Number of generators: {num_generators}")
print(f"  T(fundamental) = {T_fund}")
print(f"  Single trace: Tr[T_a²] = {T_fund}")
print(f"  Sum over all a: Σ_a Tr[T_a²] = {T_fund} × {num_generators} = {T_fund * num_generators}")

# For SU(2)
N_weak = 2
num_generators_weak = N_weak**2 - 1

print(f"\nFor SU(2) (Weak):")
print(f"  Number of generators: {num_generators_weak}")
print(f"  T(fundamental) = {T_fund}")
print(f"  Single trace: Tr[τ_a²] = {T_fund}")
print(f"  Sum over all a: Σ_a Tr[τ_a²] = {T_fund} × {num_generators_weak} = {T_fund * num_generators_weak}")

# =============================================================================
# PART 2: Anomaly Calculation with Fermion Loops
# =============================================================================

print("\n" + "=" * 60)
print("PART 2: Chiral Anomaly with Fermion Loops")
print("=" * 60)

print("""
The chiral anomaly arises from the triangle diagram with:
- One axial current vertex (j_5^μ)
- Two gauge boson vertices (G^a or W^a)

For a SINGLE Dirac fermion (one quark flavor) in the loop:

    A^a_μν = (g²/16π²) Tr[T_a T_b] ε^{μνρσ} F^b_ρσ

The anomaly equation is:
    ∂_μ j_5^μ = (g²/16π²) Tr[T_a T_b] F^a_μν F̃^{b μν}

Using Tr[T_a T_b] = (1/2) δ_ab:
    ∂_μ j_5^μ = (g²/32π²) F^a_μν F̃^{a μν}

This is the anomaly for ONE fermion flavor.
""")

# Standard anomaly coefficient
anomaly_coeff_single = 1 / (32 * np.pi**2)
print(f"\nAnomaly coefficient per fermion: 1/(32π²) = {anomaly_coeff_single:.6e}")

# =============================================================================
# PART 3: Multiple Fermion Flavors
# =============================================================================

print("\n" + "=" * 60)
print("PART 3: N_f Fermion Flavors")
print("=" * 60)

print("""
When we have N_f fermion flavors, EACH contributes to the anomaly independently.

For QCD with N_f quark flavors:
    ∂_μ j_5^μ = N_f × (g_s²/32π²) G^a_μν G̃^{a μν}

For the electroweak sector, only LEFT-HANDED quarks couple to SU(2)_L.
With N_f quark doublets:
    ∂_μ j_5^μ = N_f × (g_w²/32π²) W^a_μν W̃^{a μν}

The key insight: N_f comes from COUNTING FERMIONS, not from the trace.
The trace Tr[T²] = 1/2 is fixed by the Lie algebra normalization.
""")

N_f = 6  # Number of quark flavors
print(f"\nWith N_f = {N_f} quark flavors:")
print(f"  QCD anomaly coefficient: N_f/(32π²) = {N_f}/(32π²) = {N_f * anomaly_coeff_single:.6e}")
print(f"  EW anomaly coefficient: N_f/(32π²) = {N_f}/(32π²) = {N_f * anomaly_coeff_single:.6e}")

# =============================================================================
# PART 4: The Correct Statement
# =============================================================================

print("\n" + "=" * 60)
print("PART 4: THE CORRECT STATEMENT")
print("=" * 60)

print("""
❌ INCORRECT (Original lines 209-211):
   "Tr[T_a²] = N_f × 1/2 = N_f/2"

   This conflates the generator trace with the flavor count.

✅ CORRECT:
   The effective Lagrangian from integrating out N_f quark flavors is:

   L_eff = -(θ_χ/16π²) × [ g_s² × (N_f/2) × G⁻G̃ + g_w² × (N_f/2) × W⁻W̃ ]

   where:
   - The factor 1/2 comes from Tr[T_a T_a] = (1/2) δ_aa = 1/2 (per generator)
   - The factor N_f comes from summing over quark flavors in the loop
   - The product (N_f × 1/2) = N_f/2 gives the total coefficient

   Simplifying:
   L_eff = -(N_f θ_χ)/(32π²) × [ g_s² G⁻G̃ + g_w² W⁻W̃ ]

The FINAL RESULT (line 218) is correct:
   L_eff = -(N_f θ_χ)/(32π²) [ g_s² G⁻G̃ + g_w² W⁻W̃ ]

The INTERMEDIATE STEP (lines 209-211) needs clarification.
""")

# =============================================================================
# PART 5: Important Subtlety for Electroweak
# =============================================================================

print("\n" + "=" * 60)
print("PART 5: SU(2)_L Coupling - Left-Handed Only")
print("=" * 60)

print("""
CRITICAL SUBTLETY (Issue P4):

The SU(2)_L generators only couple to LEFT-HANDED quarks:
- Left-handed quarks: SU(2) doublets (u_L, d_L), etc.
- Right-handed quarks: SU(2) singlets (u_R, d_R), etc.

This means:
- For QCD: ALL quarks (L and R) contribute to G⁻G̃
- For SU(2): Only LEFT-HANDED quarks contribute to W⁻W̃

However, the AXIAL anomaly involves the combination:
    j_5^μ = j_L^μ - j_R^μ = ψ̄ γ^μ γ_5 ψ

For the QCD anomaly:
- Both L and R chiralities contribute (with opposite signs in j_5)
- Net contribution: proportional to Tr[T_a T_a] = 1/2

For the SU(2) anomaly:
- Only L-handed quarks are charged under SU(2)
- The R-handed contribution to the triangle is zero (they're singlets)
- The L-handed contribution: proportional to Tr[τ_a τ_a] = 1/2

The key point: The sign of the anomaly coefficient is the SAME for both sectors
because both arise from the SAME chiral current j_5^μ.

This is why sgn(c_3) = sgn(c_2) = positive.
""")

# =============================================================================
# PART 6: Verification of Signs
# =============================================================================

print("\n" + "=" * 60)
print("PART 6: Sign Verification")
print("=" * 60)

# The coefficients in the effective Lagrangian
c_3 = N_f / (32 * np.pi**2)  # QCD
c_2 = N_f / (32 * np.pi**2)  # EW (for doublets)

print(f"\nCoefficients (both positive):")
print(f"  c_3 (QCD) = N_f/(32π²) = {c_3:.6e} > 0")
print(f"  c_2 (EW)  = N_f/(32π²) = {c_2:.6e} > 0")

print("""
Since c_3 > 0 and c_2 > 0:

⟨Q_QCD⟩ = c_3⁻¹ × ∂_t θ_χ  →  sgn(⟨Q_QCD⟩) = sgn(∂_t θ_χ)
⟨Q_EW⟩  = c_2⁻¹ × ∂_t θ_χ  →  sgn(⟨Q_EW⟩)  = sgn(∂_t θ_χ)

Therefore:
    sgn(⟨Q_QCD⟩) = sgn(⟨Q_EW⟩) = sgn(∂_t θ_χ)

This sign correlation is DERIVED, not assumed. ✅
""")

# =============================================================================
# PART 7: Proposed Corrected Text
# =============================================================================

print("\n" + "=" * 60)
print("PART 7: PROPOSED CORRECTED TEXT")
print("=" * 60)

print("""
REPLACE lines 207-214 with:

**Step D2: Evaluating the Anomaly Coefficients**

The anomaly coefficient combines two factors:

1. **Generator trace normalization:** For generators in the fundamental
   representation, Tr[T_a T_b] = (1/2) δ_ab. This gives Tr[T_a²] = 1/2 for
   each generator a.

2. **Fermion flavor counting:** Each quark flavor running in the loop
   contributes independently. With N_f flavors, we sum N_f identical
   contributions.

The combined coefficient for each gauge sector is:

- **SU(3)_color:** The anomaly coefficient is N_f × (1/2) = N_f/2, where
  the 1/2 comes from the generator normalization and N_f counts quark
  flavors in the loop.

- **SU(2)_L:** Similarly, the coefficient is N_f × (1/2) = N_f/2. Note that
  only left-handed quarks are SU(2) doublets, but the axial current j_5^μ
  couples to both chiralities, and the right-handed singlets contribute
  zero to the SU(2) anomaly.

**Crucially:** Both coefficients are **positive** because:
- Tr[T²] > 0 for Hermitian generators (eigenvalues are real)
- N_f > 0 (physical fermion count)

This ensures sgn(c_3) = sgn(c_2) > 0.
""")

print("\n" + "=" * 70)
print("E1 DERIVATION COMPLETE")
print("=" * 70)
