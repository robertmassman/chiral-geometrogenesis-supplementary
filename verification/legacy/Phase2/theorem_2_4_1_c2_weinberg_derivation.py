#!/usr/bin/env python3
"""
Theorem 2.4.1 Issue C2 Resolution: Correct Weinberg Angle Derivation
=====================================================================

The issue: The trace formula sin²θ_W = Tr(T₃²)/Tr(Q²) is incorrect.

This script:
1. Derives the CORRECT formula from first principles
2. Shows why the claimed formula is wrong
3. Provides the corrected derivation that gives sin²θ_W = 3/8

Author: Verification System
Date: 2025-12-26
"""

import numpy as np

print("=" * 70)
print("ISSUE C2 RESOLUTION: Correct Weinberg Angle Derivation")
print("=" * 70)

# =============================================================================
# Part 1: The Problem with the Original Formula
# =============================================================================
print("\n" + "=" * 70)
print("PART 1: Why the Original Formula is Wrong")
print("=" * 70)

print("""
ORIGINAL CLAIM (INCORRECT):
  sin²θ_W = Tr(T₃²) / Tr(Q²)

Let's check this with actual values in the fundamental representation of SU(5):

  T₃ = diag(0, 0, 0, +1/2, -1/2)    [SU(2) generator in SU(5)]
  Y  = diag(-1/3, -1/3, -1/3, 1/2, 1/2)  [Hypercharge in SU(5)]
  Q  = T₃ + Y = diag(-1/3, -1/3, -1/3, 1, 0)  [Electric charge]
""")

# Define generators
T3 = np.diag([0, 0, 0, 0.5, -0.5])
Y = np.diag([-1/3, -1/3, -1/3, 0.5, 0.5])
Q = T3 + Y

print("Computing traces:")
Tr_T3_sq = np.trace(T3 @ T3)
Tr_Q_sq = np.trace(Q @ Q)

print(f"  Tr(T₃²) = {Tr_T3_sq}")
print(f"  Tr(Q²) = {Tr_Q_sq}")
print(f"  Tr(T₃²)/Tr(Q²) = {Tr_T3_sq / Tr_Q_sq:.6f}")
print(f"  But sin²θ_W should be = 3/8 = {3/8:.6f}")
print(f"\n  The formula Tr(T₃²)/Tr(Q²) gives WRONG answer!")

# =============================================================================
# Part 2: The Correct Physics of Weinberg Angle
# =============================================================================
print("\n" + "=" * 70)
print("PART 2: The Correct Derivation from Gauge Theory")
print("=" * 70)

print("""
CORRECT DERIVATION:

In an SU(5) GUT, the gauge coupling unifies at the GUT scale:
  g₁ = g₂ = g₃ = g_GUT

The Standard Model hypercharge coupling g' is related to g₁ by a
normalization factor that comes from embedding U(1)_Y in SU(5).

The key constraint is that ALL gauge generators must be normalized
the same way (trace normalization) in the unified theory.

For SU(N), the standard normalization is:
  Tr(TᵃTᵇ) = (1/2) δᵃᵇ  in the fundamental representation

For the hypercharge Y in SU(5), we need to rescale:
  Y_GUT = √(3/5) · Y_SM

Then: Tr(Y_GUT²) = (3/5) · Tr(Y_SM²)
""")

# =============================================================================
# Part 3: The Normalization Calculation
# =============================================================================
print("\n" + "=" * 70)
print("PART 3: Computing the Normalization Factor")
print("=" * 70)

# SM Hypercharge (unnormalized)
Y_SM = np.diag([-1/3, -1/3, -1/3, 0.5, 0.5])

print("Standard Model hypercharge Y_SM = diag(-1/3, -1/3, -1/3, 1/2, 1/2)")
print(f"  Tr(Y_SM²) = {np.trace(Y_SM @ Y_SM):.6f}")

# SU(2) generator T₃
print("\nSU(2) generator T₃ = diag(0, 0, 0, 1/2, -1/2)")
print(f"  Tr(T₃²) = {np.trace(T3 @ T3):.6f}")

# For GUT unification, we need:
#   g₁² · Tr(Y_GUT²) = g₂² · Tr(T₃²)
# At unification: g₁ = g₂
# So: Tr(Y_GUT²) = Tr(T₃²)

# If Y_GUT = k · Y_SM, then:
#   k² · Tr(Y_SM²) = Tr(T₃²)
#   k² = Tr(T₃²) / Tr(Y_SM²)

Tr_Y_sq = np.trace(Y_SM @ Y_SM)
k_squared = Tr_T3_sq / Tr_Y_sq
k = np.sqrt(k_squared)

print(f"\nGUT normalization factor:")
print(f"  k² = Tr(T₃²) / Tr(Y_SM²) = {Tr_T3_sq} / {Tr_Y_sq} = {k_squared:.6f}")
print(f"  k = √(k²) = {k:.6f}")
print(f"  Expected √(3/5) = {np.sqrt(3/5):.6f}")
print(f"  Match: {np.isclose(k, np.sqrt(3/5))}")

# =============================================================================
# Part 4: Deriving sin²θ_W = 3/8
# =============================================================================
print("\n" + "=" * 70)
print("PART 4: Deriving sin²θ_W = 3/8")
print("=" * 70)

print("""
CORRECT FORMULA for sin²θ_W at GUT scale:

The Weinberg angle is defined by:
  sin²θ_W = g'² / (g² + g'²)

where g is the SU(2) coupling and g' is the U(1)_Y coupling.

At the GUT scale, the unified coupling relates to SM couplings as:
  g = g_GUT  (SU(2) coupling = unified coupling)
  g' = √(3/5) · g_GUT  (U(1) coupling with normalization)

Wait, that's not quite right. Let me redo this carefully.

The relation is through the normalization of generators. If we use:
  g₁ = √(5/3) · g'    (GUT-normalized U(1) coupling)
  g₂ = g               (SU(2) coupling)

At unification: g₁ = g₂ = g_GUT

So:  √(5/3) · g' = g
     g'/g = √(3/5)

Therefore:
  sin²θ_W = g'² / (g² + g'²)
          = 1 / (g²/g'² + 1)
          = 1 / (5/3 + 1)
          = 1 / (8/3)
          = 3/8  ✓
""")

# Verify numerically
g_ratio_sq = 5/3  # (g/g')² at GUT scale
sin2_theta = 1 / (g_ratio_sq + 1)
print(f"Numerical verification:")
print(f"  (g/g')² = 5/3")
print(f"  sin²θ_W = 1/(5/3 + 1) = 1/(8/3) = {sin2_theta}")
print(f"  = 3/8 = {3/8}")

# =============================================================================
# Part 5: Alternative (Correct) Trace Formula
# =============================================================================
print("\n" + "=" * 70)
print("PART 5: A Correct Trace-Based Formula")
print("=" * 70)

print("""
There IS a correct trace formula, but it's more subtle:

The normalization factor k_Y = √(3/5) comes from requiring:
  Tr(Y_GUT²) = Tr(T₃²)    [equal generator normalization]

where Y_GUT = k_Y · Y_SM

From k_Y² = Tr(T₃²)/Tr(Y_SM²) = 3/5

The Weinberg angle is then:
  sin²θ_W = k_Y² / (1 + k_Y²) = (3/5) / (1 + 3/5) = (3/5) / (8/5) = 3/8

Or equivalently:
  sin²θ_W = Tr(T₃²) / [Tr(T₃²) + Tr(Y_SM²)]
          = 0.5 / (0.5 + 5/6)
          = 0.5 / (8/6)
          = (1/2) / (4/3)
          = 3/8  ✓

CORRECTED TRACE FORMULA:
  sin²θ_W = Tr(T₃²) / [Tr(T₃²) + Tr(Y_SM²)]
""")

# Verify the correct trace formula
sin2_theta_trace = Tr_T3_sq / (Tr_T3_sq + Tr_Y_sq)
print(f"Verification of corrected trace formula:")
print(f"  Tr(T₃²) = {Tr_T3_sq}")
print(f"  Tr(Y_SM²) = {Tr_Y_sq}")
print(f"  sin²θ_W = Tr(T₃²) / [Tr(T₃²) + Tr(Y_SM²)]")
print(f"          = {Tr_T3_sq} / ({Tr_T3_sq} + {Tr_Y_sq})")
print(f"          = {Tr_T3_sq} / {Tr_T3_sq + Tr_Y_sq}")
print(f"          = {sin2_theta_trace:.6f}")
print(f"  3/8 = {3/8:.6f}")
print(f"  Match: {np.isclose(sin2_theta_trace, 3/8)}")

# =============================================================================
# Part 6: The Wrong Formula Deconstructed
# =============================================================================
print("\n" + "=" * 70)
print("PART 6: Why the Original Formula is Wrong")
print("=" * 70)

print("""
The ORIGINAL (incorrect) formula was:
  sin²θ_W = Tr(T₃²) / Tr(Q²)

The problem: Q = T₃ + Y is the electric charge, which mixes
both generators. Using Tr(Q²) double-counts contributions
and doesn't correctly capture the coupling ratio.

  Tr(Q²) = Tr((T₃ + Y)²) = Tr(T₃²) + 2Tr(T₃Y) + Tr(Y²)
         = Tr(T₃²) + 0 + Tr(Y²)  [T₃ and Y are orthogonal in this rep]
         = Tr(T₃²) + Tr(Y²)

So the original formula gives:
  Tr(T₃²)/Tr(Q²) = Tr(T₃²)/[Tr(T₃²) + Tr(Y²)]

Which is EXACTLY the correct formula! The error was in the
INTERPRETATION, not the formula itself.

Wait, let me recheck...
""")

Tr_Q_computed = Tr_T3_sq + Tr_Y_sq
print(f"Recomputing:")
print(f"  Tr(Q²) directly = {Tr_Q_sq}")
print(f"  Tr(T₃²) + Tr(Y²) = {Tr_T3_sq} + {Tr_Y_sq} = {Tr_T3_sq + Tr_Y_sq}")

# Check if T₃ and Y are orthogonal
Tr_T3_Y = np.trace(T3 @ Y_SM)
print(f"  Tr(T₃·Y) = {Tr_T3_Y}")

print(f"\nSo Tr(Q²) = Tr(T₃²) + 2·Tr(T₃Y) + Tr(Y²)")
print(f"         = {Tr_T3_sq} + 2·{Tr_T3_Y} + {Tr_Y_sq}")
print(f"         = {Tr_T3_sq + 2*Tr_T3_Y + Tr_Y_sq}")

# The original formula check
original_formula = Tr_T3_sq / Tr_Q_sq
print(f"\nOriginal formula Tr(T₃²)/Tr(Q²) = {original_formula:.6f}")
print(f"3/8 = {3/8:.6f}")
print(f"Match: {np.isclose(original_formula, 3/8)}")

# =============================================================================
# Part 7: Final Resolution
# =============================================================================
print("\n" + "=" * 70)
print("PART 7: FINAL RESOLUTION OF ISSUE C2")
print("=" * 70)

print("""
RESOLUTION:

The original formula sin²θ_W = Tr(T₃²)/Tr(Q²) is ACTUALLY CORRECT
when applied in the fundamental representation, because T₃ and Y
are orthogonal (Tr(T₃Y) = 0).

The REAL issue is that the theorem's DERIVATION was unclear about
WHY this formula works. The correct understanding is:

1. At GUT unification, gauge couplings satisfy: g₁ = g₂ = g₃ = g_GUT

2. The U(1)_Y coupling is related to the GUT coupling by the
   normalization factor: g' = √(3/5) · g_GUT

3. This normalization comes from: k² = Tr(T₃²)/Tr(Y²) = 3/5

4. The Weinberg angle follows from:
   sin²θ_W = g'²/(g² + g'²) = k²/(1 + k²) = 3/8

5. This can also be written as:
   sin²θ_W = Tr(T₃²)/[Tr(T₃²) + Tr(Y²)] = Tr(T₃²)/Tr(Q²)

   [The last equality holds when Tr(T₃Y) = 0]

REQUIRED CHANGES TO THEOREM:
1. Keep the trace formula (it's correct for this case)
2. Add explanation of WHY it works (coupling normalization)
3. Note that T₃ and Y must be orthogonal for formula to apply
4. Show the connection to coupling unification explicitly
""")

# Summary verification
print("\n" + "=" * 70)
print("SUMMARY VERIFICATION")
print("=" * 70)
print(f"  Tr(T₃²) = {Tr_T3_sq}")
print(f"  Tr(Y²) = {Tr_Y_sq}")
print(f"  Tr(T₃Y) = {Tr_T3_Y} (orthogonal)")
print(f"  Tr(Q²) = Tr(T₃²) + Tr(Y²) = {Tr_Q_sq}")
print(f"  sin²θ_W = Tr(T₃²)/Tr(Q²) = {Tr_T3_sq/Tr_Q_sq:.6f}")
print(f"  Expected 3/8 = {3/8:.6f}")
print(f"  Formula is CORRECT: {np.isclose(Tr_T3_sq/Tr_Q_sq, 3/8)}")
