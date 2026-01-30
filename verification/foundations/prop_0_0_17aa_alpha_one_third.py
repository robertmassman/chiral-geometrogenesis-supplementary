#!/usr/bin/env python3
"""
Direction D: Connection to α = 1/3 — Canonical Normalization Investigation

This script investigates whether the 4/π factor arises from the canonical
normalization conventions in α-attractor inflation with α = 1/3.

Key Issue from Resolution Plan:
The relation N = (3α)/(4ε) with ε = 1/(2N) gives N = N/2, which fails!
This suggests normalization conventions need careful checking.

Research Questions:
1. What is the exact relationship between α = 1/3 and the SU(3) coset?
2. How does the canonical normalization work for SU(3)/U(1)²?
3. Does the factor 4/π emerge from the canonical normalization?
4. Where does the factor of 2 discrepancy come from?

Background:
- SU(3) has dim = 8 generators
- The coset SU(3)/U(1)² has dim = 6 (3 complex dimensions)
- For α-attractors: α = dim_C(coset)/3 = 1/3 for SU(3)/U(1)²
- The Kähler potential is K = -3α ln(1 - |z|²) = -ln(1 - |z|²) for α = 1/3

Author: Research investigation for Prop 0.0.17aa
Date: 2026-01-26
"""

import numpy as np
from scipy import integrate
from scipy.optimize import brentq
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# Constants
# =============================================================================
N_c = 3  # Number of colors
N_f = 3  # Number of flavors (topological)
b_0 = (11 * N_c - 2 * N_f) / (12 * np.pi)  # = 9/(4π)

# Target values
ln_xi = 128 * np.pi / 9
N_geo_target = 512 / 9
four_over_pi = 4 / np.pi
n_s_target = 1 - 2 / N_geo_target

print("=" * 75)
print("DIRECTION D: Connection to α = 1/3 — Canonical Normalization")
print("=" * 75)

print(f"\nTarget values:")
print(f"  N_c = {N_c}")
print(f"  b₀ = 9/(4π) = {b_0:.6f}")
print(f"  ln(ξ) = 128π/9 = {ln_xi:.6f}")
print(f"  N_geo = 512/9 = {N_geo_target:.6f}")
print(f"  4/π = {four_over_pi:.6f}")
print(f"  n_s = 1 - 2/N_geo = {n_s_target:.6f}")

# =============================================================================
# Section 1: Why α = 1/3 for SU(3)?
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 1: Why α = 1/3 for SU(3)?")
print("=" * 75)

print("""
The α-attractor parameter is determined by the target space geometry:

For a coset space G/H, the α parameter is given by:
  α = (1/3) × dim_C(G/H)

For SU(3)/U(1)² (the flag manifold F₃):
  - dim_R(SU(3)) = 8
  - dim_R(U(1)²) = 2
  - dim_R(F₃) = 8 - 2 = 6
  - dim_C(F₃) = 3

Therefore:
  α = (1/3) × 3 = 1 (WRONG!)

Wait, this gives α = 1, not α = 1/3. Let me reconsider.

CORRECTION: The formula depends on the embedding:
  - For a single complex field: α = 1 (SU(2)/U(1) ~ CP¹)
  - For α-attractors with SU(N_c) embedding: α = 1/(N_c - 1)

For SU(3): α = 1/(3-1) = 1/2 (STILL WRONG!)

Let me look at the literature conventions more carefully.
""")

# Different conventions in the literature
print("\nDifferent conventions for α:")
print("-" * 50)

# Convention 1: Kallosh-Linde standard
print("\nConvention 1 (Kallosh-Linde 2013):")
print("  K = -3α ln(1 - |z|²/v²)")
print("  For conformal attractors: α = 1")
print("  For α = 1/3: K = -ln(1 - |z|²)")

# Convention 2: From SU(N) embedding
print("\nConvention 2 (SU(N) Kähler embedding):")
print("  For SU(N)/SU(N-1)×U(1) ~ CP^{N-1}:")
print("  The natural Kähler potential has α = 1/(N-1)")
print("  For N = 3: α = 1/2")

# Convention 3: From dimensional analysis
print("\nConvention 3 (Dimensional counting):")
print("  For coset G/H with dim_C = n:")
print("  The effective single-field α = 1/n")
print("  For dim_C = 3: α = 1/3")

# =============================================================================
# Section 2: The Self-Consistency Check
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 2: The Self-Consistency Check")
print("=" * 75)

print("""
The Resolution Plan notes a factor of 2 discrepancy:

From slow-roll:
  ε = 1/(2N)  (leading-order for large N)

From the α-attractor potential V = V₀ tanh²(φ/√(6α)):
  ε = (1/2)(V'/V)² = (2/(3α)) × sech⁴(φ/√(6α)) / tanh²(φ/√(6α))

At large φ (where tanh → 1, sech → 0):
  ε ≈ (2/(3α)) × 4 exp(-4φ/√(6α))

The e-fold formula:
  N = (3α/4ε) [at large N approximation]

If ε = 1/(2N), then:
  N = (3α/4) × 2N = (3α/2) × N

For α = 1/3:
  N = (3 × 1/3 / 2) × N = N/2  ← INCONSISTENT!

The factor of 2 comes from somewhere.
""")

# Let's derive this more carefully
alpha = 1/3
print(f"\nα = {alpha}")
print(f"3α = {3 * alpha}")
print(f"6α = {6 * alpha}")
print(f"3α/2 = {3 * alpha / 2}")

# =============================================================================
# Section 3: Careful Derivation of Slow-Roll Formulas
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 3: Careful Derivation of Slow-Roll Formulas")
print("=" * 75)

print("""
Let's be very careful with the α-attractor formulas.

The Kähler potential (disk coordinates):
  K = -3α ln(1 - |z|²)

The kinetic term (setting M_P = 1):
  L_kin = K_{z̄z} |∂z|² = (3α / (1 - |z|²)²) |∂z|²

The canonical field φ satisfies:
  (1/2)(∂φ)² = (3α / (1 - |z|²)²) |∂z|²

For radial z = r (real):
  (dφ/dr)² = 6α / (1 - r²)²
  dφ/dr = √(6α) / (1 - r²)

Integrating:
  φ = √(6α) × arctanh(r)
  r = tanh(φ/√(6α))

For α = 1/3:
  φ = √2 × arctanh(r)
  r = tanh(φ/√2)
""")

# Verify the kinetic term normalization
sqrt_6alpha = np.sqrt(6 * alpha)
print(f"\n√(6α) = √(6 × 1/3) = √2 = {sqrt_6alpha:.6f}")

# =============================================================================
# Section 4: The Inflationary Potential
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 4: The Inflationary Potential")
print("=" * 75)

print("""
For α-attractors, the scalar potential in disk coordinates is:

  V(z) = V₀ × f(|z|²)

The standard T-model potential in canonical coordinates:
  V(φ) = V₀ × tanh²ⁿ(φ/√(6α))

For n = 1 (quadratic):
  V(φ) = V₀ × tanh²(φ/√(6α))

The E-model potential:
  V(φ) = V₀ × [1 - exp(-√(2/3α) × φ)]²

Let's compute ε and N for each model.
""")

# T-model with n=1
def T_model_potential(phi, alpha=1/3, V0=1):
    """T-model potential V = V₀ tanh²(φ/√(6α))"""
    return V0 * np.tanh(phi / np.sqrt(6 * alpha))**2

def T_model_epsilon(phi, alpha=1/3):
    """Slow-roll parameter ε for T-model."""
    x = phi / np.sqrt(6 * alpha)
    # V = V₀ tanh²(x)
    # V' = V₀ × 2 tanh(x) sech²(x) / √(6α)
    # ε = (1/2)(V'/V)² = (1/2)(2 sech²(x) / (tanh(x) √(6α)))²
    #   = 2 sech⁴(x) / (3α tanh²(x))
    if abs(np.tanh(x)) < 1e-10:
        return float('inf')
    eps = 2 * (1 / np.cosh(x))**4 / (3 * alpha * np.tanh(x)**2)
    return eps

def T_model_N(phi_star, phi_end, alpha=1/3):
    """E-folds from slow-roll integration for T-model."""
    def integrand(phi):
        eps = T_model_epsilon(phi, alpha)
        if eps < 1e-10:
            return 0
        return 1 / np.sqrt(2 * eps)
    result, _ = integrate.quad(integrand, phi_end, phi_star)
    return result

# E-model
def E_model_potential(phi, alpha=1/3, V0=1):
    """E-model potential V = V₀ [1 - exp(-√(2/(3α)) φ)]²"""
    return V0 * (1 - np.exp(-np.sqrt(2 / (3 * alpha)) * phi))**2

def E_model_epsilon(phi, alpha=1/3):
    """Slow-roll parameter ε for E-model."""
    # V = V₀ [1 - e^(-cx)]² where c = √(2/(3α))
    # V' = V₀ × 2[1 - e^(-cx)] × c e^(-cx)
    # ε = (1/2)(V'/V)² = (1/2)(2c e^(-cx) / [1 - e^(-cx)])²
    c = np.sqrt(2 / (3 * alpha))
    exp_term = np.exp(-c * phi)
    if abs(1 - exp_term) < 1e-10:
        return float('inf')
    eps = 0.5 * (2 * c * exp_term / (1 - exp_term))**2
    return eps

print("\nComparing T-model and E-model:")
print("-" * 70)
print(f"{'φ/M_P':<10} {'ε(T-model)':<15} {'ε(E-model)':<15} {'N ≈ 1/(2ε)':<15}")
print("-" * 70)

for phi in [2, 3, 4, 5, 6]:
    eps_T = T_model_epsilon(phi)
    eps_E = E_model_epsilon(phi)
    N_approx = 0.5 / eps_T if eps_T > 0 else float('inf')
    print(f"{phi:<10} {eps_T:<15.6f} {eps_E:<15.6f} {N_approx:<15.1f}")

# =============================================================================
# Section 5: Exact E-fold Formulas
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 5: Exact E-fold Formulas")
print("=" * 75)

print("""
For the T-model with α = 1/3, the exact e-fold formula is:

  N = (3α/4) × [cosh(2φ_*/√(6α)) - cosh(2φ_end/√(6α))]

In the large φ_* limit:
  N ≈ (3α/8) × exp(2φ_*/√(6α))

Alternatively, using sinh:
  N = (3α/4) × sinh²(φ_*/√(6α)) - (3α/4) × sinh²(φ_end/√(6α))

For large N (and small φ_end contribution):
  N ≈ (3α/2) × sinh²(φ_*/√(6α))

Wait - there's a factor of 2 difference between these formulas!
Let me check more carefully.
""")

# Exact formula using sinh²
def exact_N_sinh(phi_star, phi_end=0.5, alpha=1/3):
    """Exact e-folds using sinh² formula."""
    x_star = phi_star / np.sqrt(6 * alpha)
    x_end = phi_end / np.sqrt(6 * alpha)
    return (3 * alpha / 2) * (np.sinh(x_star)**2 - np.sinh(x_end)**2)

# Exact formula using cosh
def exact_N_cosh(phi_star, phi_end=0.5, alpha=1/3):
    """Exact e-folds using cosh formula."""
    x_star = phi_star / np.sqrt(6 * alpha)
    x_end = phi_end / np.sqrt(6 * alpha)
    return (3 * alpha / 4) * (np.cosh(2 * x_star) - np.cosh(2 * x_end))

# Compare the formulas
print("\nComparing e-fold formulas:")
print("-" * 70)
print(f"{'φ_*/M_P':<10} {'N (sinh² form)':<18} {'N (cosh form)':<18} {'Ratio':<10}")
print("-" * 70)

phi_end = 0.5  # Inflation end
for phi_star in [3, 4, 5, 6]:
    N_sinh = exact_N_sinh(phi_star, phi_end)
    N_cosh = exact_N_cosh(phi_star, phi_end)
    ratio = N_cosh / N_sinh if N_sinh > 0 else float('nan')
    print(f"{phi_star:<10} {N_sinh:<18.4f} {N_cosh:<18.4f} {ratio:<10.4f}")

# =============================================================================
# Section 6: Identity Between sinh² and cosh
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 6: Resolving the sinh² vs cosh Formula")
print("=" * 75)

print("""
The identity: cosh(2x) = 2sinh²(x) + 1 = 2cosh²(x) - 1

So:
  (3α/4)[cosh(2x_*) - cosh(2x_end)]
    = (3α/4)[2sinh²(x_*) + 1 - 2sinh²(x_end) - 1]
    = (3α/2)[sinh²(x_*) - sinh²(x_end)]

The two formulas are IDENTICAL! The apparent factor of 2 was because
I was comparing (3α/4)cosh to (3α/2)sinh² without accounting for the
identity cosh(2x) = 2sinh²(x) + 1.

CORRECT FORMULA:
  N = (3α/2) × sinh²(φ_*/√(6α))  [for large N, neglecting φ_end term]

For α = 1/3:
  N = (1/2) × sinh²(φ_*/√2)
""")

# Verify the identity
print("\nVerifying cosh(2x) = 2sinh²(x) + 1:")
for x in [1, 2, 3]:
    cosh_2x = np.cosh(2 * x)
    sinh_sq = 2 * np.sinh(x)**2 + 1
    print(f"x = {x}: cosh(2x) = {cosh_2x:.6f}, 2sinh²(x) + 1 = {sinh_sq:.6f}")

# =============================================================================
# Section 7: The Self-Consistency Issue Revisited
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 7: The Self-Consistency Issue Revisited")
print("=" * 75)

print("""
The Resolution Plan stated:
  N = (3α)/(4ε) = (3 × 1/3)/(4 × 1/(2N)) = N/2  (FAILS!)

But this formula is WRONG. The correct relation is:

From ε = 1/(2N) and the definition ε = (1/2)(V'/V)²:
  N = ∫ V/(V' M_P²) dφ = ∫ 1/(M_P √(2ε)) dφ

This is NOT the same as N = (3α)/(4ε).

The formula N = (3α)/(4ε) comes from:
  ε = (1/2)(V'/V)² ≈ (2/(3α)) × [something depending on φ]

Let's compute the correct relation between ε and N.
""")

# The correct relation
print("\nCorrect relation between ε and N:")
print("-" * 50)

# At horizon exit, we have:
# ε_* = 1/(2N) (leading order)
# This comes from n_s = 1 - 2/N, and n_s ≈ 1 - 6ε + 2η ≈ 1 - 2ε for single-field
# So 2/N ≈ 2ε, giving ε ≈ 1/N... but that contradicts ε = 1/(2N)!

print("""
Actually, for α-attractors:
  n_s = 1 - 2/N  (exact to leading order)

The slow-roll parameters for T-model (large N limit):
  ε ≈ (4/3) / (αN²)  ← NOT ε = 1/(2N)!
  η ≈ -2/(3αN)

With the standard formula n_s = 1 - 6ε + 2η:
  n_s ≈ 1 - 8/(αN²) - 4/(3αN)

For large N, the dominant term is the η term:
  n_s ≈ 1 - 4/(3αN)

For α = 1/3:
  n_s ≈ 1 - 4/N

But wait, this gives n_s = 1 - 4/N, not n_s = 1 - 2/N!

Let me recalculate more carefully.
""")

# =============================================================================
# Section 8: Careful Computation of Slow-Roll Parameters
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 8: Careful Computation of Slow-Roll Parameters")
print("=" * 75)

def compute_slow_roll(phi, alpha=1/3):
    """Compute ε, η, and N for T-model α-attractor."""
    x = phi / np.sqrt(6 * alpha)
    tanh_x = np.tanh(x)
    sech_x = 1 / np.cosh(x)

    # V = V₀ tanh²(x)
    # V' = (V₀/√(6α)) × 2 tanh(x) sech²(x)
    # V'' = (V₀/(6α)) × 2 sech²(x) × [sech²(x) - 2tanh²(x)]

    if abs(tanh_x) < 1e-10:
        return float('inf'), float('nan'), 0

    # ε = (1/2)(V'/V)² = (1/2) × [2 sech²(x) / (√(6α) tanh(x))]²
    #   = 2 sech⁴(x) / (6α tanh²(x))
    #   = sech⁴(x) / (3α tanh²(x))
    epsilon = sech_x**4 / (3 * alpha * tanh_x**2)

    # η = V''/(V) = [2 sech²(x)(sech²(x) - 2tanh²(x))] / [6α tanh²(x)]
    #   = [sech⁴(x) - 2sech²(x)tanh²(x)] / [3α tanh²(x)]
    eta = (sech_x**4 - 2 * sech_x**2 * tanh_x**2) / (3 * alpha * tanh_x**2)

    # N (from origin) using sinh² formula
    N = (3 * alpha / 2) * np.sinh(x)**2

    return epsilon, eta, N

print("\nSlow-roll parameters for T-model with α = 1/3:")
print("-" * 80)
print(f"{'φ/M_P':<8} {'x=φ/√2':<10} {'ε':<12} {'η':<12} {'N':<12} {'1/(2N)':<12} {'n_s':<10}")
print("-" * 80)

for phi in np.linspace(2, 6, 9):
    epsilon, eta, N = compute_slow_roll(phi)
    one_over_2N = 1 / (2 * N) if N > 0 else float('nan')
    n_s = 1 - 6 * epsilon + 2 * eta if eta != float('nan') else float('nan')
    x = phi / np.sqrt(2)
    print(f"{phi:<8.2f} {x:<10.4f} {epsilon:<12.6f} {eta:<12.6f} {N:<12.2f} {one_over_2N:<12.6f} {n_s:<10.6f}")

# =============================================================================
# Section 9: The n_s = 1 - 2/N Formula
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 9: Deriving n_s = 1 - 2/N")
print("=" * 75)

print("""
For α-attractors, the spectral index n_s = 1 - 6ε + 2η has special behavior.

At large N:
  sinh(x) ≈ (1/2)exp(x) for x >> 1
  tanh(x) ≈ 1 - 2exp(-2x)
  sech(x) ≈ 2exp(-x)

From N = (3α/2)sinh²(x):
  sinh(x) = √(2N/(3α))
  For large N: exp(x) ≈ 2√(2N/(3α))

Then:
  sech(x) ≈ √(3α/(2N))
  tanh(x) ≈ 1

So:
  ε ≈ sech⁴(x) / (3α) = (3α/(2N))² / (3α) = 3α/(4N²)

For α = 1/3:
  ε ≈ 1/(4N²)

This is MUCH smaller than 1/(2N) for large N!

The η term:
  η ≈ sech⁴(x) / (3α) - 2sech²(x) / (3α)
    ≈ -2sech²(x) / (3α)  [dominant term]
    ≈ -2/(3α) × (3α/(2N))
    = -1/N

So:
  n_s = 1 - 6ε + 2η ≈ 1 - 6/(4N²) - 2/N ≈ 1 - 2/N  [for large N]

The n_s = 1 - 2/N formula comes from the η term dominating!
""")

# Verify numerically
print("\nNumerical verification:")
print("-" * 60)
print(f"{'N':<12} {'6ε':<12} {'2η':<12} {'n_s calc':<12} {'1-2/N':<12}")
print("-" * 60)

for N_target in [50, 60, 70, 100]:
    # Find φ that gives this N
    def N_residual(phi):
        _, _, N = compute_slow_roll(phi)
        return N - N_target

    phi_val = brentq(N_residual, 2, 8)
    epsilon, eta, N = compute_slow_roll(phi_val)
    n_s_calc = 1 - 6 * epsilon + 2 * eta
    n_s_approx = 1 - 2 / N
    print(f"{N:<12.2f} {6*epsilon:<12.6f} {2*eta:<12.6f} {n_s_calc:<12.6f} {n_s_approx:<12.6f}")

# =============================================================================
# Section 10: Where Does 4/π Enter?
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 10: Where Does 4/π Enter?")
print("=" * 75)

print("""
Now we understand the slow-roll mechanics. The question is:
How does 4/π enter the relation N = (4/π) × ln(ξ)?

The connection must come from:
1. The bootstrap gives ln(ξ) = 128π/9 (from QCD + topological data)
2. This determines the INITIAL CONDITIONS for inflation
3. Specifically, it determines φ_* (the field value at horizon exit)

The 4/π factor converts between:
  - ln(ξ): dimensionless information from QCD
  - N: number of e-folds from inflationary geometry

The key relation:
  N = (3α/2) × sinh²(φ_*/√(6α))

If N = (4/π) × ln(ξ), then:
  sinh²(φ_*/√(6α)) = (2/(3α)) × (4/π) × ln(ξ)
                   = (8/(3απ)) × ln(ξ)

For α = 1/3:
  sinh²(φ_*/√2) = (8/π) × ln(ξ) = (8/π) × (128π/9) = 1024/9

So:
  sinh(φ_*/√2) = 32/3
  φ_*/√2 = arcsinh(32/3) ≈ 3.367
  φ_* ≈ 4.76 M_P
""")

# Calculate the field value
sinh_target = np.sqrt(1024/9)
phi_star_over_sqrt2 = np.arcsinh(sinh_target)
phi_star = np.sqrt(2) * phi_star_over_sqrt2

print(f"\nCalculated field value at horizon exit:")
print(f"  sinh(φ_*/√2) = 32/3 = {sinh_target:.6f}")
print(f"  φ_*/√2 = arcsinh(32/3) = {phi_star_over_sqrt2:.6f}")
print(f"  φ_* = {phi_star:.6f} M_P")

# Verify
epsilon, eta, N = compute_slow_roll(phi_star)
n_s_calc = 1 - 6 * epsilon + 2 * eta
print(f"\nVerification:")
print(f"  N = {N:.6f}")
print(f"  Target N_geo = {N_geo_target:.6f}")
print(f"  n_s = {n_s_calc:.6f}")
print(f"  Target n_s = {n_s_target:.6f}")

# =============================================================================
# Section 11: The Factor 4/π = (N_c² - 1)/(2π)
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 11: The Factor 4/π = (N_c² - 1)/(2π)")
print("=" * 75)

print("""
We have established:
  N_geo = (4/π) × ln(ξ)

where 4/π = (N_c² - 1)/(2π) = 8/(2π) for N_c = 3.

This identity is EXACT for N_c = 3 only because:
  N_c² - 1 = 8 = 2 × 4

For other values of N_c:
  N_c = 2: (N_c² - 1)/(2π) = 3/(2π) ≈ 0.477 ≠ 4/π
  N_c = 4: (N_c² - 1)/(2π) = 15/(2π) ≈ 2.387 ≠ 4/π

So the identity 4/π = dim(SU(3))/(2π) is a COINCIDENCE specific to SU(3).

The question remains: Why does the conversion factor equal dim(SU(3))/(2π)?
""")

# Show for different N_c
print("\nConversion factors for different N_c:")
print("-" * 50)
for N_c_test in [2, 3, 4, 5]:
    factor = (N_c_test**2 - 1) / (2 * np.pi)
    print(f"N_c = {N_c_test}: (N_c² - 1)/(2π) = {N_c_test**2 - 1}/(2π) = {factor:.6f}")

print(f"\n4/π = {four_over_pi:.6f}")

# =============================================================================
# Section 12: Connection to α = 1/3
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 12: Connection to α = 1/3")
print("=" * 75)

print("""
For the SU(3) coset, we have α = 1/3.

The e-fold formula with α = 1/3:
  N = (3α/2) × sinh²(φ/√(6α)) = (1/2) × sinh²(φ/√2)

The prefactor (3α/2) = 1/2 for α = 1/3.

The canonical field normalization √(6α) = √2 for α = 1/3.

Is there a connection between α = 1/3 and 4/π?

Let's check various combinations:
""")

# Check combinations
print("\nPotential connections:")
print(f"  α = 1/3 = 0.333...")
print(f"  4/π = {four_over_pi:.6f}")
print(f"  3α = {3 * alpha:.6f}")
print(f"  6α = {6 * alpha:.6f}")
print(f"  1/α = {1/alpha:.6f}")
print(f"  π/α = {np.pi/alpha:.6f}")
print(f"  4/(3α) = {4/(3*alpha):.6f}")
print(f"  (4/π) × α = {four_over_pi * alpha:.6f}")
print(f"  (4/π) / α = {four_over_pi / alpha:.6f}")
print(f"  √(4/π) = {np.sqrt(four_over_pi):.6f}")
print(f"  √(6α) × (4/π) = {np.sqrt(6*alpha) * four_over_pi:.6f}")

# Is there a relation?
print(f"\n12/π = {12/np.pi:.6f}")
print(f"(4/π) / α = 12/π = {(4/np.pi)/alpha:.6f}")

# =============================================================================
# Section 13: The Key Observation - 12/π
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 13: The Key Observation - 12/π")
print("=" * 75)

print("""
Notice that:
  (4/π) / α = (4/π) / (1/3) = 12/π

And from the e-fold formula:
  N = (1/2) sinh²(φ/√2) = (3α/2) sinh²(φ/√(6α))

The connection:
  sinh²(φ/√2) = 2N = (8/π) × ln(ξ)

The factor 8/π = 2 × (4/π) enters through:
  - Factor 2: from N = (1/2) sinh² ↔ sinh² = 2N
  - Factor 4/π: the conversion from ln(ξ) to N

Can we express 8/π in terms of α?
  8/π = (4/π) × 2 = (4/π) × (1/3α) × (2/3) × 3

Hmm, this is getting complicated. Let's try another approach.
""")

# =============================================================================
# Section 14: Dimensional Analysis Approach
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 14: Dimensional Analysis Approach")
print("=" * 75)

print("""
Let's use dimensional analysis to understand the structure.

Inputs:
  - N_c = 3 (dimensionless)
  - α = 1/3 (dimensionless)
  - π (dimensionless)

From SU(3): dim(SU(3)) = N_c² - 1 = 8

The coset SU(3)/U(1)² has:
  - Real dimension: 6
  - Complex dimension: 3
  - α = 1/3 (from complex dimension)

Natural combinations:
  - dim(SU(3)) = 8
  - dim_R(coset) = 6
  - dim_C(coset) = 3
  - 2π (angular period)

The factor 4/π = 8/(2π) = dim(SU(3))/(2π)

Alternatively:
  4/π = (2 × dim_C(coset))/(2π) = dim_C(coset)/π

This suggests:
  The 4/π factor counts the complex dimensions of the coset,
  normalized by the angular period π (not 2π).

INTERPRETATION:
  4/π = dim_C(SU(3)/U(1)²) / π = 3/π... wait, that's 0.955, not 1.273!

Let me reconsider.
""")

# Check the combination
print("\nDimensional combinations:")
print(f"  dim(SU(3)) = {N_c**2 - 1}")
print(f"  dim_R(coset) = 6")
print(f"  dim_C(coset) = 3")
print(f"  3/π = {3/np.pi:.6f}")
print(f"  6/π = {6/np.pi:.6f}")
print(f"  8/π = {8/np.pi:.6f}")
print(f"  8/(2π) = {8/(2*np.pi):.6f}")
print(f"  4/π = {4/np.pi:.6f}")

# The relation
print(f"\n8/(2π) = 4/π ✓")
print(f"dim(SU(3))/(2π) = 4/π ✓")

# =============================================================================
# Section 15: The Bootstrap-Inflation Connection
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 15: The Bootstrap-Inflation Connection")
print("=" * 75)

print("""
The complete chain of reasoning:

1. FROM QCD BOOTSTRAP:
   ln(ξ) = (N_c² - 1)² / (2b₀)
         = 64 / (9/(2π))
         = 128π/9

2. FROM α-ATTRACTOR INFLATION (α = 1/3):
   N = (1/2) sinh²(φ/√2)
   n_s = 1 - 2/N

3. THE CONNECTION:
   N_geo = (4/π) × ln(ξ) = (4/π) × (128π/9) = 512/9

4. THE PREDICTION:
   n_s = 1 - 2/N_geo = 1 - 18/512 = 247/256 ≈ 0.9648

WHY IS THE CONNECTION FACTOR 4/π?

The factor 4/π = (N_c² - 1)/(2π) converts between:
  - ln(ξ): "information" from the bootstrap (involving b₀ ∝ 1/π)
  - N: "e-folds" from inflation (involving hyperbolic volume ∝ π)

The π factors cancel in a specific way that leaves 4/π.

Specifically:
  N = (4/π) × ln(ξ)
    = (4/π) × (N_c² - 1)² × (4π/9) / 2
    = (4/π) × 64 × (4π/9) / 2
    = (4/π) × (128π/9)
    = 512/9

The π in ln(ξ) comes from b₀ = 9/(4π).
The 4/π conversion removes this π and introduces the factor 4.
""")

# =============================================================================
# Section 16: The Origin of 4
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 16: The Origin of 4")
print("=" * 75)

print("""
The factor 4/π has:
  - 4 in the numerator
  - π in the denominator

Where does the 4 come from?

Option 1: From (N_c² - 1)/2 = 8/2 = 4
  This is half the dimension of SU(3).

Option 2: From the slow-roll integration
  The integral ∫ V/V' dφ may produce factors of 4.

Option 3: From the kinetic term normalization
  The factor √(6α) = √2 for α = 1/3.
  (√2)² = 2, not 4.

Option 4: From the sinh² formula
  N = (1/2) sinh², so sinh² = 2N.
  8/π × ln(ξ) = 2 × (4/π) × ln(ξ) = 2 × N_geo...

  So 8/π = 2 × (4/π), and the 2 comes from the sinh² ↔ N relation.

  The 4 in 4/π must come from (N_c² - 1)/2 = 8/2 = 4.

CONCLUSION:
  4 = dim(SU(3)) / 2 = 8/2

The factor 4/π = dim(SU(3)) / (2 × 2π) where:
  - dim(SU(3)) = 8 is the gauge group dimension
  - 2 is from the sinh² = 2N relation
  - 2π is the angular period
""")

# =============================================================================
# Section 17: Final Synthesis
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 17: FINAL SYNTHESIS")
print("=" * 75)

print("""
DIRECTION D FINDINGS:

1. SELF-CONSISTENCY:
   The formula N = (3α)/(4ε) is NOT correct for comparing ε and N.
   The correct relation is n_s = 1 - 6ε + 2η ≈ 1 - 2/N,
   where the η term dominates.

2. CANONICAL NORMALIZATION:
   For α = 1/3:
   - Kähler potential: K = -ln(1 - |z|²)
   - Canonical field: φ = √2 arctanh(|z|)
   - E-folds: N = (1/2) sinh²(φ/√2)

3. THE 4/π FACTOR:
   The relation N = (4/π) × ln(ξ) gives:
   sinh²(φ_*/√2) = 2N = (8/π) × ln(ξ) = 1024/9

   The factor 4/π = 8/(2π) = dim(SU(3))/(2π) appears to be:
   - NUMERICALLY EXACT for N_c = 3
   - A COINCIDENCE that 8 = 2 × 4

4. CONNECTION TO α = 1/3:
   The value α = 1/3 determines the kinetic term normalization
   (√(6α) = √2), but this doesn't directly produce 4/π.

   The 4/π factor comes from matching the bootstrap ln(ξ)
   to the inflationary N, not from α = 1/3 per se.

STATUS: NOT A DERIVATION

While we understand the algebraic structure thoroughly, the origin of
4/π remains a numerical coincidence specific to SU(3).
""")

# =============================================================================
# Section 18: Numerical Summary
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 18: NUMERICAL SUMMARY")
print("=" * 75)

print(f"\nα-attractor parameters:")
print(f"  α = {alpha} = 1/3")
print(f"  √(6α) = √2 = {np.sqrt(6*alpha):.6f}")
print(f"  Prefactor: 3α/2 = 1/2")

print(f"\nBootstrap values:")
print(f"  N_c = {N_c}")
print(f"  b₀ = 9/(4π) = {b_0:.6f}")
print(f"  ln(ξ) = 128π/9 = {ln_xi:.6f}")

print(f"\nInflation values:")
print(f"  N_geo = 512/9 = {N_geo_target:.6f}")
print(f"  n_s = 247/256 = {n_s_target:.6f}")
print(f"  φ_*/M_P = {phi_star:.6f}")

print(f"\nConversion factor:")
print(f"  4/π = {four_over_pi:.6f}")
print(f"  = dim(SU(3))/(2π) = 8/(2π)")
print(f"  = (N_c² - 1)/(2π)")

print(f"\nKey relations:")
print(f"  N_geo = (4/π) × ln(ξ)")
print(f"  sinh²(φ_*/√2) = (8/π) × ln(ξ) = 1024/9")
print(f"  n_s = 1 - 2/N_geo = 1 - 18/512 = 247/256")

print("\n" + "=" * 75)
print("Script completed successfully")
print("=" * 75)
