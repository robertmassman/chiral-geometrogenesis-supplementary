#!/usr/bin/env python3
"""
E2 Fix: Dimensional Analysis of Chiral Charge Change

Issue: Lines 89-92 claim:
    ΔN_5 = ∫_V d³x v_χ² (∂_t θ_χ) dt = v_χ² · V · Δθ_χ / L

This has dimensional problems:
- ΔN_5 should be dimensionless (it's a number of fermions)
- But the RHS has dimensions [energy]² × [length]³ × [dimensionless] / [length]

This script derives the correct dimensional analysis.
"""

import numpy as np

print("=" * 70)
print("E2 FIX: DIMENSIONAL ANALYSIS OF CHIRAL CHARGE")
print("=" * 70)

# =============================================================================
# PART 1: The Axial Current and Its Dimensions
# =============================================================================

print("\n" + "=" * 60)
print("PART 1: Dimensions of the Axial Current")
print("=" * 60)

print("""
The axial current j_5^μ has dimensions:

    [j_5^μ] = [ψ̄ γ^μ γ_5 ψ] = [energy]³

In natural units (ℏ = c = 1):
    [energy] = [mass] = [length]⁻¹ = [time]⁻¹

So:
    [j_5^μ] = [energy]³ = [GeV]³

The divergence:
    [∂_μ j_5^μ] = [energy]⁴

The integrated charge:
    N_5 = ∫ d³x j_5^0
    [N_5] = [length]³ × [energy]³ = [energy]³ / [energy]³ = dimensionless ✓
""")

# =============================================================================
# PART 2: The Anomaly Equation
# =============================================================================

print("\n" + "=" * 60)
print("PART 2: Anomaly Equation Dimensions")
print("=" * 60)

print("""
The anomaly equation:
    ∂_μ j_5^μ = (g²/16π²) F_μν F̃^μν

Dimensions:
    LHS: [∂_μ j_5^μ] = [energy]⁴

    RHS: [g²/16π²] × [F_μν F̃^μν]
         = dimensionless × [energy]⁴
         = [energy]⁴ ✓

Integrated over spacetime:
    ΔN_5 = ∫ d⁴x ∂_μ j_5^μ = (g²/16π²) ∫ d⁴x F F̃

    [ΔN_5] = [length]⁴ × [energy]⁴ = [energy]⁴ / [energy]⁴ = dimensionless ✓

The topological charge Q = (1/32π²) ∫ d⁴x g² F F̃ is dimensionless.
""")

# =============================================================================
# PART 3: The Problem with Lines 89-92
# =============================================================================

print("\n" + "=" * 60)
print("PART 3: The Dimensional Problem")
print("=" * 60)

print("""
The text claims:
    j_5^μ[χ] = v_χ² ∂^μ θ_χ

where v_χ is the chiral VEV with [v_χ] = [energy].

Dimensions:
    [j_5^μ[χ]] = [v_χ²] × [∂^μ θ_χ]
                = [energy]² × [energy]
                = [energy]³ ✓ (This is correct!)

The problem is in the integration:
    ΔN_5 = ∫_V d³x v_χ² (∂_t θ_χ) dt

The text writes this as:
    ΔN_5 = v_χ² · V · Δθ_χ / L

where V is volume and L is length.

Dimensions:
    [v_χ² · V · Δθ_χ / L] = [energy]² × [length]³ × 1 / [length]
                          = [energy]² × [length]²
                          = [energy]² / [energy]²
                          = dimensionless ✓ (in natural units)

Wait - this IS dimensionally correct in natural units!
Let me recheck...

In natural units where [length] = [energy]⁻¹:
    [V] = [length]³ = [energy]⁻³
    [L] = [length] = [energy]⁻¹

    [v_χ² · V / L] = [energy]² × [energy]⁻³ / [energy]⁻¹
                    = [energy]² × [energy]⁻³ × [energy]
                    = [energy]⁰ = dimensionless ✓

So the dimensional analysis IS correct in natural units!
""")

# =============================================================================
# PART 4: The Real Issue - Physical Interpretation
# =============================================================================

print("\n" + "=" * 60)
print("PART 4: The Physical Interpretation Issue")
print("=" * 60)

print("""
The issue is NOT dimensional but conceptual:

PROBLEM: The equation
    ΔN_5 = v_χ² · V · Δθ_χ / L

is confusing because:
1. It introduces an arbitrary length scale L
2. The relationship to the anomaly isn't clear
3. The reader doesn't understand where V and L come from

SOLUTION: Replace with the standard anomaly index theorem formulation:

The Atiyah-Singer index theorem relates:
    ΔN_5 = N_L - N_R = 2 × (Topological Charge)

where the topological charge is:
    Q = (g²/32π²) ∫ d⁴x F_μν F̃^μν

The key physical insight is that:
- The SIGN of ΔN_5 depends on the sign of the integrated F F̃
- The χ field's phase gradient biases this integral

Rather than the confusing V·Δθ/L expression, we should write:

    sign(ΔN_5) = sign(∫ d⁴x ∂_t θ_χ) = sign(Δθ_χ)

where Δθ_χ is the total phase change over the cosmological history.
""")

# =============================================================================
# PART 5: Numerical Check
# =============================================================================

print("\n" + "=" * 60)
print("PART 5: Numerical Verification")
print("=" * 60)

# Physical constants
v_chi = 246  # GeV (Higgs/chiral VEV)
delta_theta = 2 * np.pi / 3  # Phase change per color cycle (radians)

# Cosmological scales (in GeV^-1)
# Hubble time at T ~ 160 GeV is about H^-1 ~ 10^-16 s ~ 10^8 GeV^-1
H_inv_GeV = 1e8  # GeV^-1 (characteristic time)

# Horizon volume at EWPT
L_horizon = H_inv_GeV  # GeV^-1
V_horizon = L_horizon**3  # GeV^-3

print(f"\nPhysical scales:")
print(f"  v_χ = {v_chi} GeV")
print(f"  Δθ_χ = 2π/3 ≈ {delta_theta:.4f} radians")
print(f"  Hubble time H⁻¹ ~ {H_inv_GeV:.0e} GeV⁻¹")
print(f"  Horizon volume V ~ {V_horizon:.0e} GeV⁻³")

# The integrated phase change rate
# ∂_t θ_χ ~ Δθ / (H^-1) ~ Δθ × H
# This has dimensions [energy] in natural units
partial_t_theta = delta_theta / H_inv_GeV  # GeV

print(f"\n∂_t θ_χ ~ Δθ/(H⁻¹) = {partial_t_theta:.2e} GeV")

# The axial charge density
# n_5 = v_χ² × ∂_t θ_χ
n_5 = v_chi**2 * partial_t_theta  # GeV^3

print(f"\nAxial charge density:")
print(f"  n_5 = v_χ² × ∂_t θ_χ = {n_5:.2e} GeV³")

# Total axial charge in horizon volume
N_5 = n_5 * V_horizon  # dimensionless

print(f"\nTotal axial charge in horizon:")
print(f"  N_5 = n_5 × V = {N_5:.2e}")
print(f"  (This is ~ 10^{np.log10(abs(N_5)):.0f})")

# =============================================================================
# PART 6: Proposed Corrected Text
# =============================================================================

print("\n" + "=" * 60)
print("PART 6: PROPOSED CORRECTED TEXT")
print("=" * 60)

print("""
REPLACE lines 85-94 with:

For the chiral current sourced by χ, we have:
$$j^\\mu_5[\\chi] = v_\\chi^2 \\partial^\\mu \\theta_\\chi$$

where $v_\\chi \\sim 246$ GeV is the chiral VEV and $\\theta_\\chi = \\arg(\\chi)$.

The total axial charge change is:
$$\\Delta N_5 = \\int d^4x \\, \\partial_\\mu j^\\mu_5 = \\int d^4x \\, v_\\chi^2 \\, \\partial_t^2 \\theta_\\chi + \\ldots$$

However, for understanding the **sign correlation**, we only need to note that:

1. The anomaly equation couples $\\partial_\\mu j^\\mu_5$ to both $G\\tilde{G}$ and $W\\tilde{W}$
2. The χ field has a definite phase gradient direction: either R→G→B ($\\Delta\\theta = +2\\pi/3$) or B→G→R ($\\Delta\\theta = -2\\pi/3$)
3. This **sign** propagates to both gauge sectors simultaneously

The magnitude of ΔN_5 involves cosmological details (Hubble rate, horizon volume), but the **sign** depends only on the chirality of χ:

$$\\text{sgn}(\\Delta N_5) = \\text{sgn}(\\Delta\\theta_\\chi)$$

This is the key insight: the sign of the total chiral charge change is determined by the geometric chirality of the χ field, independent of cosmological scales.
""")

print("\n" + "=" * 70)
print("E2 ANALYSIS COMPLETE")
print("=" * 70)

print("""
CONCLUSION: The dimensional analysis is actually CORRECT in natural units,
but the text is CONFUSING because:
1. It introduces arbitrary scales V and L without physical justification
2. It doesn't clearly explain the relationship to the anomaly
3. The reader doesn't understand why the sign is what matters

The fix should CLARIFY the physics rather than correct a math error.
""")
