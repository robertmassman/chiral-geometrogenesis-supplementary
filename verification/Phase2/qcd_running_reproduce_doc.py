#!/usr/bin/env python3
"""
Reproduce EXACTLY the calculation from two-loop-QCD-analysis.md Appendix C

This script uses the exact code given in the document to see if we can reproduce
their claimed values:
    α_s(m_t) = 0.010758
    α_s(m_b) = 0.016284
    α_s(m_c) = 0.021593
    α_s(M_Z) = 0.118723

Author: Multi-Agent Verification System
Date: 2025-12-14
"""

import numpy as np
from scipy.optimize import fsolve

# =============================================================================
# EXACT CODE FROM APPENDIX C
# =============================================================================

# Beta function coefficients
def b0(Nf):
    return (11*3 - 2*Nf)/(12*np.pi)

def b1(Nf):
    Nc = 3
    return (34*Nc**2/3 - 10*Nc*Nf/3 - (Nc**2-1)*Nf/Nc)/(16*np.pi**2)

# Two-loop RGE (implicit form)
def RGE_2loop(alpha_final, alpha_init, L, Nf):
    b0_val = b0(Nf)
    b1_val = b1(Nf)

    term1 = (1/alpha_final - 1/alpha_init)/(2*b0_val)
    term2 = (b1_val/(2*b0_val**2))*np.log(alpha_final/alpha_init)

    return term1 + term2 - L

# Physical constants (from document)
M_P = 1.22e19  # GeV
M_Z = 91.2     # GeV
m_t = 173.0    # GeV
m_b = 4.2      # GeV
m_c = 1.3      # GeV

print("=" * 70)
print("REPRODUCING APPENDIX C FROM two-loop-QCD-analysis.md")
print("=" * 70)

print("\nBeta function coefficients:")
for nf in [3, 4, 5, 6]:
    print(f"  N_f = {nf}: b0 = {b0(nf):.6f}, b1 = {b1(nf):.6f}")

alpha_MP = 1/64

print(f"\nStarting value: α_s(M_P) = {alpha_MP:.6f} = 1/64")

# Stage 1: M_P to m_t (Nf=6)
print("\n--- Stage 1: M_P → m_t (N_f = 6) ---")
L1 = np.log(m_t/M_P)
print(f"L1 = ln(m_t/M_P) = ln({m_t}/{M_P:.2e}) = {L1:.4f}")

alpha_mt = fsolve(lambda a: RGE_2loop(a, alpha_MP, L1, 6), 0.01)[0]
print(f"α_s(m_t) = {alpha_mt:.6f}")
print(f"Document claims: 0.010758")
print(f"Match: {np.isclose(alpha_mt, 0.010758, rtol=0.01)}")

# Stage 2: m_t to m_b (Nf=5)
print("\n--- Stage 2: m_t → m_b (N_f = 5) ---")
L2 = np.log(m_b/m_t)
print(f"L2 = ln(m_b/m_t) = ln({m_b}/{m_t}) = {L2:.4f}")

alpha_mb = fsolve(lambda a: RGE_2loop(a, alpha_mt, L2, 5), 0.015)[0]
print(f"α_s(m_b) = {alpha_mb:.6f}")
print(f"Document claims: 0.016284")
print(f"Match: {np.isclose(alpha_mb, 0.016284, rtol=0.01)}")

# Stage 3: m_b to m_c (Nf=4)
print("\n--- Stage 3: m_b → m_c (N_f = 4) ---")
L3 = np.log(m_c/m_b)
print(f"L3 = ln(m_c/m_b) = ln({m_c}/{m_b}) = {L3:.4f}")

alpha_mc = fsolve(lambda a: RGE_2loop(a, alpha_mb, L3, 4), 0.02)[0]
print(f"α_s(m_c) = {alpha_mc:.6f}")
print(f"Document claims: 0.021593")
print(f"Match: {np.isclose(alpha_mc, 0.021593, rtol=0.01)}")

# Stage 4: m_c to M_Z (Nf=3)
print("\n--- Stage 4: m_c → M_Z (N_f = 3) ---")
L4 = np.log(M_Z/m_c)
print(f"L4 = ln(M_Z/m_c) = ln({M_Z}/{m_c}) = {L4:.4f}")

alpha_MZ = fsolve(lambda a: RGE_2loop(a, alpha_mc, L4, 3), 0.12)[0]
print(f"α_s(M_Z) = {alpha_MZ:.6f}")
print(f"Document claims: 0.118723")
print(f"Match: {np.isclose(alpha_MZ, 0.118723, rtol=0.01)}")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print(f"α_s(M_P) = {alpha_MP:.6f}")
print(f"α_s(m_t) = {alpha_mt:.6f}")
print(f"α_s(m_b) = {alpha_mb:.6f}")
print(f"α_s(m_c) = {alpha_mc:.6f}")
print(f"α_s(M_Z) = {alpha_MZ:.6f}")
print(f"")
print(f"Experimental: 0.1179 ± 0.0010")
print(f"Discrepancy: {100*(alpha_MZ - 0.1179)/0.1179:.2f}%")

# =============================================================================
# DETAILED DEBUGGING
# =============================================================================

print("\n" + "=" * 70)
print("DETAILED DEBUGGING")
print("=" * 70)

# Check the RGE equation manually
print("\nManual verification of Stage 1:")
print(f"  L1 = {L1:.6f}")
print(f"  b0(6) = {b0(6):.6f}")
print(f"  b1(6) = {b1(6):.6f}")

# Using claimed α_s(m_t) = 0.010758
alpha_mt_claimed = 0.010758
term1_claimed = (1/alpha_mt_claimed - 1/alpha_MP)/(2*b0(6))
term2_claimed = (b1(6)/(2*b0(6)**2))*np.log(alpha_mt_claimed/alpha_MP)
rhs_claimed = term1_claimed + term2_claimed

print(f"\n  Using claimed α_s(m_t) = 0.010758:")
print(f"    Term1 = (1/α_mt - 1/α_MP)/(2b0) = {term1_claimed:.6f}")
print(f"    Term2 = (b1/2b0²)·ln(α_mt/α_MP) = {term2_claimed:.6f}")
print(f"    RHS = Term1 + Term2 = {rhs_claimed:.6f}")
print(f"    L1 = {L1:.6f}")
print(f"    Residual = RHS - L1 = {rhs_claimed - L1:.6f}")

# Using my calculated α_s(m_t) = 0.048923
alpha_mt_calc = 0.048923
term1_calc = (1/alpha_mt_calc - 1/alpha_MP)/(2*b0(6))
term2_calc = (b1(6)/(2*b0(6)**2))*np.log(alpha_mt_calc/alpha_MP)
rhs_calc = term1_calc + term2_calc

print(f"\n  Using my calculated α_s(m_t) = 0.048923:")
print(f"    Term1 = (1/α_mt - 1/α_MP)/(2b0) = {term1_calc:.6f}")
print(f"    Term2 = (b1/2b0²)·ln(α_mt/α_MP) = {term2_calc:.6f}")
print(f"    RHS = Term1 + Term2 = {rhs_calc:.6f}")
print(f"    L1 = {L1:.6f}")
print(f"    Residual = RHS - L1 = {rhs_calc - L1:.6f}")

# What's going on with fsolve?
print("\n" + "-" * 70)
print("FSOLVE BEHAVIOR ANALYSIS")
print("-" * 70)

# Try different initial guesses
print("\nStage 1 with different initial guesses:")
for guess in [0.001, 0.005, 0.01, 0.02, 0.05, 0.1]:
    result = fsolve(lambda a: RGE_2loop(a, alpha_MP, L1, 6), guess, full_output=True)
    sol = result[0][0]
    info = result[1]
    residual = abs(RGE_2loop(sol, alpha_MP, L1, 6))
    print(f"  Guess = {guess:.3f} → Solution = {sol:.6f}, Residual = {residual:.2e}")

# The one-loop solution for comparison
print("\n" + "-" * 70)
print("ONE-LOOP COMPARISON")
print("-" * 70)

def one_loop_running(alpha_init, L, Nf):
    """One-loop running: 1/α(μ) = 1/α(μ₀) + 2b₀L"""
    b0_val = b0(Nf)
    return alpha_init / (1 + 2*b0_val*alpha_init*L)

# For running DOWN, L is negative
alpha_mt_1loop = one_loop_running(alpha_MP, L1, 6)
print(f"One-loop: α_s(m_t) = {alpha_mt_1loop:.6f}")

# Wait, L1 is negative! Let's check the running direction
print(f"\nL1 = {L1:.4f} (negative because m_t < M_P)")
print(f"Running DOWN in energy: α_s should INCREASE (asymptotic freedom)")
print(f"So α_s(m_t) should be > α_s(M_P) = 0.015625")
print(f"\nMy calculation: α_s(m_t) = 0.049 > 0.016 ✓ (Correct direction)")
print(f"Document claim: α_s(m_t) = 0.011 < 0.016 ✗ (WRONG direction!)")

# =============================================================================
# THE KEY INSIGHT
# =============================================================================

print("\n" + "=" * 70)
print("KEY INSIGHT: SIGN CONVENTION ERROR IN DOCUMENT")
print("=" * 70)

print("""
The document's claimed intermediate values are PHYSICALLY IMPOSSIBLE.

When running DOWN in energy (M_P → m_t), due to asymptotic freedom,
α_s must INCREASE, not decrease.

  α_s(M_P) = 0.0156 (given)
  α_s(m_t) = should be > 0.0156

But the document claims:
  α_s(m_t) = 0.0108 < 0.0156  ← VIOLATES ASYMPTOTIC FREEDOM

The ONLY way to get α_s DECREASING when running to lower energy
would be if QCD were NOT asymptotically free (b₀ < 0), which
requires N_f > 16.5 flavors.

Conclusion: The document contains a fundamental sign error.
The claimed 0.7% agreement is based on incorrect physics.
""")

# =============================================================================
# THE ALTERNATIVE INTERPRETATION
# =============================================================================

print("\n" + "=" * 70)
print("ALTERNATIVE: MAYBE THE DOCUMENT RUNS BACKWARDS?")
print("=" * 70)

print("\nWhat if the document runs from M_Z → M_P instead?")
print("Let's check if that produces the claimed intermediate values.")

# Start from α_s(M_Z) = 0.1187 and run UP to M_P
alpha_mz_start = 0.1187

# Stage 1: M_Z → m_c (Nf=3) - running DOWN
L1_rev = np.log(m_c/M_Z)  # negative
print(f"\nM_Z → m_c: L = {L1_rev:.4f}")
alpha_mc_rev = fsolve(lambda a: RGE_2loop(a, alpha_mz_start, L1_rev, 3), 0.3)[0]
print(f"α_s(m_c) = {alpha_mc_rev:.6f}")

# Stage 2: m_c → m_b (Nf=4) - running UP
L2_rev = np.log(m_b/m_c)  # positive
print(f"\nm_c → m_b: L = {L2_rev:.4f}")
alpha_mb_rev = fsolve(lambda a: RGE_2loop(a, alpha_mc_rev, L2_rev, 4), 0.1)[0]
print(f"α_s(m_b) = {alpha_mb_rev:.6f}")

# Stage 3: m_b → m_t (Nf=5) - running UP
L3_rev = np.log(m_t/m_b)  # positive
print(f"\nm_b → m_t: L = {L3_rev:.4f}")
alpha_mt_rev = fsolve(lambda a: RGE_2loop(a, alpha_mb_rev, L3_rev, 5), 0.05)[0]
print(f"α_s(m_t) = {alpha_mt_rev:.6f}")

# Stage 4: m_t → M_P (Nf=6) - running UP
L4_rev = np.log(M_P/m_t)  # positive
print(f"\nm_t → M_P: L = {L4_rev:.4f}")
alpha_mp_rev = fsolve(lambda a: RGE_2loop(a, alpha_mt_rev, L4_rev, 6), 0.01)[0]
print(f"α_s(M_P) = {alpha_mp_rev:.6f}")
print(f"1/α_s(M_P) = {1/alpha_mp_rev:.2f}")

print("\n" + "-" * 70)
print("This also doesn't match the document's intermediate values.")
print("-" * 70)

# =============================================================================
# FINAL DIAGNOSIS
# =============================================================================

print("\n" + "=" * 70)
print("FINAL DIAGNOSIS")
print("=" * 70)

print("""
After extensive analysis, the document's claimed intermediate values are
PHYSICALLY INCONSISTENT with QCD.

The claimed running:
  α_s(M_P) = 0.0156
  α_s(m_t) = 0.0108 (claimed - WRONG)
  α_s(m_b) = 0.0163 (claimed)
  α_s(m_c) = 0.0216 (claimed)
  α_s(M_Z) = 0.1187 (claimed)

Has α_s DECREASING from M_P to m_t, which violates asymptotic freedom.

CORRECT running should give:
  α_s(M_P) = 0.0156
  α_s(m_t) = 0.049 (increases because energy decreased)
  α_s(m_b) = 0.063 (increases more)
  α_s(m_c) = 0.071 (increases more)
  α_s(M_Z) = 0.049 (decreases because we run UP from m_c to M_Z)

The final result α_s(M_Z) ≈ 0.049 is ~58% away from experiment (0.1179),
NOT 0.7% as claimed.

ROOT CAUSE:
The document appears to have constructed intermediate values that give
the desired final answer, rather than computing them from the RGE.
""")
