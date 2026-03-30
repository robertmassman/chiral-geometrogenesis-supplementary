#!/usr/bin/env python3
"""
Verify UV convergence table for Theorem 7.6.8: Effective Action Convergence.

Parameters:
  beta = 100, g_0^2 = 6/beta = 0.06
  b_0 = 11/(16*pi^2) ~ 0.0697
  One-loop running coupling: g_k^2 = g_0^2 / (1 - 2*b_0*g_0^2*ln(2)*k)

Two conventions explored:
  Convention A: Coupling INCREASES with k (UV -> IR blocking steps)
  Convention B: Coupling DECREASES with k (IR -> UV, asymptotic freedom)
"""

import numpy as np
from scipy.special import zeta

print("=" * 80)
print("THEOREM 7.6.8 UV CONVERGENCE TABLE VERIFICATION")
print("=" * 80)

# ─── Parameters ───────────────────────────────────────────────────────────────
beta = 100
g0_sq = 6.0 / beta  # = 0.06
b0 = 11.0 / (16.0 * np.pi**2)
ln2 = np.log(2)

print(f"\n{'PARAMETERS':=^60}")
print(f"  beta           = {beta}")
print(f"  g_0^2          = 6/beta = {g0_sq:.6f}")
print(f"  b_0            = 11/(16*pi^2) = {b0:.8f}")
print(f"  ln(2)          = {ln2:.8f}")
print(f"  2*b_0*g_0^2*ln(2) = {2*b0*g0_sq*ln2:.8f}")

# ─── Landau pole location ────────────────────────────────────────────────────
k_pole = 1.0 / (2 * b0 * g0_sq * ln2)
print(f"\n{'LANDAU POLE':=^60}")
print(f"  k_pole = 1/(2*b_0*g_0^2*ln(2)) = {k_pole:.4f}")
print(f"  (coupling diverges at k = {k_pole:.4f})")

# ─── Zeta function reference ─────────────────────────────────────────────────
zeta_3_2 = zeta(3.0 / 2.0)
zeta_3 = zeta(3.0)
print(f"\n{'ZETA FUNCTION REFERENCES':=^60}")
print(f"  zeta(3/2) = {zeta_3_2:.8f}")
print(f"  zeta(3)   = {zeta_3:.8f}")

# ═══════════════════════════════════════════════════════════════════════════════
# CONVENTION A: Coupling INCREASES with k (UV blocking toward IR)
#   g_k^2 = g_0^2 / (1 - 2*b_0*g_0^2*ln(2)*k)
# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n{'=' * 80}")
print("CONVENTION A: Coupling INCREASES with k (UV -> IR)")
print("  g_k^2 = g_0^2 / (1 - 2*b_0*g_0^2*ln(2)*k)")
print("  Each step k integrates out a momentum shell, moving toward IR.")
print("  Coupling grows as we approach the Landau pole.")
print("=" * 80)

# ─── Contraction threshold and k_max ─────────────────────────────────────────
g_star_sq = 0.1
# k_max: max{k : g_k^2 <= g_*^2}
# g_k^2 <= g_*^2  =>  g_0^2 / (1 - 2*b_0*g_0^2*ln(2)*k) <= g_*^2
# =>  1 - 2*b_0*g_0^2*ln(2)*k >= g_0^2/g_*^2
# =>  k <= (1 - g_0^2/g_*^2) / (2*b_0*g_0^2*ln(2))
k_max_exact = (1.0 - g0_sq / g_star_sq) / (2 * b0 * g0_sq * ln2)
k_max = int(np.floor(k_max_exact))
print(f"\n  Contraction threshold: g_*^2 = {g_star_sq}")
print(f"  k_max (exact)  = {k_max_exact:.4f}")
print(f"  k_max (floor)  = {k_max}")

# ─── Table of values ─────────────────────────────────────────────────────────
k_values = [0, 1, 2, 5, 10, 20, 50, 100]
# Also add k_max if not in list
if k_max not in k_values:
    k_values.append(k_max)
    k_values.sort()

# Filter to valid range
k_values = [k for k in k_values if k < k_pole]

def g_sq_A(k):
    """One-loop coupling, convention A (increasing)."""
    denom = 1.0 - 2 * b0 * g0_sq * ln2 * k
    if denom <= 0:
        return float('inf')
    return g0_sq / denom

print(f"\n  {'k':>6s} | {'g_k^2':>12s} | {'g_k^3':>12s} | {'g_k^(3/2)':>12s} | {'Sum g_j^3':>12s} | {'Sum g_j^(3/2)':>14s}")
print(f"  {'-'*6:s}-+-{'-'*12:s}-+-{'-'*12:s}-+-{'-'*12:s}-+-{'-'*12:s}-+-{'-'*14:s}")

cumsum_g3 = 0.0
cumsum_g32 = 0.0
for k in k_values:
    gk2 = g_sq_A(k)
    gk3 = gk2 ** (3.0 / 2.0)  # g_k^3 means (g_k^2)^{3/2} = |g_k|^3
    gk_32 = gk2 ** (3.0 / 4.0)  # (g_k^2)^{3/4}
    cumsum_g3 += gk3
    cumsum_g32 += gk_32
    marker = " <-- k_max" if k == k_max else ""
    print(f"  {k:6d} | {gk2:12.8f} | {gk3:12.8f} | {gk_32:12.8f} | {cumsum_g3:12.8f} | {cumsum_g32:14.8f}{marker}")

# Full sum from 0 to k_max
full_sum_g3 = sum(g_sq_A(k)**(3.0/2.0) for k in range(k_max + 1))
full_sum_g32 = sum(g_sq_A(k)**(3.0/4.0) for k in range(k_max + 1))

print(f"\n  FULL SUMS (k = 0 to k_max = {k_max}):")
print(f"    Sum_{{k=0}}^{{k_max}} (g_k^2)^{{3/2}} = {full_sum_g3:.8f}")
print(f"    Sum_{{k=0}}^{{k_max}} (g_k^2)^{{3/4}} = {full_sum_g32:.8f}")

# ─── Convergence analysis ────────────────────────────────────────────────────
print(f"\n  {'CONVERGENCE ANALYSIS':=^60}")
print(f"  The sum is FINITE because:")
print(f"    1. k_max = {k_max} is finite (coupling hits threshold)")
print(f"    2. k_pole = {k_pole:.2f} provides an absolute cutoff")
print(f"    3. Each term g_k^3 is bounded: g_0^3 = {g0_sq**(3/2):.6f}")
print(f"       to g_{{k_max}}^3 = {g_sq_A(k_max)**(3/2):.6f}")
print(f"    4. Total sum = {full_sum_g3:.6f}")
print(f"    5. Even without threshold, max possible terms = {int(np.floor(k_pole))}")

# Worst-case bound: k_max * g_*^3
bound_trivial = (k_max + 1) * g_star_sq**(3.0/2.0)
print(f"\n  Trivial bound: (k_max+1) * (g_*^2)^(3/2) = {k_max+1} * {g_star_sq**(3/2):.6f} = {bound_trivial:.6f}")
print(f"  Actual sum / bound = {full_sum_g3 / bound_trivial:.6f}")

# ═══════════════════════════════════════════════════════════════════════════════
# CONVENTION B: Coupling DECREASES with k (IR -> UV, asymptotic freedom)
#   g_k^2 = 1 / (2*b_0*k*ln(2))  for large k (deep UV)
# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n{'=' * 80}")
print("CONVENTION B: Coupling DECREASES with k (IR -> UV, asymptotic freedom)")
print("  g_k^2 ~ 1/(2*b_0*k*ln(2))  for k >> 1")
print("  Here k counts momentum shells from IR toward UV.")
print("  Coupling decreases as we go deeper into UV (asymptotic freedom).")
print("=" * 80)

def g_sq_B(k):
    """Asymptotically free coupling, convention B (decreasing)."""
    if k == 0:
        return float('inf')  # undefined at k=0
    return 1.0 / (2 * b0 * k * ln2)

# Start from k=1 since k=0 is singular
k_values_B = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000]

print(f"\n  {'k':>6s} | {'g_k^2':>12s} | {'(g_k^2)^(3/2)':>14s} | {'1/k^(3/2)':>12s} | {'Sum (g_j^2)^(3/2)':>18s}")
print(f"  {'-'*6:s}-+-{'-'*12:s}-+-{'-'*14:s}-+-{'-'*12:s}-+-{'-'*18:s}")

cumsum_B = 0.0
for k in k_values_B:
    gk2 = g_sq_B(k)
    gk3 = gk2 ** (3.0 / 2.0)
    k_inv_32 = 1.0 / k**(3.0/2.0)
    # Accumulate all terms from previous display value to this one
    prev_k = k_values_B[k_values_B.index(k) - 1] + 1 if k_values_B.index(k) > 0 else 1
    for j in range(prev_k, k + 1):
        cumsum_B += g_sq_B(j) ** (3.0 / 2.0)
    print(f"  {k:6d} | {gk2:12.8f} | {gk3:14.10f} | {k_inv_32:12.8f} | {cumsum_B:18.8f}")

# The infinite sum comparison
coeff_B = 1.0 / (2 * b0 * ln2) ** (3.0 / 2.0)
print(f"\n  Coefficient: [1/(2*b_0*ln(2))]^(3/2) = {coeff_B:.8f}")
print(f"  Sum (g_k^2)^(3/2) ~ {coeff_B:.4f} * zeta(3/2) = {coeff_B * zeta_3_2:.8f}")

# Compute partial sums more carefully
N_terms = 10000
partial_sum_B = sum(g_sq_B(k)**(3.0/2.0) for k in range(1, N_terms + 1))
analytic_B = coeff_B * zeta_3_2
print(f"\n  Partial sum (k=1 to {N_terms}):  {partial_sum_B:.8f}")
print(f"  Analytic (coeff * zeta(3/2)):  {analytic_B:.8f}")
print(f"  Ratio partial/analytic:        {partial_sum_B / analytic_B:.8f}")

print(f"\n  CONVERGENCE: The sum converges because (g_k^2)^(3/2) ~ C/k^(3/2)")
print(f"  and zeta(3/2) = {zeta_3_2:.8f} is finite (p = 3/2 > 1).")

# ═══════════════════════════════════════════════════════════════════════════════
# SUMMARY COMPARISON
# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n{'=' * 80}")
print("SUMMARY")
print("=" * 80)
print(f"""
  Convention A (coupling increases, UV->IR blocking):
    - Coupling runs from g_0^2 = {g0_sq} up to g_*^2 = {g_star_sq}
    - Finite sum: k_max = {k_max} terms
    - Total Sum_{{k=0}}^{{{k_max}}} (g_k^2)^{{3/2}} = {full_sum_g3:.8f}
    - Landau pole at k = {k_pole:.2f} (never reached)

  Convention B (coupling decreases, asymptotic freedom, IR->UV):
    - Coupling falls as 1/(2*b_0*k*ln(2))
    - Infinite sum CONVERGES: Sum ~ {coeff_B:.4f} * zeta(3/2) = {analytic_B:.6f}
    - Convergence rate: (g_k^2)^(3/2) ~ 1/k^(3/2), p-series with p=3/2 > 1

  KEY INSIGHT:
    In both conventions, Sum (g_k^2)^(3/2) is FINITE.
    - Convention A: finite because sum has finitely many terms (k_max = {k_max})
    - Convention B: finite because terms decay as 1/k^(3/2) (convergent p-series)
""")

# ═══════════════════════════════════════════════════════════════════════════════
# DETAILED TABLE for k = 0..k_max (Convention A) - for the proof
# ═══════════════════════════════════════════════════════════════════════════════
print(f"{'=' * 80}")
print(f"DETAILED TABLE: Convention A, k = 0 to k_max = {k_max}")
print(f"{'=' * 80}")

print(f"\n  {'k':>4s} | {'g_k^2':>12s} | {'(g_k^2)^(3/2)':>14s} | {'Cumulative':>14s} | {'g_k^2/g_*^2':>12s}")
print(f"  {'-'*4:s}-+-{'-'*12:s}-+-{'-'*14:s}-+-{'-'*14:s}-+-{'-'*12:s}")

cumsum = 0.0
for k in range(k_max + 1):
    gk2 = g_sq_A(k)
    gk3 = gk2 ** (3.0 / 2.0)
    cumsum += gk3
    ratio = gk2 / g_star_sq
    if k <= 20 or k % 10 == 0 or k == k_max:
        print(f"  {k:4d} | {gk2:12.8f} | {gk3:14.10f} | {cumsum:14.8f} | {ratio:12.6f}")

print(f"\n  Final sum = {cumsum:.10f}")

# ─── Additional check: contraction factor ────────────────────────────────────
print(f"\n{'=' * 80}")
print("CONTRACTION FACTOR CHECK")
print("=" * 80)
print(f"\n  For the RG map R_k to be a contraction, we need:")
print(f"  ||R_k(u) - R_k(v)|| <= rho_k * ||u - v||")
print(f"  where rho_k = C * g_k^2 for some constant C.")
print(f"\n  With g_*^2 = {g_star_sq} and requiring rho_k < 1,")
print(f"  we need C < 1/g_*^2 = {1/g_star_sq:.1f}.")
print(f"\n  The product of contraction factors:")
print(f"  Product_{{k=0}}^{{k_max}} rho_k = C^(k_max+1) * Product g_k^2")

log_product = sum(np.log(g_sq_A(k)) for k in range(k_max + 1))
print(f"\n  Sum of ln(g_k^2), k=0..{k_max}: {log_product:.6f}")
print(f"  Product of g_k^2: exp({log_product:.4f}) = {np.exp(log_product):.6e}")
print(f"  (Product of g_k^2)^(1/{k_max+1}) = geometric mean g_k^2 = {np.exp(log_product/(k_max+1)):.8f}")
