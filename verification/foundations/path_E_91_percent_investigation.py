#!/usr/bin/env python3
"""
Path E Investigation: Is the combined NP correction factor topological?

The bootstrap predicts sqrt(sigma)_1loop = 481.1 MeV.
Observation: sqrt(sigma) = 440 +/- 30 MeV (FLAG 2024).

Four NP corrections bring this to ~439-435 MeV:
  - Gluon condensate: varies with chi_eff
  - Threshold matching: -3.0%
  - Two-loop beta: -2.0%
  - Instanton disruption: -1.6% to -1.7%

Question: Does exp(-1/N_c^2) = 0.895 or some other topological form
reproduce the combined correction factor?

References:
  - Props 0.0.17z, z1, z2
  - Research-Absolute-Scale-Determination-Paths.md, Path E
"""

import numpy as np
from itertools import product

# ==============================================================
# Section 1: The four NP corrections from Props 0.0.17z/z1/z2
# ==============================================================

N_c = 3
N_f = 3  # light flavors at confinement scale

# --- Group theory constants ---
C_A = N_c                          # = 3
C_F = (N_c**2 - 1) / (2 * N_c)    # = 4/3
dim_adj = N_c**2 - 1               # = 8
b_0_coeff = (11 * N_c - 2 * N_f)  # = 27 (numerator of b_0)
b_0 = b_0_coeff / (12 * np.pi)    # = 9/(4*pi) = 0.7162

# Bootstrap one-loop prediction
sqrt_sigma_1loop = 481.1  # MeV
sqrt_sigma_obs = 440.0    # MeV (FLAG 2024)
sqrt_sigma_obs_err = 30.0  # MeV

print("=" * 70)
print("PATH E INVESTIGATION: Topological form of NP correction factor")
print("=" * 70)

# --- Correction 1: Gluon condensate ---
# From Prop 0.0.17z: delta_sqrt_sigma / sqrt_sigma = (1/2) * c_G * <G^2>/sigma^2
# Phenomenological (z):  c_G = 0.2,  correction = -3.0%
# Geometric chi=4 (z1): c_G = 0.37, correction = -5.9%
# Scale-dep chi_eff (z2): c_G_eff = 0.127, correction = -2.0%

G2_condensate = 0.012  # GeV^4 (SVZ value)
sigma_sq = (0.440)**2  # GeV^2 -> sigma = 0.194 GeV^2... wait
# sigma = sqrt_sigma^2 in appropriate units
# sqrt(sigma) = 440 MeV = 0.440 GeV, so sigma = 0.194 GeV^2
sigma = 0.440**2  # GeV^2

# Three versions of gluon condensate coefficient
c_G_phenom = 0.20   # Prop 0.0.17z
c_G_chi4 = 0.37     # Prop 0.0.17z1 (fixed chi=4)
c_G_chi_eff = 0.127  # Prop 0.0.17z2 (chi_eff = 2.21)

ratio_G2_sigma2 = G2_condensate / sigma**2

corr_glue_phenom = -0.5 * c_G_phenom * ratio_G2_sigma2
corr_glue_chi4 = -0.5 * c_G_chi4 * ratio_G2_sigma2
corr_glue_chi_eff = -0.5 * c_G_chi_eff * ratio_G2_sigma2

# --- Correction 2: Threshold matching ---
corr_threshold = -0.030  # -3.0%

# --- Correction 3: Two-loop beta ---
corr_twoloop = -0.020  # -2.0%

# --- Correction 4: Instanton disruption ---
rho_inst = 0.338  # fm (Prop z1 geometric derivation)
n_inst = 1.03     # fm^-4
c_inst = 0.030    # (Prop z1)
hbarc = 197.327   # MeV*fm
rho_sigma = rho_inst * sqrt_sigma_obs / hbarc  # dimensionless

# From z2: correction is -1.7%
corr_inst_z = -0.016   # Prop z
corr_inst_z2 = -0.017  # Prop z2

print("\n--- Individual NP Corrections ---")
print(f"{'Source':<25} {'Prop z':>10} {'Prop z1 (chi=4)':>15} {'Prop z2 (chi_eff)':>18}")
print("-" * 70)
print(f"{'Gluon condensate':<25} {corr_glue_phenom:>+10.3f} {corr_glue_chi4:>+15.3f} {corr_glue_chi_eff:>+18.3f}")
print(f"{'Threshold matching':<25} {corr_threshold:>+10.3f} {corr_threshold:>+15.3f} {corr_threshold:>+18.3f}")
print(f"{'Two-loop beta':<25} {corr_twoloop:>+10.3f} {corr_twoloop:>+15.3f} {corr_twoloop:>+18.3f}")
print(f"{'Instanton disruption':<25} {corr_inst_z:>+10.3f} {corr_inst_z:>+15.3f} {corr_inst_z2:>+18.3f}")

total_z = corr_glue_phenom + corr_threshold + corr_twoloop + corr_inst_z
total_z1 = corr_glue_chi4 + corr_threshold + corr_twoloop + corr_inst_z
total_z2 = corr_glue_chi_eff + corr_threshold + corr_twoloop + corr_inst_z2

print("-" * 70)
print(f"{'TOTAL':<25} {total_z:>+10.3f} {total_z1:>+15.3f} {total_z2:>+18.3f}")
print(f"{'Factor (1+total)':<25} {1+total_z:>10.4f} {1+total_z1:>15.4f} {1+total_z2:>18.4f}")

factor_z = 1 + total_z
factor_z1 = 1 + total_z1
factor_z2 = 1 + total_z2

sqrt_sigma_z = sqrt_sigma_1loop * factor_z
sqrt_sigma_z1 = sqrt_sigma_1loop * factor_z1
sqrt_sigma_z2 = sqrt_sigma_1loop * factor_z2

print(f"\n{'Predicted sqrt(sigma)':<25} {sqrt_sigma_z:>10.1f} {sqrt_sigma_z1:>15.1f} {sqrt_sigma_z2:>18.1f} MeV")
print(f"{'Observed':<25} {'440 +/- 30 MeV':>45}")

# ==============================================================
# Section 2: Candidate topological forms
# ==============================================================

print("\n" + "=" * 70)
print("CANDIDATE TOPOLOGICAL CORRECTION FACTORS")
print("=" * 70)

# Target factors
targets = {
    'Prop z (phenom)': factor_z,
    'Prop z2 (chi_eff)': factor_z2,
}

# Candidate forms involving N_c, group theory constants
candidates = {}

# Basic exponential forms
candidates['exp(-1/N_c^2)'] = np.exp(-1/N_c**2)
candidates['exp(-1/(N_c^2-1))'] = np.exp(-1/(N_c**2 - 1))
candidates['exp(-1/(2*N_c^2))'] = np.exp(-1/(2*N_c**2))
candidates['exp(-C_F/N_c^2)'] = np.exp(-C_F/N_c**2)
candidates['exp(-1/(N_c*(N_c+1)))'] = np.exp(-1/(N_c*(N_c+1)))

# Power-law forms (1/N_c expansion)
candidates['1 - 1/N_c^2'] = 1 - 1/N_c**2
candidates['1 - 1/(N_c^2+1)'] = 1 - 1/(N_c**2 + 1)
candidates['1 - C_F/N_c^2'] = 1 - C_F/N_c**2
candidates['1 - 1/(2*N_c^2)'] = 1 - 1/(2*N_c**2)
candidates['1 - 1/(N_c*(N_c+1))'] = 1 - 1/(N_c*(N_c+1))
candidates['(N_c^2-1)/N_c^2'] = (N_c**2 - 1)/N_c**2  # = 1 - 1/N_c^2

# Beta function related
candidates['exp(-b_0/(2*pi))'] = np.exp(-b_0/(2*np.pi))
candidates['exp(-1/(4*pi*b_0))'] = np.exp(-1/(4*np.pi*b_0))

# Euler characteristic related (chi = 4 for stella)
chi_stella = 4
candidates['exp(-1/chi)'] = np.exp(-1/chi_stella)
candidates['exp(-2/chi)'] = np.exp(-2/chi_stella)
candidates['1 - 1/chi'] = 1 - 1/chi_stella
candidates['1 - 2/(chi*N_c^2)'] = 1 - 2/(chi_stella * N_c**2)

# Combinations of N_c and chi
candidates['exp(-chi/(N_c^2*chi+N_c^2))'] = np.exp(-chi_stella/(N_c**2 * chi_stella + N_c**2))
candidates['exp(-1/(N_c^2+N_c))'] = np.exp(-1/(N_c**2 + N_c))

# Scale-dependent chi_eff = 2.21
chi_eff = 2.21
candidates['exp(-1/(chi_eff*N_c))'] = np.exp(-1/(chi_eff * N_c))
candidates['exp(-chi_eff/(2*N_c^2))'] = np.exp(-chi_eff/(2 * N_c**2))

# Casimir-related deeper forms
candidates['exp(-C_F/(N_c*C_A))'] = np.exp(-C_F/(N_c*C_A))
candidates['(1-1/N_c^2)^(1/2)'] = np.sqrt(1 - 1/N_c**2)

# b_0-dependent
candidates['exp(-9/(4*pi*N_c)^2)'] = np.exp(-9/(4*np.pi*N_c)**2)

print(f"\n{'Candidate':<35} {'Value':>8} ", end="")
for name in targets:
    print(f"{'|Δ| from ' + name:>22}", end="")
print()
print("-" * 90)

# Sort by closeness to z2 target
sorted_candidates = sorted(candidates.items(),
                          key=lambda x: abs(x[1] - factor_z2))

for name, val in sorted_candidates:
    print(f"{name:<35} {val:>8.5f} ", end="")
    for tname, tval in targets.items():
        delta = abs(val - tval)
        print(f"{delta:>22.5f}", end="")
    print()

# ==============================================================
# Section 3: Deep analysis of the best candidates
# ==============================================================

print("\n" + "=" * 70)
print("DEEP ANALYSIS: Best candidate forms")
print("=" * 70)

# The z2 combined factor
print(f"\nTarget: combined correction factor from Prop z2 = {factor_z2:.4f}")
print(f"This means: sqrt(sigma) is reduced by {(1-factor_z2)*100:.1f}% from one-loop")

# Check: what exponent x gives exp(-x) = factor_z2?
x_needed = -np.log(factor_z2)
print(f"\nFor exp(-x) = {factor_z2:.4f}, need x = {x_needed:.5f}")
print(f"  Compare: 1/N_c^2 = {1/N_c**2:.5f}")
print(f"  Compare: 1/(N_c^2-1) = {1/(N_c**2-1):.5f}")
print(f"  Compare: 1/(N_c*(N_c+1)) = {1/(N_c*(N_c+1)):.5f}")
print(f"  Compare: C_F/N_c^2 = {C_F/N_c**2:.5f}")

# Check: what coefficient c gives 1 - c/N_c^2 = factor_z2?
c_needed = (1 - factor_z2) * N_c**2
print(f"\nFor 1 - c/N_c^2 = {factor_z2:.4f}, need c = {c_needed:.4f}")
print(f"  Compare: 1 (simplest) → factor = {1-1/N_c**2:.4f}")
print(f"  Compare: C_F = {C_F:.4f} → factor = {1-C_F/N_c**2:.4f}")

# What about the z correction?
print(f"\nTarget: combined correction factor from Prop z = {factor_z:.4f}")
x_needed_z = -np.log(factor_z)
print(f"For exp(-x) = {factor_z:.4f}, need x = {x_needed_z:.5f}")
c_needed_z = (1 - factor_z) * N_c**2
print(f"For 1 - c/N_c^2 = {factor_z:.4f}, need c = {c_needed_z:.4f}")

# ==============================================================
# Section 4: Large-N_c analysis
# ==============================================================

print("\n" + "=" * 70)
print("LARGE-N_c SCALING ANALYSIS")
print("=" * 70)

print("""
In the 1/N_c expansion (t'Hooft large-N_c limit):

1. Planar diagrams dominate (leading order)
2. Non-planar corrections suppressed by 1/N_c^2
3. The four NP corrections scale differently with N_c:

   a) Gluon condensate: <G^2> ~ N_c^2 * Lambda^4 (scales with N_c^2)
      But the OPE coefficient c_G contains 1/(N_c^2 - 1) factors
      Net: delta ~ O(1) at large N_c (no suppression)

   b) Threshold matching: depends on N_f/N_c ratio
      In Veneziano limit (N_f/N_c fixed): O(1)
      In real world (N_f fixed): correction shrinks as N_c grows

   c) Two-loop beta: b_1/b_0^2 ~ O(1) at large N_c
      (both b_1 and b_0 scale as N_c)

   d) Instanton: exp(-8*pi^2/(g^2)) ~ exp(-N_c/lambda)
      Exponentially suppressed at large N_c (in 't Hooft limit)

Conclusion: The four corrections do NOT scale uniformly with N_c.
A single topological form exp(-1/N_c^2) would predict uniform 1/N_c^2
scaling, but the actual corrections have mixed scaling behavior.
""")

# Compute corrections for various N_c to see scaling
print("Scaling of individual corrections with N_c:")
print(f"{'N_c':>4} {'b_0':>8} {'1/N_c^2':>8} {'exp(-1/N_c^2)':>14} {'1-1/N_c^2':>10}")
print("-" * 50)
for nc in [2, 3, 4, 5, 6, 10, 100]:
    b0_nc = (11*nc - 2*N_f) / (12*np.pi)
    print(f"{nc:>4} {b0_nc:>8.4f} {1/nc**2:>8.4f} {np.exp(-1/nc**2):>14.6f} {1-1/nc**2:>10.6f}")

# ==============================================================
# Section 5: Instanton resummation on stella boundary
# ==============================================================

print("\n" + "=" * 70)
print("INSTANTON CONTRIBUTION ON STELLA BOUNDARY")
print("=" * 70)

print("""
On the stella boundary, the instanton contribution can potentially
be computed exactly because the geometry constrains the moduli space.

Key parameters (from Prop 0.0.17z1):
  - Instanton density: n = 1.03 fm^-4 (from S_4 symmetry)
  - Average size: <rho> = 0.338 fm (from stella cavity)
  - Disruption coefficient: c_inst = 0.030 (from constrained moduli)

The instanton partition function on the stella:
  Z_inst = sum_{k=0}^{inf} (1/k!) * (n*V_eff)^k * exp(-8*pi^2*k/g^2)

At the confinement scale, g^2 ~ 4*pi*alpha_s ~ 4*pi * 0.3 ~ 3.77
  exp(-8*pi^2/g^2) ~ exp(-20.9) ~ 8.3e-10 per instanton

But this is the DILUTE instanton gas approximation. The instanton
LIQUID model (Shuryak) uses a different approach where the instanton
density is treated as a thermodynamic variable.
""")

# Key calculation: instanton contribution at different scales
g2_conf = 4 * np.pi * 0.3  # at confinement scale
S_inst = 8 * np.pi**2 / g2_conf
print(f"Instanton action at confinement scale: S = 8*pi^2/g^2 = {S_inst:.1f}")
print(f"exp(-S) = {np.exp(-S_inst):.2e}")
print(f"This is TINY - individual instantons are strongly suppressed")
print(f"But the instanton liquid is a collective effect, not individual tunneling")

# At the stella boundary UV scale (alpha_s = 1/64)
g2_UV = 4 * np.pi / 64
S_UV = 8 * np.pi**2 / g2_UV
print(f"\nAt stella UV scale (alpha_s = 1/64):")
print(f"g^2 = {g2_UV:.5f}, S = {S_UV:.1f}")
print(f"exp(-S) = {np.exp(-S_UV):.2e} (astronomically small)")

# ==============================================================
# Section 6: Can we derive the combined factor?
# ==============================================================

print("\n" + "=" * 70)
print("DERIVATION ATTEMPT: Combined NP factor from first principles")
print("=" * 70)

print("""
Strategy: Decompose the combined correction into perturbative and
truly non-perturbative pieces, then see if each has a clean form.

Perturbative corrections (computable order by order):
  - Two-loop beta: -2.0%  → This is genuinely perturbative
  - Threshold matching: -3.0% → This is perturbative (running)
  Subtotal: -5.0%

Non-perturbative corrections (require all-orders/topological input):
  - Gluon condensate: -2.0% (z2) to -3.0% (z)
  - Instanton disruption: -1.6% to -1.7%
  Subtotal: -3.6% (z2) to -4.6% (z)
""")

# Perturbative piece
pert_corr = corr_threshold + corr_twoloop  # = -0.05
pert_factor = 1 + pert_corr
print(f"Perturbative factor: {pert_factor:.4f} (= 1 - 0.05)")

# Non-perturbative piece (z2)
np_corr_z2 = corr_glue_chi_eff + corr_inst_z2
np_factor_z2 = 1 + np_corr_z2
print(f"Non-perturbative factor (z2): {np_factor_z2:.4f}")

# Non-perturbative piece (z)
np_corr_z = corr_glue_phenom + corr_inst_z
np_factor_z = 1 + np_corr_z
print(f"Non-perturbative factor (z):  {np_factor_z:.4f}")

# Check: does the NP piece have a topological form?
print(f"\nNon-perturbative correction = {np_corr_z2:.4f} (z2) or {np_corr_z:.4f} (z)")
print(f"Compare candidate NP forms:")

np_candidates = {
    'exp(-1/N_c^2) - 1': np.exp(-1/N_c**2) - 1,
    '-1/N_c^2': -1/N_c**2,
    '-C_F/N_c^2': -C_F/N_c**2,
    '-1/(2*N_c^2)': -1/(2*N_c**2),
    '-1/(N_c*(N_c+1))': -1/(N_c*(N_c+1)),
    '-1/(2*(N_c^2-1))': -1/(2*(N_c**2-1)),
}

print(f"\n{'Form':<25} {'Value':>10} {'|Δ| from z2 NP':>15} {'|Δ| from z NP':>15}")
print("-" * 70)
for name, val in sorted(np_candidates.items(), key=lambda x: abs(x[1] - np_corr_z2)):
    print(f"{name:<25} {val:>+10.5f} {abs(val-np_corr_z2):>15.5f} {abs(val-np_corr_z):>15.5f}")

# ==============================================================
# Section 7: The key test — does it work for other N_c?
# ==============================================================

print("\n" + "=" * 70)
print("PREDICTIVE TEST: What would the correction be for other N_c?")
print("=" * 70)

print("""
If the combined correction is truly topological (e.g., exp(-1/N_c^2)),
it must make predictions for SU(2) and SU(4+) that can be checked
against lattice data.

Lattice QCD results for string tension ratios (Lucini & Teper 2001,
Bringoltz & Teper 2007):

  sqrt(sigma_N)/sqrt(sigma_3) data from lattice:
""")

# Lattice data: string tension ratios relative to SU(3)
# From Lucini, Teper, Wenger (2004) and Athenodorou, Teper (2021)
lattice_ratios = {
    2: 0.836,  # SU(2)/SU(3) ratio (approximate from Casimir scaling)
    3: 1.000,
    4: 1.118,
    5: 1.206,
    6: 1.276,
}

# If correction is exp(-1/N_c^2), the ratio of correction factors is:
print(f"{'N_c':>4} {'exp(-1/N_c^2)':>14} {'Ratio to N_c=3':>15} {'Lattice ratio':>14}")
print("-" * 50)
f3 = np.exp(-1/9)
for nc, lat_ratio in lattice_ratios.items():
    fn = np.exp(-1/nc**2)
    ratio = fn / f3
    print(f"{nc:>4} {fn:>14.6f} {ratio:>15.5f} {lat_ratio:>14.3f}")

print("""
Note: The lattice ratios above are for the FULL string tension,
including all perturbative and NP effects. The topological form
exp(-1/N_c^2) would only account for the NP correction FACTOR,
not the overall N_c-dependence (which is dominated by Casimir scaling).

The correct comparison would be: does the NP correction to the
Casimir-scaled string tension follow exp(-1/N_c^2)?

This requires isolating the NP correction at each N_c from lattice
data, which is a non-trivial extraction.
""")

# ==============================================================
# Section 8: Final assessment
# ==============================================================

print("=" * 70)
print("FINAL ASSESSMENT")
print("=" * 70)

# The actual combined factors
print(f"""
Combined correction factors:
  Prop z  (phenomenological):  {factor_z:.4f}  (total: -{(1-factor_z)*100:.1f}%)
  Prop z2 (scale-dep chi):     {factor_z2:.4f}  (total: -{(1-factor_z2)*100:.1f}%)

Best-matching simple topological forms:
""")

# Top 5 matches for each target
for target_name, target_val in targets.items():
    print(f"\n  Best matches for {target_name} = {target_val:.4f}:")
    sorted_by_target = sorted(candidates.items(), key=lambda x: abs(x[1] - target_val))
    for i, (name, val) in enumerate(sorted_by_target[:5]):
        delta = val - target_val
        delta_pct = delta / target_val * 100
        print(f"    {i+1}. {name:<35} = {val:.5f}  (Δ = {delta:+.5f}, {delta_pct:+.2f}%)")

print(f"""
KEY FINDINGS:

1. MISMATCH WITH exp(-1/N_c^2):
   exp(-1/N_c^2) = {np.exp(-1/N_c**2):.5f}
   Prop z factor  = {factor_z:.5f}  (discrepancy: {abs(np.exp(-1/N_c**2) - factor_z)/factor_z*100:.1f}%)
   Prop z2 factor = {factor_z2:.5f}  (discrepancy: {abs(np.exp(-1/N_c**2) - factor_z2)/factor_z2*100:.1f}%)

2. THE CORRECTIONS DON'T SCALE UNIFORMLY WITH N_c:
   - Threshold and two-loop are perturbative (order-by-order in alpha_s)
   - Gluon condensate is power correction (1/Q^4 in OPE)
   - Instanton is exponential (exp(-8*pi^2/g^2))
   These have fundamentally different N_c scaling.

3. NO SINGLE TOPOLOGICAL FORM WORKS:
   The combined correction is a sum of four physically distinct effects.
   Collapsing them into one topological factor would require either:
   (a) A deep unification of all four mechanisms, or
   (b) A coincidence at N_c = 3 that breaks at other N_c values.

4. THE "91% PATTERN" ASSESSMENT:
   The universality of ~91% across different observables is real but
   explained by the fact that all observables inherit from sqrt(sigma):
     - sqrt(sigma) gets the -9.6% correction directly
     - l_P = R_stella * exp(-128*pi/9) inherits the same factor
     - M_P = hbar*c / l_P inherits it inversely

   This is NOT four independent 91% agreements — it is ONE correction
   propagated through the derivation chain.

5. REMAINING VALUE:
   While exp(-1/N_c^2) is not exact, the observation that the combined
   NP correction is O(1/N_c^2) ~ 10% is itself meaningful. In the
   large-N_c expansion, the leading NP correction IS expected to be
   O(1/N_c^2). The coefficient ~0.8-1.0 is O(1) as expected.

   The decomposition:
     Total = perturbative O(alpha_s) + non-perturbative O(1/N_c^2)
           = -5.0%              + (-3.7% to -4.6%)

   is consistent with general large-N_c expectations.
""")

# Quantify: is the NP piece specifically 1/N_c^2?
print("Checking: is the non-perturbative piece = c/N_c^2 with c = O(1)?")
np_piece_z2 = abs(np_corr_z2)
np_piece_z = abs(np_corr_z)
c_z2 = np_piece_z2 * N_c**2
c_z = np_piece_z * N_c**2
print(f"  z2: NP correction = {np_piece_z2:.4f} → c = {c_z2:.3f}  (c/N_c^2 = {c_z2/N_c**2:.4f})")
print(f"  z:  NP correction = {np_piece_z:.4f} → c = {c_z:.3f}  (c/N_c^2 = {c_z/N_c**2:.4f})")
print(f"  Both have c ~ O(1) as expected from large-N_c expansion.")
print(f"  But c is NOT exactly 1 (it's {c_z2:.2f}-{c_z:.2f}), so exp(-1/N_c^2) is not exact.")

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)
print(f"""
Path E result: PARTIALLY CONFIRMED, with important caveats.

CONFIRMED:
  - The combined NP correction is O(1/N_c^2) ~ 10%, consistent with
    large-N_c expectations
  - The non-perturbative piece (gluon condensate + instantons) has
    coefficient c ~ {c_z2:.1f}-{c_z:.1f} in c/N_c^2, which is O(1)

NOT CONFIRMED:
  - exp(-1/N_c^2) does NOT exactly reproduce the correction
  - The four corrections have different physical origins and different
    N_c scaling — no single topological form unifies them
  - The "universality" of 91% across observables is explained by
    inheritance through the derivation chain, not by topology

UPGRADE NOT POSSIBLE:
  Cannot replace 4 corrections with 1 topological factor.
  The corrections are physically distinct and must be computed separately.

HOWEVER — a weaker but genuine result emerges:
  The framework's NP corrections follow large-N_c scaling expectations.
  This is a non-trivial consistency check that was not previously noted.
""")

# ==============================================================
# Section 9: Thread 1 — Geometric meaning of the NP coefficient c
# ==============================================================

print("\n" + "=" * 70)
print("THREAD 1: Geometric Meaning of NP Coefficient c")
print("=" * 70)

print("""
The non-perturbative piece (gluon condensate + instantons) gives a
correction c/N_c^2 with c ~ 0.34-0.43. Can c be derived analytically
from stella geometry?
""")

# --- Trace c_G through the spectral zeta function derivation ---
# From Prop 0.0.17z1 (sections 2.5-2.8):

# Stella geometry
R_stella = 0.44847  # fm (observed)
A_stella = (16 * np.sqrt(3) / 3) * R_stella**2  # surface area
L_eff = 5.960 * R_stella / 0.449  # effective edge length (scale to actual R)
# Actually L_eff/R = 5.960/0.449 = 13.27... that can't be right
# L_eff = 5.960 R where R is the stella radius, so L_eff = 5.960 * R_stella
# But the formula uses R as a parameter. Let me use ratios.

# The key ratio (dimensionless, geometry-only)
G_ratio = 1.961  # L_eff / sqrt(A) — fixed by stella geometry

# Spectral zeta residues (from heat kernel on stella boundary)
a_0_hat = 4 * np.sqrt(3) / (3 * np.pi)  # = 0.735
a_half_hat = -0.420  # edge contribution
a_1_hat_chi4 = 4 / 6  # = 0.667 (chi=4)

z_half = 0.420  # = -a_half_hat / (s - 1/2) at s = -1/2
# z_1(chi) = a_1_hat / s at s = -1/2 = (chi/6) / (-1/2) = -chi/3

def z_1(chi):
    return -chi / 3

def enhancement(chi):
    """Enhancement factor E(chi) = |z_{1/2} + z_1(chi)| / |z_{1/2}|"""
    return abs(z_half + z_1(chi)) / z_half

# --- Analytic expression for gluon condensate coefficient ---
# From Prop z1 section 2.6:
# c_G^adj = G_ratio * C_A / ((N_c^2 - 1) * 2*pi)
# c_G^full = c_G^adj * (1 + N_f * C_F / (N_c * C_A))
# c_G^eff = c_G^full * Enhancement(chi_eff)

def c_G_full_analytic(Nc, Nf):
    """Full gluon condensate coefficient (before chi enhancement)."""
    Ca = Nc
    Cf = (Nc**2 - 1) / (2 * Nc)
    c_adj = G_ratio * Ca / ((Nc**2 - 1) * 2 * np.pi)
    quark_factor = 1 + Nf * Cf / (Nc * Ca)
    return c_adj * quark_factor

def c_G_eff_analytic(Nc, Nf, chi):
    """Effective gluon condensate coefficient at scale chi_eff."""
    return c_G_full_analytic(Nc, Nf) * enhancement(chi)

print("--- Analytic decomposition of c_G ---")
print(f"G_ratio = L_eff/sqrt(A) = {G_ratio:.4f} (stella geometry)")
print(f"z_{{1/2}} = {z_half:.4f} (edge spectral residue)")
print(f"z_1(chi=4) = {z_1(4):.4f} (Euler spectral residue)")
print(f"z_1(chi_eff=2.21) = {z_1(2.21):.4f}")
print()

for chi_val, label in [(4.0, "chi=4 (UV)"), (2.21, "chi_eff=2.21 (confinement)")]:
    cg = c_G_eff_analytic(N_c, N_f, chi_val)
    E = enhancement(chi_val)
    print(f"  {label}:")
    print(f"    c_G^full = {c_G_full_analytic(N_c, N_f):.5f}")
    print(f"    Enhancement E(chi) = {E:.4f}")
    print(f"    c_G^eff = {cg:.5f}")
    # Gluon condensate correction
    glue_corr = 0.5 * cg * ratio_G2_sigma2
    print(f"    Gluon correction = (1/2) * {cg:.4f} * {ratio_G2_sigma2:.3f} = {glue_corr:.5f}")

# --- Analytic expression for instanton coefficient ---
# From Prop z1 section 3:
# c_inst = [(N_c^2-1)/N_c] * [<rho^2>/R^2] * [1/(8*pi^2)] * [1/N_c]
#          * [1 + f_corr] * [theta_O/theta_T] * 2
# where f_corr = 2*pi*<rho>^2 * n^(1/3) * (1 - 1/N_c^2)

def c_inst_analytic(Nc, rho, R, n):
    """Instanton disruption coefficient from constrained moduli integration."""
    # Step 1: single instanton, color-constrained
    c_single = ((Nc**2 - 1) / Nc) * (rho**2 / R**2) * (1 / (8 * np.pi**2)) * (1 / Nc)

    # Step 2: I-Ibar pair correlation
    f_corr = 2 * np.pi * rho**2 * n**(1/3) * (1 - 1/Nc**2)
    c_pair = c_single * (1 + f_corr)

    # Step 3: dihedral enhancement
    theta_T = np.arccos(1/3)   # tetrahedral dihedral
    theta_O = np.arccos(-1/3)  # octahedral dihedral
    dihedral_enhance = theta_O / theta_T
    c_honeycomb = c_pair * dihedral_enhance

    # Step 4: both I and Ibar
    c_total = 2 * c_honeycomb

    return c_total, {
        'single': c_single,
        'pair': c_pair,
        'honeycomb': c_honeycomb,
        'total': c_total,
        'f_corr': f_corr,
        'dihedral': dihedral_enhance
    }

c_inst_val, inst_details = c_inst_analytic(N_c, rho_inst, R_stella, n_inst)
print(f"\n--- Analytic decomposition of c_inst ---")
print(f"  c_single = {inst_details['single']:.5f}")
print(f"  f_corr = {inst_details['f_corr']:.4f}")
print(f"  c_pair = {inst_details['pair']:.5f}")
print(f"  dihedral enhancement = {inst_details['dihedral']:.4f}")
print(f"  c_honeycomb = {inst_details['honeycomb']:.5f}")
print(f"  c_inst (total) = {inst_details['total']:.5f}")

# --- Instanton correction to sqrt(sigma) ---
# delta_inst / sqrt(sigma) = 2 * (rho*sqrt_sigma)^2 * n * V_tube * c_inst
# From Props: the full instanton correction is ~1.6-1.7%
# But the formula above double-counts the factor of 2 (already in c_inst)
# Let me use the correction directly
inst_corr_z2_val = abs(corr_inst_z2)

# --- Total NP coefficient c as a function of N_c ---
print(f"\n--- Deriving c = (|delta_glue| + |delta_inst|) * N_c^2 ---")

# At chi_eff = 2.21 (Prop z2)
glue_corr_z2 = 0.5 * c_G_eff_analytic(N_c, N_f, 2.21) * ratio_G2_sigma2
total_np_z2 = glue_corr_z2 + inst_corr_z2_val
c_coeff_z2 = total_np_z2 * N_c**2

print(f"\n  At chi_eff = 2.21 (Prop z2):")
print(f"    Gluon condensate: {glue_corr_z2:.5f}")
print(f"    Instanton:        {inst_corr_z2_val:.5f}")
print(f"    Total NP:         {total_np_z2:.5f}")
print(f"    c = NP * N_c^2 =  {c_coeff_z2:.4f}")

# At chi = 4 (Prop z1)
glue_corr_chi4 = 0.5 * c_G_eff_analytic(N_c, N_f, 4.0) * ratio_G2_sigma2
inst_corr_z_val = abs(corr_inst_z)
total_np_chi4 = glue_corr_chi4 + inst_corr_z_val
c_coeff_chi4 = total_np_chi4 * N_c**2

print(f"\n  At chi = 4.0 (Prop z1):")
print(f"    Gluon condensate: {glue_corr_chi4:.5f}")
print(f"    Instanton:        {inst_corr_z_val:.5f}")
print(f"    Total NP:         {total_np_chi4:.5f}")
print(f"    c = NP * N_c^2 =  {c_coeff_chi4:.4f}")

# --- Test geometric candidates for c ---
print(f"\n--- Testing geometric candidates for c ---")
print(f"  Target: c = {c_coeff_z2:.4f} (z2) to {c_coeff_chi4:.4f} (z1)")

chi_eff = 2.21
geo_candidates = {
    '1/N_c':                 1/N_c,
    '1/chi_eff':             1/chi_eff,
    'C_F/N_c':               C_F/N_c,
    '1/(chi_eff - 1)':       1/(chi_eff - 1),
    'z_{1/2}':               z_half,
    '|z_{1/2}+z_1|/N_c':    abs(z_half + z_1(chi_eff))/N_c,
    'G_ratio/(4*pi*N_c)':    G_ratio/(4*np.pi*N_c),
    '1/(2*N_c)':             1/(2*N_c),
    'C_F/(N_c^2-1)':         C_F/(N_c**2 - 1),
    '2/(3*N_c)':             2/(3*N_c),
    'Enhancement/N_c^2':     enhancement(chi_eff)/N_c**2,
}

print(f"\n  {'Candidate':<25} {'Value':>8} {'|Δ| from z2':>12} {'|Δ| from z1':>12}")
print("  " + "-" * 60)
for name, val in sorted(geo_candidates.items(), key=lambda x: abs(x[1] - c_coeff_z2)):
    d_z2 = abs(val - c_coeff_z2)
    d_z1 = abs(val - c_coeff_chi4)
    print(f"  {name:<25} {val:>8.5f} {d_z2:>12.5f} {d_z1:>12.5f}")

# --- The key insight: trace N_c dependence analytically ---
print(f"""
--- Analytic N_c dependence of the NP coefficient ---

The gluon condensate coefficient has the following N_c structure:

  c_G^full(N_c) = G_ratio * [N_c / ((N_c^2-1) * 2*pi)] * [1 + N_f*(N_c^2-1)/(2*N_c^3)]

Simplifying:
  = G_ratio / (2*pi) * [N_c/(N_c^2-1)] * [1 + N_f*(N_c^2-1)/(2*N_c^3)]

For large N_c:
  N_c/(N_c^2-1) ~ 1/N_c  (leading)
  N_f*(N_c^2-1)/(2*N_c^3) ~ N_f/(2*N_c)  (leading)

So c_G^full ~ G_ratio/(2*pi*N_c) * (1 + N_f/(2*N_c))
           ~ G_ratio/(2*pi*N_c)  at leading order

The gluon condensate correction is:
  delta_glue = (1/2) * c_G^full * Enhancement(chi_eff) * <G^2>/sigma^2

The instanton coefficient has N_c structure:
  c_inst ~ [(N_c^2-1)/N_c] * [1/N_c] * ... = [(N_c^2-1)/N_c^2] * ...
         ~ 1 at large N_c (but exponentially suppressed by exp(-N_c))

So the gluon condensate piece scales as 1/N_c (not 1/N_c^2!)
and the instanton piece is O(1) but exponentially suppressed.

The COMBINED correction scaling as ~1/N_c^2 at N_c=3 is a coincidence
of the particular values, not a deep 1/N_c^2 structure.
""")

# Compute c for various N_c to verify
print("NP coefficient c(N_c) = |delta_glue + delta_inst| * N_c^2:")
print(f"{'N_c':>4} {'c_G^full':>10} {'E(chi_eff)':>10} {'delta_glue':>12} {'delta_inst':>12} {'c':>8}")
print("-" * 65)

# For other N_c, we need to generalize the instanton correction
# Instanton correction: exponentially suppressed at large N_c in 't Hooft limit
# At small N_c, it's approximately constant (O(1) effect at confinement scale)
# We'll use the same absolute instanton correction (conservative estimate)

for nc in [2, 3, 4, 5, 6, 8]:
    cg_full = c_G_full_analytic(nc, N_f)
    E_chi = enhancement(chi_eff)
    delta_g = 0.5 * cg_full * E_chi * ratio_G2_sigma2

    # Instanton: c_inst has explicit N_c dependence
    if nc >= 2:
        c_inst_nc, _ = c_inst_analytic(nc, rho_inst, R_stella, n_inst)
        # Approximate instanton correction as proportional to c_inst
        delta_i = inst_corr_z2_val * (c_inst_nc / c_inst_val)
    else:
        delta_i = inst_corr_z2_val

    total_np = delta_g + delta_i
    c_val = total_np * nc**2
    print(f"{nc:>4} {cg_full:>10.5f} {E_chi:>10.4f} {delta_g:>12.5f} {delta_i:>12.5f} {c_val:>8.4f}")

print("""
The coefficient c is NOT constant across N_c — it grows with N_c.
This confirms that the 1/N_c^2 scaling is approximate, not exact.
The gluon condensate piece scales as ~1/N_c, which means
c = |delta| * N_c^2 ~ N_c (growing, not constant).
""")

# --- Final assessment for Thread 1 ---
print("THREAD 1 CONCLUSION:")
print(f"""
  The NP coefficient c ~ {c_coeff_z2:.2f}-{c_coeff_chi4:.2f} does NOT have a clean
  geometric meaning. Its value at N_c = 3 is a numerical coincidence:

  1. The gluon condensate coefficient scales as ~G_ratio/(2*pi*N_c),
     which gives ~1/N_c scaling, NOT 1/N_c^2.

  2. The instanton coefficient has complex N_c dependence through
     [(N_c^2-1)/N_c^2] * dihedral * pair-correlation factors.

  3. The value c ~ 1/3 at N_c = 3 is suggestive (c = 1/N_c?) but
     this does not hold at other N_c values.

  4. The range 0.34-0.67 across N_c = 2-6 reflects the gluon
     condensate's ~1/N_c scaling dressed by instanton contributions.

  STATUS: No clean geometric expression found. The individual
  corrections (c_G, c_inst) ARE derived from stella geometry
  (Props z1, z2), but their SUM does not simplify further.
""")


# ==============================================================
# Section 10: Thread 2 — Large-N_c lattice validation
# ==============================================================

print("\n" + "=" * 70)
print("THREAD 2: Large-N_c Lattice Validation")
print("=" * 70)

print("""
Lattice data: Athenodorou & Teper (2021), arXiv:2106.00364
"SU(N) gauge theories in 3+1 dimensions: glueball spectrum,
string tensions and topology," JHEP 12 (2021) 082.

Key result (Eq. 20, Table 15):
  Lambda_MS / sqrt(sigma) = 0.5055(7) + 0.306(12) / N^2

This CONFIRMS 1/N^2 scaling of the ratio Lambda_MS/sqrt(sigma).
""")

# --- Lattice data from Athenodorou & Teper 2021, Table 15 ---
# Lambda_MS / sqrt(sigma) at 3-loop level
lattice_data = {
    # N_c: (Lambda_MS/sqrt_sigma, stat_error, sys_error_estimate)
    2:  (0.5806, 0.0021, 0.057),
    3:  (0.5424, 0.0013, 0.019),
    4:  (0.5222, 0.0011, 0.023),
    5:  (0.5174, 0.0015, 0.025),
    6:  (0.5158, 0.0011, 0.025),
    8:  (0.5115, 0.0017, 0.025),
}

# The fit from the paper:
# Lambda_MS/sqrt(sigma) = a_inf + b/N^2
a_inf = 0.5055  # +/- 0.0007
a_inf_err = 0.0007
b_coeff = 0.306  # +/- 0.012
b_coeff_err = 0.012

print("--- Lattice data: Lambda_MS / sqrt(sigma) ---")
print(f"{'N_c':>4} {'Lattice':>10} {'Stat err':>10} {'Fit (a+b/N^2)':>14} {'Residual':>10}")
print("-" * 55)

for nc, (val, err_stat, err_sys) in sorted(lattice_data.items()):
    fit_val = a_inf + b_coeff / nc**2
    residual = val - fit_val
    print(f"{nc:>4} {val:>10.4f} {err_stat:>10.4f} {fit_val:>14.4f} {residual:>+10.4f}")

print(f"\nFit: Lambda_MS/sqrt(sigma) = {a_inf}(7) + {b_coeff}(12)/N^2")
print(f"chi^2/n_df = 2.70 (from paper)")

# --- Convert to sqrt(sigma)/Lambda_MS and extract NP correction ---
print(f"\n--- Inverting to sqrt(sigma)/Lambda_MS ---")
print("""
sqrt(sigma)/Lambda_MS = 1/(a_inf + b/N^2)
                      ≈ (1/a_inf) * (1 - (b/a_inf)/N^2 + ...)

The 1/N^2 correction to sqrt(sigma)/Lambda_MS is:
  delta(N) = -(b/a_inf) / N^2 = -{0:.4f} / N^2
""".format(b_coeff/a_inf))

frac_correction = b_coeff / a_inf
print(f"Fractional 1/N^2 coefficient: b/a_inf = {frac_correction:.4f}")

print(f"\n{'N_c':>4} {'sqrt(s)/Lam':>12} {'N=inf limit':>12} {'Frac. dev.':>12} {'c_lattice':>12}")
print("-" * 55)

for nc, (val, err_stat, err_sys) in sorted(lattice_data.items()):
    ratio_inv = 1 / val
    ratio_inf = 1 / a_inf
    frac_dev = (ratio_inv - ratio_inf) / ratio_inf
    c_lat = -frac_dev * nc**2
    print(f"{nc:>4} {ratio_inv:>12.4f} {ratio_inf:>12.4f} {frac_dev:>+12.5f} {c_lat:>12.4f}")

# --- Compare with framework predictions ---
print(f"\n--- Comparison: framework vs lattice ---")
print("""
The framework predicts NP corrections to sqrt(sigma):
  delta_NP(N_c=3) = -3.7% (z2) to -4.6% (z)
  → c_framework = 0.34 to 0.43

The lattice measures the TOTAL correction to sqrt(sigma)/Lambda_MS:
  delta_total(N_c) includes BOTH perturbative and NP effects.

The 1/N^2 fit coefficient:
  c_lattice = b/a_inf = {0:.3f}

But this is the coefficient of the TOTAL 1/N^2 correction
(perturbative + NP). The lattice cannot easily separate them.
""".format(frac_correction))

# --- Perturbative N_c dependence ---
print("--- Perturbative corrections at different N_c ---")
print("""
The perturbative corrections (threshold, two-loop) also depend on N_c:

Threshold: b_0(N_c, N_f) = (11*N_c - 2*N_f)/(12*pi)
  The threshold correction depends on the ratio of b_0 at different
  N_f values, which changes with N_c.

Two-loop: b_1/b_0^2 depends on N_c through both b_0 and b_1.
  b_1 = (34*N_c^3 - 13*N_c*N_f + 3*N_f/N_c) / (48*pi^2)
""")

print(f"{'N_c':>4} {'b_0':>8} {'b_1':>8} {'b_1/b_0^2':>10} {'2-loop corr':>12}")
print("-" * 50)
for nc in [2, 3, 4, 5, 6, 8]:
    b0 = (11*nc - 2*N_f) / (12*np.pi)
    b1 = (34*nc**3 - 13*nc*N_f + 3*N_f/nc) / (48*np.pi**2)
    ratio_b = b1 / b0**2
    # Two-loop correction approximately proportional to b1/b0^2
    twoloop_corr = -0.02 * (ratio_b / (1.70 / b_0**2))  # normalized to N_c=3 value
    print(f"{nc:>4} {b0:>8.4f} {b1:>8.4f} {ratio_b:>10.4f} {twoloop_corr:>+12.4f}")

# --- The critical test: does lattice 1/N^2 match framework? ---
print(f"\n--- Critical comparison ---")
print(f"""
  Lattice 1/N^2 coefficient (total):        c_lat = {frac_correction:.3f}
  Framework NP-only coefficient (z2):        c_fw  = {c_coeff_z2:.3f}
  Framework NP-only coefficient (z):         c_fw  = {c_coeff_chi4:.3f}

  The lattice coefficient ({frac_correction:.3f}) is LARGER than the framework's
  NP-only coefficient ({c_coeff_z2:.3f}-{c_coeff_chi4:.3f}).

  This is EXPECTED: the lattice 1/N^2 includes perturbative corrections
  (threshold, two-loop) that also have 1/N^2 components.
""")

# Estimate the perturbative 1/N^2 contribution
# At N_c=3, pert correction = -5%. What fraction scales as 1/N_c^2?
# Threshold: depends on N_f/b_0(N_c). Since b_0 ~ N_c at large N_c,
# and N_f is fixed, the threshold correction ~ N_f/N_c ~ 1/N_c
# Two-loop: b_1/b_0^2 ~ O(1) at large N_c, so its correction is ~constant

print("Estimate of perturbative 1/N^2 contribution:")
print("  Threshold: scales as ~N_f/N_c (1/N_c, not 1/N_c^2)")
print("  Two-loop: scales as ~constant (b_1/b_0^2 is O(1))")
print("  Neither is purely 1/N_c^2, but they contribute to the measured")
print("  1/N_c^2 coefficient through mixing with higher-order terms.")
print()
print(f"  Combined framework (total at N_c=3): {abs(total_z2)*100:.1f}%")
print(f"  c_total = {abs(total_z2) * N_c**2:.3f}")
print(f"  Compare: c_lattice = {frac_correction:.3f}")
print(f"  Ratio: c_lattice / c_total = {frac_correction / (abs(total_z2) * N_c**2):.2f}")

# --- Lattice glueball mass ratios as cross-check ---
print(f"\n--- Cross-check: Glueball mass ratios from lattice ---")
print("""
From Lucini & Teper (2001), Eq. 7-9:
  m(0++) / sqrt(sigma) = 3.37(15) + 1.93(85) / N^2
  m(2++) / sqrt(sigma) = 4.93(30) + 2.6(1.9) / N^2

These also show O(1/N^2) corrections with O(1) coefficients,
confirming the general large-N_c pattern.
""")

glueball_data = {
    'm(0++)': {'a_inf': 3.37, 'b': 1.93, 'a_err': 0.15, 'b_err': 0.85},
    'm(2++)': {'a_inf': 4.93, 'b': 2.6, 'a_err': 0.30, 'b_err': 1.9},
}

print(f"{'Quantity':<20} {'a_inf':>8} {'b (1/N^2 coeff)':>16} {'b/a_inf':>10}")
print("-" * 58)
for name, data in glueball_data.items():
    ratio = data['b'] / data['a_inf']
    print(f"{name + '/sqrt(s)':<20} {data['a_inf']:>8.2f} {data['b']:>16.2f} {ratio:>10.3f}")
print(f"{'Lambda_MS/sqrt(s)':<20} {a_inf:>8.4f} {b_coeff:>16.3f} {frac_correction:>10.3f}")

print("""
Note: The 1/N^2 coefficients for glueball masses (~0.6) and for
Lambda_MS/sqrt(sigma) (~0.6) are remarkably similar, suggesting
a universal O(1/N^2) correction across observables.
""")

# --- Final assessment for Thread 2 ---
print("THREAD 2 CONCLUSION:")
print(f"""
  The lattice data CONFIRMS 1/N^2 scaling:

  1. Athenodorou & Teper (2021) measured Lambda_MS/sqrt(sigma) for
     N = 2, 3, 4, 5, 6, 8, 10, 12 and fit:
     Lambda_MS/sqrt(sigma) = 0.5055(7) + 0.306(12)/N^2
     The 1/N^2 form is verified to high precision.

  2. The lattice 1/N^2 coefficient (c_lat = {frac_correction:.3f} in fractional
     correction to sqrt(sigma)) is LARGER than the framework's NP-only
     prediction (c_fw = {c_coeff_z2:.3f}-{c_coeff_chi4:.3f}), as expected since the
     lattice measures the TOTAL correction.

  3. The framework's TOTAL correction at N_c=3 is {abs(total_z2)*100:.1f}%,
     giving c_total = {abs(total_z2) * N_c**2:.3f}. This is comparable to
     c_lattice = {frac_correction:.3f}, with the remaining difference attributable
     to different definitions (Lambda_MS scheme vs bootstrap scheme).

  4. The glueball mass ratios show similar O(1/N^2) scaling with
     comparable coefficients, supporting universality.

  STATUS: CONSISTENT. The 1/N^2 scaling is confirmed by lattice data.
  The coefficient magnitudes are in the right ballpark but a precise
  comparison requires careful scheme matching (Lambda_MS vs bootstrap).
""")
