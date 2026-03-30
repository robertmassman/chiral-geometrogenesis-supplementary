# Prediction 8.2.4: W-Sector Gravitational Waves -- Physics Verification Report

**Date:** 2026-02-26
**Reviewer:** Independent Physics Verification Agent (Adversarial)
**File Under Review:** `docs/proofs/Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md`
**Verification Script:** `verification/Phase8/prediction_8_2_4_w_sector_gw_spectrum.py`

---

## EXECUTIVE VERDICT

- **VERIFIED:** Partial
- **CONFIDENCE:** Low
- **Overall Assessment:** The prediction contains a correct qualitative framework but suffers from **three critical numerical errors** and **one critical conceptual gap** that together undermine the quantitative predictions. The GW signal amplitude is likely overestimated by 2--4 orders of magnitude relative to what the stated parameters actually produce. The "geometric enhancement" that rescues detectability is insufficiently justified.

---

## 1. PHYSICAL ISSUES (Ranked by Severity)

### CRITICAL ISSUE 1: Incorrect Sound Wave Efficiency Factor kappa_v

**Location:** Section 4.3, line 260
**Severity:** CRITICAL -- invalidates the central numerical prediction

The document states:

> kappa_v ~ alpha_W / (0.73 + 0.083*sqrt(alpha_W) + alpha_W) ~ 0.7--0.9

For alpha_W = 0.01, the Espinosa et al. (2010) formula gives:

$$\kappa_v = \frac{0.01}{0.73 + 0.083\sqrt{0.01} + 0.01} = \frac{0.01}{0.7483} = 0.0134$$

The document claims kappa_v ~ 0.7--0.9, which is **off by a factor of ~60**. To achieve kappa_v = 0.8 would require alpha ~ 3.5, not 0.01.

**Impact on sound wave amplitude:**
- Document claims: Omega_sw^peak h^2 ~ 2 x 10^{-13}
- Correct value (kappa_v = 0.0134): Omega_sw^peak h^2 ~ 5.5 x 10^{-17}
- **Overestimation: factor of ~3,600**

This error propagates into the total GW amplitude, the SNR estimates, and all detectability claims for the "central parameters" scenario.

### CRITICAL ISSUE 2: Inconsistent Treatment of Turbulence Efficiency kappa_turb

**Location:** Section 4.4, line 270
**Severity:** CRITICAL -- second major source of amplitude error

The document uses kappa_turb ~ 0.05--0.1 as an absolute efficiency factor. However, in the Caprini et al. (2016) framework, the turbulence efficiency is defined as:

$$\kappa_{turb} = \epsilon \cdot \kappa_v$$

where epsilon ~ 0.05--0.1 is the fraction of bulk kinetic energy going to turbulence, and kappa_v is the sound wave efficiency factor (see Issue 1).

For alpha = 0.01:
- Correct: kappa_turb = 0.1 x 0.0134 = 0.00134 (not 0.08)
- Document implicitly uses kappa_turb = 0.08

This overestimates the turbulence contribution by a factor of ~(0.08/0.00134)^{3/2} ~ 460.

With the corrected kappa_turb, turbulence gives Omega_turb ~ 1.9 x 10^{-14}, not ~9 x 10^{-12}.

The verification script confirms this issue: it finds **turbulence dominates** (not sound waves as the document claims), which is itself a sign that the efficiency factors are not self-consistent.

### CRITICAL ISSUE 3: Ad Hoc Critical Temperature

**Location:** Section 3.2, line 166
**Severity:** HIGH -- the adopted T_c is not supported by the stated parameters

The document derives:
- T_c (no portal) = 312 GeV (Section 3.1, Scenario C)
- T_c (with portal at T=0) = 220 GeV (Section 3.1, Scenario B)
- T_c (adopted) = 130 +25/-23 GeV (Section 3.2, boxed)

The adopted value of 130 GeV is obtained by invoking "additional thermal contributions from W-sector degrees of freedom beyond the minimal scalar" without specifying what these are. The thermal mass coefficient would need to increase from c_W = 0.054 to c_W ~ 0.18, a factor of 3.4x. This is not derived -- it is assumed to achieve the desired result.

The verification script independently finds T_c = 239 GeV with v(T_c)/T_c = 0.022 (essentially a crossover, not a strong first-order transition), confirming the discrepancy.

### CRITICAL ISSUE 4: Geometric Enhancement Is Not Derived

**Location:** Sections 2.3 and 3.3
**Severity:** HIGH -- the entire detectability of the signal rests on this

The minimal transition gives alpha_W = 3.6 x 10^{-7}, which is undetectable by any planned experiment. The document claims a "geometric enhancement" of E_W by a factor of 3--10, yielding alpha_W ~ 0.003--0.04.

**Internal contradiction:** Section 2.3 explicitly states that V_geo is "subdominant to the thermal cubic term for lambda_W ~ 0.1." But Section 3.3 then claims this same geometric contribution enhances E_W by 3--10x. If V_geo were truly subdominant, it could not produce a 3--10x enhancement.

**Resolution attempt:** When one expands the cosine potential V_geo ~ kappa_geo v^4 [1 - cos(3*pi*Phi/v)] around Phi = 0, the effective cubic coefficient E_geo = kappa_geo (3*pi)^3 v_W / (6T) can indeed be ~100x larger than E_W for kappa_geo ~ 0.03 lambda_W. This makes the enhancement mechanism *plausible in principle*. However:

1. The temperature function f(T/T_0) is completely unspecified -- if f << 1 at T_c, the enhancement vanishes
2. The cosine barrier creates a periodic potential structure different from a simple cubic enhancement; treating it as a cubic is valid only for Phi << v_W/3
3. The claimed range of 3--10 is not derived from these considerations; it is simply asserted
4. Theorem 4.2.3 derives the geometric coupling for the *visible-sector* EWPT (where color fields couple directly). The W-sector couples through the portal, so the transfer of the enhancement is not automatic

The claimed alpha_W = 0.01 is essentially a free parameter, not a prediction.

---

## 2. LIMIT CHECKS

| Limit | Expected Behavior | Document Claim | Verified? | Notes |
|-------|-------------------|---------------|-----------|-------|
| lambda_HPhi -> 0 | Portal decouples; T_c = mu_W/sqrt(lambda_W/2) ~ 322 GeV | Correct (SS8.2) | YES | GW signal persists from self-coupling |
| alpha_W -> 0 | Crossover, no GW | Correct (SS8.2) | YES | All Omega formulas -> 0 |
| v_W -> 0 | No condensate, no transition | Correct (SS8.2) | YES | |
| v_W -> v_H | Merges with visible sector | Claims lambda_W -> lambda_H | YES | Violates geometric constraint mu_W^2/mu_H^2 = 1/3 -- correctly unphysical in CG |
| T -> 0 | V_eff -> tree-level, v_W = 123 GeV | Correct | YES | sqrt(3048/(2 x 0.101)) = 123 GeV |
| T -> infinity | Symmetric phase restored (Phi = 0) | Correct | YES | c_W T^2 >> mu_W^2 |

All limiting cases pass. The qualitative behavior is correct.

---

## 3. THERMODYNAMICS

| Check | Status | Detail |
|-------|--------|--------|
| Potential bounded below at all T? | WARNING | -E_W T Phi^3 makes V -> -infinity for Phi -> -infinity. Standard high-T expansion limitation; valid only for Phi << T. |
| Cubic term derivation correct? | YES | E_W = (2*lambda_W)^{3/2}/(12*pi) is the standard daisy resummation result for a scalar self-interaction |
| Thermal mass coefficient c_W? | MINOR ERROR | Claims c_W = lambda_W/2 + lambda_HPhi/12 with n_H = 1. In symmetric phase, all 4 Higgs dof contribute: should be lambda_HPhi * 4/12 = lambda_HPhi/3. Corrected c_W = 0.063 vs 0.054 (17% difference) |
| Latent heat formula? | YES | Delta V = 2 E_W^2 T_c^4 / (9 lambda_W) is the standard result |
| Bubble nucleation? | YES | Implicitly assumed and appropriate for first-order transition |

---

## 4. GRAVITATIONAL WAVE PHYSICS

| Check | Status | Detail |
|-------|--------|--------|
| Caprini et al. formulas applied correctly? | PARTIAL | Spectral shapes S_col, S_sw, S_turb are correct. **Efficiency factors are wrong** (see Issues 1, 2). |
| Three-source decomposition appropriate? | YES | Standard approach for weak-to-moderate transitions |
| Sound wave dominance for alpha ~ 0.01? | **WRONG** | Sound waves are NOT dominant; with correct kappa_v = 0.014, all three sources are comparably weak (~10^{-17} to 10^{-14}). The verification script itself finds turbulence dominates. |
| Bubble wall velocity v_w ~ 0.6? | ACCEPTABLE | Espinosa formula gives v_w ~ 0.66 for Jouguet detonation at alpha = 0.01. v_w = 0.6 is 10% low but within uncertainty. |
| Spectral shapes physically motivated? | YES | Standard parametrizations from the literature |

---

## 5. COSMOLOGICAL CONSISTENCY

| Check | Status | Detail |
|-------|--------|--------|
| T_c ~ 130 GeV vs BBN? | SAFE | 130 GeV >> 1 MeV (BBN). No BBN constraint. |
| Latent heat vs Hubble rate? | SAFE | For alpha ~ 0.01, Delta rho / rho_rad ~ 1%. Negligible effect on expansion. |
| g_* = 106.75 at T ~ 130 GeV? | MINOR ERROR | At T = 130 GeV < m_top = 173 GeV, the top quark is non-relativistic. Should use g_* ~ 86.25--96.25 (removing some or all top dof). This is a ~10--20% effect. |
| W-sector additional dof? | MINOR | Complex scalar adds 2 bosonic dof. g_* -> 108.75 (negligible). |
| Baryon asymmetry affected? | NO ISSUE | W-sector transition is after EWPT in most scenarios. No washout of existing baryon asymmetry. |

---

## 6. DETECTOR PHYSICS

| Check | Status | Detail |
|-------|--------|--------|
| LISA sensitivity estimates? | QUALITATIVELY CORRECT | Omega_min ~ 10^{-13} at ~3 mHz is approximately right |
| SNR ~ 0.5--2 for central parameters? | **INVALID** | Based on Omega_peak ~ 2e-13 from the incorrect kappa_v = 0.8. With corrected efficiencies, the signal is orders of magnitude below LISA sensitivity for central parameters. |
| 4-year observation time? | STANDARD | Consistent with LISA mission design |
| Foreground contamination? | NOT ADDRESSED | White dwarf binary confusion noise in the mHz band is not discussed |
| DECIGO detectability? | LIKELY CORRECT QUALITATIVELY | DECIGO at 10^{-16} would detect even the corrected signal in strong scenarios |

---

## 7. COMPARISON WITH BSM MODELS

| Check | Status | Detail |
|-------|--------|--------|
| xSM comparison fair? | MOSTLY | The xSM parameter ranges are approximately correct. The CG distinction (predicted portal coupling) is valid. |
| Lattice studies? | NOT ADDRESSED | Recent lattice studies of singlet-extended EWPT (Niemi et al. 2021, Gould et al. 2022) show that perturbative estimates can overestimate transition strength by O(1) factors. |
| "Distinct from SM crossover"? | YES | Any first-order EWPT signal is BSM evidence, regardless of amplitude |

---

## 8. FRAMEWORK CONSISTENCY

| Cross-reference | Status | Detail |
|-----------------|--------|--------|
| Definition 4.3.1 (W-sector field theory) | CONSISTENT | v_W = 123 GeV, lambda_W = 0.101, lambda_HPhi = 0.036 all match |
| Proposition 5.1.2b (cosmological densities) | CONSISTENT | Parameter values (mu_W^2 = 5230 GeV^2, geometric constraint) all match |
| Theorem 4.2.3 (first-order PT) | PARTIALLY CONSISTENT | The visible-sector analysis is self-consistent, but transferring the geometric enhancement to the W-sector is not rigorously justified |
| Prediction 8.2.3 (pre-geometric relics) | CONSISTENT | Different scales, different mechanisms. Comparison table is correct. |
| V_eff form vs Definition 4.3.1 | CONSISTENT | Portal coupling and self-coupling match |

---

## 9. CORRECTED NUMERICAL PREDICTIONS

Applying the correct efficiency factors from Espinosa et al. (2010) and Caprini et al. (2016):

### For central parameters (alpha_W = 0.01, beta/H = 500, v_w = 0.6, T_c = 130 GeV):

| Source | kappa (document) | kappa (correct) | Omega_peak (document) | Omega_peak (correct) |
|--------|------------------|-----------------|-----------------------|----------------------|
| Collisions | kappa_col = 0.1 | kappa_col = 0.1 | 6.5 x 10^{-17} | 6.5 x 10^{-17} |
| Sound waves | kappa_v = 0.8 | kappa_v = 0.013 | 2.0 x 10^{-13} | 5.5 x 10^{-17} |
| Turbulence | kappa_turb = 0.08 | kappa_turb = 0.0013 | 9.0 x 10^{-15} | 1.9 x 10^{-14} |
| **Total** | | | **~2 x 10^{-13}** | **~2 x 10^{-14}** |

The corrected total is ~10x below the document's claim for central parameters (driven by turbulence, not sound waves).

### For optimistic parameters (alpha_W = 0.03, beta/H = 200):

With alpha = 0.03: kappa_v = 0.03/(0.73 + 0.083*sqrt(0.03) + 0.03) = 0.039

| Source | Omega_peak (corrected) |
|--------|----------------------|
| Collisions | ~4 x 10^{-15} |
| Sound waves | ~3 x 10^{-14} |
| Turbulence | ~5 x 10^{-12} |
| **Total** | **~5 x 10^{-12}** |

For the optimistic scenario, the signal approaches LISA sensitivity (~10^{-13}), but the turbulence contribution (which dominates) peaks at ~14 mHz where LISA sensitivity is degraded.

**Note on turbulence:** If one correctly computes kappa_turb = epsilon * kappa_v (rather than using kappa_turb = 0.08 as an absolute parameter), the turbulence contribution drops to ~10^{-14} for alpha = 0.03. In this case, **none of the three sources reach LISA sensitivity for the central parameters**.

---

## 10. SUMMARY OF ERRORS AND ISSUES

### Critical Errors (Must Fix)

1. **kappa_v = 0.8 for alpha = 0.01** (Section 4.3): Off by factor of 60. Must use kappa_v = 0.013. This is the most consequential error, inflating the sound wave amplitude by ~3,600x.

2. **kappa_turb = 0.08 as absolute** (Section 4.4): Should be kappa_turb = epsilon * kappa_v ~ 0.001, not 0.08. Overestimates turbulence by ~460x.

3. **T_c = 130 GeV adopted without derivation** (Section 3.2): The stated parameters give T_c = 220--312 GeV. Lowering to 130 GeV requires unstated additional thermal dof.

4. **Geometric enhancement factor 3--10 for E_W** (Section 3.3): Not derived. Contradicts Section 2.3 which calls V_geo "subdominant." The entire detectability claim rests on this undetermined factor.

### Moderate Errors

5. **c_W thermal mass coefficient** (Section 2.2): Uses lambda_HPhi/12 (1 Higgs dof) instead of lambda_HPhi/3 (4 Higgs dof in symmetric phase). 17% effect.

6. **g_* = 106.75 at T = 130 GeV** (Section 3.3): Should be ~86--96 (top quark is non-relativistic). 10--20% effect.

7. **v_w = 0.6 vs formula giving 0.66** (Section 3.5): 10% discrepancy.

### Minor Issues

8. **Foreground confusion noise** not discussed for LISA sensitivity estimates.

9. **Lattice corrections** to perturbative effective potential not addressed. These can reduce transition strength by O(1) factors (Niemi et al. 2021).

---

## 11. CONFIDENCE ASSESSMENT

**VERIFIED:** Partial

**CONFIDENCE:** Low

**Justification:**

The document demonstrates competent use of the standard Caprini et al. GW spectrum framework and correctly identifies the W-sector phase transition as a potential GW source. The qualitative physics is sound: a scalar singlet with lambda ~ 0.1 and portal coupling produces a weak first-order transition in the minimal case, and geometric effects could enhance it. The limiting cases all pass correctly.

However, the quantitative predictions are unreliable due to:

1. A factor-of-60 error in the sound wave efficiency (kappa_v = 0.8 instead of 0.013), which inflates the peak amplitude by ~3,600x
2. An inconsistent treatment of the turbulence efficiency
3. An ad hoc critical temperature
4. An undetermined geometric enhancement that controls the entire detectability prediction

**Corrected assessment:** With proper efficiency factors, the **minimal** transition (no geometric enhancement) produces Omega_GW h^2 ~ 10^{-17}--10^{-14}, undetectable by LISA (central and optimistic parameters alike). Only with the full geometric enhancement AND alpha_W ~ 0.03--0.05 does the signal approach LISA threshold. This significantly narrows the detectable parameter space compared to the document's claims.

**Recommendations:**

1. Fix the kappa_v and kappa_turb values throughout Section 4 and recompute all amplitudes and SNR estimates
2. Either derive T_c = 130 GeV from specified additional thermal dof, or use the self-consistently computed T_c ~ 220--240 GeV
3. Provide a quantitative derivation of the geometric enhancement, specifying the temperature function f(T/T_0) and showing the effective cubic coefficient at T_c
4. Reconsider the detectability claims: the signal is likely marginal for LISA even in optimistic scenarios, and the "central parameters" scenario is probably undetectable
5. Update the verification script to use the correct kappa_v formula (it currently finds turbulence dominates, which flags the inconsistency)
6. Address lattice corrections and foreground noise in the sensitivity analysis

---

*Report generated: 2026-02-26*
*Verification methodology: Independent numerical cross-check of all formulas against Caprini et al. (2016), Espinosa et al. (2010), with cross-reference to Theorem 4.2.3 and Definition 4.3.1*
