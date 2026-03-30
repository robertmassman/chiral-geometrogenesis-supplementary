# Multi-Agent Verification Report: Theorem 4.3.2 — W-Soliton Existence and Properties

**Date:** 2026-02-25
**File:** `docs/proofs/Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md`
**Agents:** Literature, Mathematics, Physics (adversarial)
**Overall Verdict:** PARTIAL VERIFICATION — Core topology and stability are sound; quantitative predictions require corrections

---

## Executive Summary

| Agent | Verdict | Confidence | Key Issues |
|-------|---------|------------|------------|
| Literature | Partial | Medium | Missing prior work (Skyrmion DM papers); Bogomolny bound mislabeled; Bullet Cluster citation outdated |
| Mathematics | Partial | Medium-High | Derrick prose reversed; instanton action dimensional error; resonance enhancement unjustified (10^8 factor) |
| Physics | Partial | Medium (65%) | EFT validity (M_W > Λ_W); resonance enhancement unjustified; symmetric component annihilation incomplete |

### Consensus Issues (Flagged by 2+ Agents)

1. **CRITICAL — Self-interaction resonance enhancement (§8.3):** All three agents flag the jump from σ/m ~ 10⁻¹² to ~10⁻⁴ cm²/g as unjustified. The ~10⁸ enhancement factor has no derivation, no reference, and no physical mechanism specified. The geometric estimate (σ/m ~ 10⁻¹² cm²/g) already satisfies all bounds.

2. **CRITICAL — EFT validity (§9.3):** M_W ≈ 1620 GeV exceeds Λ_W = 4πv_W ≈ 1546 GeV. The mass prediction is not parametrically controlled. Stated uncertainty (±180 GeV, ~11%) is underestimated; realistic range is ±500 GeV (~30%).

3. **MODERATE — Bogomolny bound mislabeling (§5.1):** The formula M = 6π²v_W/e_W is NOT the Faddeev-Bogomolny bound (which is 12π² in Skyrme units). The coefficient 6π² = 59.22 underestimates the ANW numerical result (72.92) by 19%.

4. **MODERATE — Uncertainty budget (§4.4):** The 6π² vs 72.92 discrepancy (23% shift, +374 GeV) exceeds the stated combined uncertainty of ±180 GeV.

---

## 1. Literature Verification Agent Report

### VERIFIED: Partial

### Citation Accuracy

| Reference | Status | Notes |
|-----------|--------|-------|
| Skyrme (1962), Nucl. Phys. 31, 556-569 | ✅ Correct | Foundational paper |
| Adkins, Nappi, Witten (1983), Nucl. Phys. B 228, 552-566 | ✅ Correct | ANW Skyrmion mass confirmed |
| Witten (1983), Nucl. Phys. B 223, 433-444 | ✅ Correct | Current algebra and baryons |
| Markevitch et al. (2004), ApJ 606, 819 | ⚠️ Incomplete | Original bound was σ/m < 5 cm²/g, not < 1 |
| Randall et al. (2008), ApJ 679, 1173 | ⚠️ Slightly overstated | Actual bound ~1.25 cm²/g, not exactly < 1 |

### Numerical Values Verified

| Value | Document | Verified | Status |
|-------|----------|----------|--------|
| π₃(SU(2)) = ℤ | Correct | Standard algebraic topology | ✅ |
| 1/(24π²) normalization | Correct | Standard winding number | ✅ |
| Hedgehog BCs F(0)=π, F(∞)=0 | Correct | Standard for B=1 | ✅ |
| 6π²/72.92 = 0.812 | Correct | 59.2176/72.92 = 0.8121 | ✅ |
| 1 GeV = 1.78×10⁻²⁴ g | Correct | 1.78266×10⁻²⁴ g | ✅ |
| e ≈ 4.84 (ANW) | Plausible | Convention-dependent, commonly quoted | ✅ |
| f_π = 92.1 MeV | Correct | PDG 2024, PS convention | ✅ |

### Outdated Values

| Value | Document | Current | Source |
|-------|----------|---------|--------|
| Bullet Cluster bound | σ/m < 1 cm²/g (2004/2008) | σ/m < 0.5 cm²/g (2025) | Cha et al. 2025, JWST |
| Markevitch bound | Cited as < 1 cm²/g | Actually < 5 cm²/g | Markevitch et al. 2004 |

### Missing References (Important Prior Work)

1. **Gudnason & Rishi (2017):** "Very heavy dark Skyrmions," Eur. Phys. J. C 77, 813. Hidden-sector SU(2) Skyrme DM with mass formula M_S = 73 f_w/g_V — directly comparable model.
2. **Kitano & Kurachi (2016):** "Electroweak-Skyrmion as topological dark matter," JHEP 07 (2016) 037. EW Skyrmion DM at ~34 TeV.
3. **Hamada, Kitano, Kurachi (2022):** "Electroweak-Skyrmion as asymmetric dark matter," JHEP 02 (2022) 124. Asymmetric DM from Skyrmion topology.
4. **Robertson, Massey & Eke (2017):** MNRAS 465, 569. Bullet Cluster constraint reanalysis showing larger systematic uncertainties.

### Key Finding: Bogomolny Bound Mislabeling

The Faddeev-Bogomolny bound for the Skyrme model is E ≥ 12π² |B| (in Skyrme units). The document's coefficient 6π² is exactly **half** this value and is **not** the Bogomolny bound. The formula underestimates the ANW numerical mass by 19%.

---

## 2. Mathematical Verification Agent Report

### VERIFIED: Partial (Confidence: Medium-High)

### Errors Found

| # | Location | Error | Severity |
|---|----------|-------|----------|
| 1 | §5.2 | Derrick's theorem prose REVERSED: "kinetic term favors expansion" should be "favors contraction" (and vice versa for Skyrme term). Mathematical scaling (E₂~R, E₄~1/R) is correct. | Low |
| 2 | §5.3 | Instanton suppression S ~ 4πv_W/e_W = 343 has dimensions [Energy], not dimensionless. Action in exp(-S) must be dimensionless. | Medium |

### Warnings

| # | Location | Warning | Severity |
|---|----------|---------|----------|
| 1 | §8.3 | Resonance enhancement factor ~10⁸ from σ/m ~10⁻¹² to ~10⁻⁴ cm²/g is UNJUSTIFIED. No derivation, no reference. Standard Skyrmion-Skyrmion resonance enhancement is O(10)–O(100), not O(10⁸). | **High** |
| 2 | §4.2-4.4 | Using Bogomolny bound (6π²=59.22) as mass formula when ANW gives 72.92 (+23%). The +374 GeV systematic exceeds the stated ±180 GeV uncertainty. | Medium |
| 3 | §9.3 | M_W > Λ_W means higher-order operators contribute at same order. Mass prediction not parametrically controlled. | Medium |
| 4 | §9.1 | T_f ~ M/20 is WIMP freeze-out estimate, inconsistent with ADM production mechanism stated in Def 4.3.1 §8.4. Conclusion (T_f >> T_BBN) still valid. | Low |
| 5 | §8.1 vs §8.2 | Two cross-section formulas (perturbative ~10⁻³⁵ cm² vs geometric ~10⁻³³ cm²) differ by ×370, unreconciled. | Low |

### Equations Re-derived and Verified

| Equation | Document | Independent | Status |
|----------|----------|-------------|--------|
| Topological charge normalization 1/(24π²) | ✅ | ✅ | VERIFIED |
| Hedgehog Q_W = 1 with F(0)=π, F(∞)=0 | ✅ | ✅ | VERIFIED |
| M_W = 6π² × 123/4.5 = 1619 GeV | 1619 | 1618.62 | VERIFIED |
| r_W = 1/(4.5 × 123) → 3.6×10⁻¹⁷ cm | 3.6×10⁻¹⁷ | 3.57×10⁻¹⁷ | VERIFIED |
| σ_geom = πr_W² ≈ 4×10⁻³³ cm² | 4×10⁻³³ | 3.99×10⁻³³ | VERIFIED |
| σ/m (geometric) ≈ 1.4×10⁻¹² cm²/g | 1.4×10⁻¹² | 1.38×10⁻¹² | VERIFIED |
| Derrick scaling E₂ ~ R, E₄ ~ 1/R | Correct | Correct | VERIFIED (scaling); PROSE ERROR |
| T_f = M_W/20 = 81 GeV | 81 | 81 | VERIFIED |
| S ~ 4πv_W/e_W ≈ 342 | 342 | 343.5 | VERIFIED (arithmetic); **DIMENSIONAL ERROR** |
| Resonance enhancement to 10⁻⁴ | claimed | UNJUSTIFIED | **FLAG** |

---

## 3. Physics Verification Agent Report

### VERIFIED: Partial (Confidence: Medium, 65%)

### Physical Issues

#### Critical

1. **Self-interaction resonance enhancement (§8.3):** The 10⁸ enhancement has no physical mechanism specified. Standard Skyrmion resonances produce O(10) enhancement. To get 10⁸ would require a scattering length a ~ 10⁴ × r_W, implying an extremely fine-tuned near-threshold bound state with no mechanism to produce it.

2. **EFT validity (§4, §9.3):** M_W/Λ_W ≈ 1620/1546 ≈ 1.05 — soliton mass ABOVE EFT cutoff. Compare visible sector: M_N/Λ_χ ≈ 938/1160 ≈ 0.81 (below cutoff). Higher-order operators (6-derivative terms) contribute at same order. Realistic uncertainty: M_W = 1600 ± 500 GeV.

#### Moderate

3. **Symmetric component annihilation (§9.2):** The claim "symmetric component annihilates early via portal coupling" is likely incorrect. With σv ~ 10⁻²⁸ cm³/s, thermal freeze-out gives Ωh² ~ 23 (over-abundant). For ADM, need σv >> 3×10⁻²⁶ cm³/s to remove symmetric component — two orders of magnitude too weak. Conclusion (no CMB problem) is correct for a different reason: annihilation rate too low for detectable distortion.

4. **Dynamic suspension interpretation (§7):** Must explicitly distinguish field-space confinement (pre-geometric internal structure) from physical-space localization. A dark matter particle "confined to D_W" sounds incompatible with galactic-halo-scale distribution.

5. **Bogomolny bound vs ANW mass (§4.4):** Using ANW coefficient gives M_W ≈ 1995 GeV. The 23% systematic exceeds stated uncertainties.

#### Minor

6. **T_f formula (§9.1):** Correct as BBN consistency check but misleading in ADM context.

### Limit Checks

| Limit | Behavior | Expected | Result |
|-------|----------|----------|--------|
| v_W → 0 | M_W → 0, no condensate | No soliton | ✅ PASS |
| e_W → ∞ | M_W → 0, r_W → 0 | Soliton collapses | ✅ PASS |
| e_W → 0 | M_W → ∞, no Skyrme stabilization | No stable soliton | ✅ PASS |
| λ_{HΦ} → 0 | Complete decoupling | Pure gravitational DM | ✅ PASS |
| QCD limit (v_W → f_π) | Recovers nucleon physics | With e_W ~ e ~ 4.84 | ✅ PASS |

### Experimental Tensions

| Observable | CG Prediction | Current Bound | Status |
|------------|--------------|---------------|--------|
| Direct detection σ_SI | 1.5×10⁻⁴⁷ cm² | ~1-3×10⁻⁴⁶ cm² (LZ at 1.6 TeV) | ✅ OK |
| LHC monojet | Negligible at λ=0.036 | ~10 fb | ✅ OK |
| Bullet Cluster σ/m | 10⁻¹² cm²/g (geometric) | < 0.5 cm²/g (JWST 2025) | ✅ OK |
| CMB late annihilation | σv ~ 10⁻²⁸ cm³/s | f_eff σv/M < 3.5×10⁻²⁸ cm³/s/GeV | ✅ OK |
| Higgs invisible width | Kinematically forbidden | BR < 10.7% | ✅ OK |
| Higgs signal strength | μ = 1.00 | μ = 1.00 ± 0.06 | ✅ OK |

**No experimental exclusion identified.** Most constraining future test: DARWIN/XLZD direct detection.

### Framework Consistency

| Cross-Reference | Status |
|----------------|--------|
| Theorem 4.1.1 (Soliton Existence) | ✅ Consistent — same π₃(SU(2)) = ℤ topology |
| Theorem 4.1.2 (Mass Formula) | ✅ Consistent — same formula with W-sector parameters |
| Theorem 4.1.3 (Fermion Number) | ✅ Consistent — W-soliton inherits spin-1/2 |
| Theorem 4.1.4 (Dynamic Suspension) | ✅ Consistent — parallel construction |
| Definition 4.3.1 (W-Sector Field Theory) | ✅ Consistent — all parameters match |
| Proposition 4.3.5 (Skyrme Parameter) | ✅ Consistent — e_W = 4.5 ± 0.3 |
| Proposition 5.1.2b (Self-consistent v_W) | ✅ Consistent — v_W = 123 ± 15 GeV |
| Prediction 8.3.1 (W-Condensate DM) | ⚠️ Mostly consistent — minor mass value differences |

---

## 4. Consolidated Recommendations

### Must Fix (Critical)

1. **Remove or derive the resonance enhancement (§8.3).** Replace with: report geometric cross-section σ/m ~ 10⁻¹² cm²/g as the primary result, noting this is effectively collisionless and satisfies all observational bounds by a factor of ~10¹².

2. **Fix Derrick's theorem prose (§5.2).** Swap "expansion" and "contraction": the kinetic term favors contraction (lower E₂ at smaller R); the Skyrme term favors expansion (lower E₄ at larger R).

3. **Fix instanton action dimensional issue (§5.3).** Either use the correct dimensionless action (e.g., S_Euclidean = M_W × r_W = 1620 GeV × 1/(554 GeV) ≈ 2.93, or the sphaleron-like estimate S ~ 4π/e_W² ≈ 0.62), or simply argue suppression via the large soliton energy E >> T for all relevant temperatures.

### Should Fix (Moderate)

4. **Correct Bogomolny bound label (§5.1).** The Faddeev-Bogomolny bound is 12π² (in Skyrme units), not 6π². Clarify that M = 6π²v_W/e_W is an analytic approximation, not the topological lower bound.

5. **Expand uncertainty budget (§4.4).** Include the 6π² vs 72.92 systematic as a named contribution, or switch to the ANW coefficient. The realistic mass range is M_W = 1600–2000 GeV.

6. **Update Bullet Cluster citation (§8.4).** Attribute σ/m < 1 cm²/g to Randall et al. (2008) specifically. Consider adding JWST 2025 result (σ/m < 0.5 cm²/g).

7. **Add missing Skyrmion DM references (§11).** Cite Gudnason & Rishi (2017), Kitano & Kurachi (2016), Hamada et al. (2022) to contextualize the W-soliton proposal.

8. **Clarify dynamic suspension (§7).** Explicitly state that D_W confinement is in field-theory internal space, not physical spacetime.

9. **Clarify symmetric component (§9.2).** The portal coupling alone may be insufficient to annihilate the symmetric component. Note that the CMB constraint is satisfied regardless.

### Informational (Minor)

10. **Reconcile perturbative vs geometric cross-section (§8.1-8.2).** Remove or contextualize the perturbative formula.

11. **Clarify T_f in ADM context (§9.1).** Note that T_f ~ M/20 is a consistency check for BBN, not the ADM decoupling temperature.

---

## 5. Verification Methodology

- **Literature agent:** Checked all 5 external citations against ADS/arXiv databases, verified numerical values against local reference data and web sources, searched for prior work on Skyrmion dark matter.
- **Mathematics agent:** Re-derived all key equations independently, checked dimensional analysis on every term, verified arithmetic to 4+ significant figures, traced logical dependencies.
- **Physics agent:** Tested limiting cases (v_W→0, e_W→0, e_W→∞, λ→0), checked all experimental bounds (LZ, Bullet Cluster, CMB, LHC, Higgs), verified framework consistency across 8 cross-references.

---

## 6. Computational Verification

**Adversarial physics verification script:** `verification/Phase4/theorem_4_3_2_adversarial_verification.py`
**Verification plots:** `verification/plots/theorem_4_3_2_*.png`

---

*Report generated by multi-agent adversarial review system.*
*Agents: Claude Opus 4.6 (Literature, Mathematics, Physics)*
