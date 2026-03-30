# Multi-Agent Verification Report: Proposition 4.3.4 (W-Soliton Structure Formation Compatibility)

**Date:** 2026-02-25
**Document:** `docs/proofs/Phase4/Proposition-4.3.4-W-Soliton-Structure-Formation.md`
**Agents:** Literature, Mathematical, Physics (adversarial)
**Overall Verdict:** ✅ RESOLVED — 11 issues found (2 critical, 4 significant, 5 minor); all 11 resolved on 2026-02-25.

---

## Executive Summary

All three verification agents agree that the **qualitative conclusions of Proposition 4.3.4 are correct**: W-solitons are cold, effectively collisionless dark matter compatible with all structure formation observations. However, the document contains **multiple numerical errors**, including an 8-order-of-magnitude discrepancy in the self-interaction cross-section versus the upstream Theorem 4.3.2. All errors go in the direction that *strengthens* the conclusions (the actual W-soliton is even colder and more collisionless than stated), so no qualitative claim is invalidated.

---

## Issue Tracker

| # | Severity | Section | Issue | Status |
|---|----------|---------|-------|--------|
| 1 | **CRITICAL** | §3.2 | σ/m = 2×10⁻⁴ cm²/g disagrees with Thm 4.3.2 value of 1.4×10⁻¹² cm²/g (8 orders of magnitude) | ✅ RESOLVED |
| 2 | **CRITICAL** | §2.2 | λ_fs ~ 10⁻⁶ Mpc is wrong; correct value is ~10⁻¹⁵ to 10⁻¹³ Mpc | ✅ RESOLVED |
| 3 | Significant | §2.1 | Velocity arithmetic: intermediate step assigns 4.6×10⁻¹³ to T_eq/T_f instead of product; final answer ~10⁻¹⁴ should be ~4.6×10⁻¹³ | ✅ RESOLVED |
| 4 | Significant | §3.3 | Interaction range r ≈ 0.004 fm is wrong; correct is 0.00036 fm (factor ~11 off) | ✅ RESOLVED |
| 5 | Significant | §3.1 | Markevitch et al. (2004) σ/m < 1.25 cm²/g — wrong attribution. Value is from Randall et al. (2008); Markevitch gives < 1 cm²/g | ✅ RESOLVED |
| 6 | Significant | §3.1 | Harvey et al. (2015) σ/m < 0.7 cm²/g — wrong value (actual: < 0.47 cm²/g) and revised to ~2 cm²/g by Wittman et al. (2018) | ✅ RESOLVED |
| 7 | Minor | §6.3 | Ω_W h² = 0.12 ± 0.04 misleading — Prop 4.3.3 derives 0.14 ± 0.05; table conflates observation with prediction | ✅ RESOLVED |
| 8 | Minor | §4.1 | k_fs ~ 10⁶ Mpc⁻¹ off by factor 2π; should be ≫10⁷ with corrected λ_fs | ✅ RESOLVED |
| 9 | Minor | §6.1 | ⟨σv⟩_late = 0 stated as exact; should note suppressed by δ_sym² ~ 10⁻¹² | ✅ RESOLVED |
| 10 | Minor | §9 | Missing references: Randall et al. (2008), Wittman et al. (2018), Robertson et al. (2017) | ✅ RESOLVED |
| 11 | Minor | §3.3 | Born regime claim marginal (λ_dB ~ r_W at cluster velocities) | ✅ RESOLVED |

---

## Agent 1: Literature Verification

### VERIFIED: Partial
### CONFIDENCE: Medium-High

### Citation Accuracy

| Citation | Claimed | Actual | Status |
|----------|---------|--------|--------|
| Markevitch et al. (2004) σ/m | < 1.25 cm²/g | < 1 cm²/g | **INCORRECT** — 1.25 from Randall et al. (2008) |
| Harvey et al. (2015) σ/m | < 0.7 cm²/g | < 0.47 cm²/g (95% CL) | **INCORRECT** — revised to ~2 cm²/g by Wittman et al. (2018) |
| Irsic et al. (2017) m_WDM | > 5.3 keV | > 5.3 keV | **CORRECT** (minor update: > 5.7 keV from 2024 analyses) |
| Planck Ω_c h² | 0.1200 ± 0.0012 | 0.1200 ± 0.0012 | **CORRECT** |
| Planck n_s | 0.9649 ± 0.0042 | 0.9649 ± 0.0042 | **CORRECT** |
| Planck τ | 0.054 ± 0.007 | 0.054 ± 0.007 | **CORRECT** |
| Planck H_0 | 67.4 ± 0.5 km/s/Mpc | 67.4 ± 0.5 km/s/Mpc | **CORRECT** |
| FIRAS |μ| | < 9 × 10⁻⁵ | < 9 × 10⁻⁵ | **CORRECT** |
| FIRAS |y| | < 1.5 × 10⁻⁵ | < 1.5 × 10⁻⁵ | **CORRECT** |
| CMB annihilation bound | < 3.2 × 10⁻²⁸ cm³/s/GeV | ~3.2–3.5 × 10⁻²⁸ | **APPROXIMATELY CORRECT** |
| T_eq | ~0.75 eV | ~0.75–0.93 eV | **CORRECT** (within standard range) |
| T_f = M/20 | 81 GeV | ~81 GeV | **CORRECT** |

### Missing References

1. **Randall, Markevitch, Clowe, Gonzalez & Bradac (2008)**, ApJ 679, 1173 [arXiv:0704.0261] — actual source of σ/m < 1.25 cm²/g
2. **Wittman, Golovich & Dawson (2018)**, ApJ 869, 104 [arXiv:1701.05877] — critical revision of Harvey et al.
3. **Robertson, Massey & Eke (2017)**, MNRAS 465, 569 [arXiv:1605.04307] — careful Bullet Cluster analysis
4. **Sales, Wetzel & Fattahi (2022)**, Nature Astronomy 6, 897 — baryonic solutions review

### Impact Assessment

The citation errors do not affect the scientific conclusion. W-solitons satisfy all self-interaction bounds regardless of whether the bound is 0.47, 0.7, 1.0, 1.25, or 2 cm²/g.

---

## Agent 2: Mathematical Verification

### VERIFIED: Partial
### CONFIDENCE: Medium

### Re-derived Equations

| Equation | Document Value | Re-derived Value | Status |
|----------|---------------|-----------------|--------|
| T_eq/T_f | 4.6 × 10⁻¹³ | 9.26 × 10⁻¹² | **ERROR** (factor 20) |
| T_f/M_W | 0.05 | 0.05 | CORRECT |
| v_W/c at T_eq | ~10⁻¹⁴ | 4.6 × 10⁻¹³ | **ERROR** (factor ~20) |
| λ_fs | ~10⁻⁶ Mpc | ~10⁻¹⁵ to 10⁻¹³ Mpc | **ERROR** (~9 orders of magnitude) |
| σ_WW/M_W (Prop 4.3.4) | 2 × 10⁻⁴ cm²/g | 1.4 × 10⁻¹² cm²/g | **ERROR** (10⁸ discrepancy) |
| σ_WW/M_W (Thm 4.3.2) | 1.4 × 10⁻¹² cm²/g | 1.38 × 10⁻¹² cm²/g | CORRECT |
| r_W (Prop 4.3.4) | 0.004 fm | 0.000356 fm | **ERROR** (factor ~11) |
| r_W (Thm 4.3.2) | 0.00036 fm | 0.000356 fm | CORRECT |
| k_fs | 10⁶ Mpc⁻¹ | ≫10⁷ Mpc⁻¹ | Minor (2π factor + λ_fs error) |
| ⟨σv⟩_late for ADM | 0 | ~0 (δ_sym² suppressed) | CORRECT |
| Ω_W h² | 0.12 ± 0.04 | 0.14 ± 0.05 (from Prop 4.3.3) | MISLEADING |

### Critical Issue: Self-Interaction Cross-Section

**Proposition 4.3.4 §3.2** claims σ_WW/M_W ≈ 2 × 10⁻⁴ cm²/g and attributes this to Theorem 4.3.2 §8.

**Theorem 4.3.2 §8.2** explicitly derives:
- σ_WW ≈ 4 × 10⁻³³ cm²
- σ_WW/M_W = 4 × 10⁻³³ / 2.9 × 10⁻²¹ ≈ 1.4 × 10⁻¹² cm²/g

Independent re-derivation confirms:
- r_W = ℏc/(e_W v_W) = 197.3 MeV·fm / (4.5 × 123 GeV) = 3.56 × 10⁻⁴ fm = 3.56 × 10⁻¹⁷ cm
- σ_WW = πr_W² = π × (3.56 × 10⁻¹⁷)² = 3.99 × 10⁻³³ cm²
- σ_WW/M_W = 3.99 × 10⁻³³ / 2.89 × 10⁻²¹ = 1.38 × 10⁻¹² cm²/g

The Theorem 4.3.2 value of **1.4 × 10⁻¹² cm²/g is correct**. The Proposition 4.3.4 value of 2 × 10⁻⁴ cm²/g is wrong by **8 orders of magnitude**.

### Critical Issue: Free-Streaming Length

With v/c = 4.6 × 10⁻¹³ and t_eq = 5 × 10⁴ yr:
- λ_fs = v × t_eq = 4.6 × 10⁻¹³ × c × 5 × 10⁴ yr = 2.3 × 10⁻⁸ ly ≈ 7 × 10⁻¹⁵ Mpc

Even with comoving corrections (log enhancement ~50):
- λ_fs^com ~ 50 × 7 × 10⁻¹⁵ ≈ 4 × 10⁻¹³ Mpc

The claimed 10⁻⁶ Mpc appears borrowed from generic 100 GeV WIMP estimates, not recomputed for M_W = 1620 GeV.

### Dimensional Analysis

All equations have consistent dimensions. ✅

### Logical Structure

The logical flow (CDM classification → self-interaction bounds → large-scale → small-scale → CMB) is sound. ✅

---

## Agent 3: Physics Verification

### VERIFIED: Partial
### CONFIDENCE: Medium

### Physical Issues

**1. Freeze-out vs. Kinetic Decoupling (Moderate)** — ✅ RESOLVED
The calculation uses chemical freeze-out T_f ≈ M/20 for the velocity estimate. However, kinetic decoupling (when elastic scattering ceases) typically occurs at a lower temperature T_kd < T_f. For W-solitons interacting via Higgs portal, T_kd could be significantly below 81 GeV. Using T_f instead of T_kd may underestimate the velocity by a moderate factor, but the qualitative CDM classification is unaffected given the enormous margin.
*Resolution:* §2.1 now derives T_kd ~ 0.1–40 GeV from the Higgs portal coupling λ_HΦ = 0.036 (Bringmann & Hofmann 2007 framework). Velocity and λ_fs tables show results for multiple T_kd values; even the most conservative case (T_kd ~ 0.1 GeV) gives v/c ~ 10⁻¹⁰ and λ_fs ≲ 10⁻¹⁰ Mpc.

**2. ADM Freeze-out Subtlety (Minor)** — ✅ RESOLVED
The T_f = M/20 formula applies to WIMP chemical freeze-out. For ADM, the relevant "freeze-out" is the annihilation of the symmetric component. The physics is slightly different but the temperature estimate is similar since it still requires ⟨σv⟩n ≲ H at T ~ M/20.
*Resolution:* §2.1 now explicitly notes that T_f ≈ M/20 applies to the symmetric component annihilation for ADM, with the same Boltzmann suppression as standard WIMPs.

**3. Self-Interaction Discrepancy (Critical)** — ✅ RESOLVED (Issue #1)
Same as Math Agent finding — 8 orders of magnitude between Prop 4.3.4 and Thm 4.3.2. The Thm 4.3.2 value (1.4 × 10⁻¹² cm²/g) is correct.

**4. Residual Symmetric Component (Minor)** — ✅ RESOLVED (Issue #9)
Prop 4.3.3 §4.2 gives δ_sym ~ 10⁻⁶. The residual annihilation rate is ⟨σv⟩_eff ~ δ_sym² × ⟨σv⟩₀ ~ 10⁻¹² × 10⁻²² ~ 10⁻³⁴ cm³/s, which is negligible. The claim ⟨σv⟩_late = 0 is effectively correct.

**5. Small-Scale Structure Claims (Moderate)** — ✅ RESOLVED
The assertion that baryonic feedback resolves all CDM small-scale problems represents the current majority view but is not universally accepted. The proposition should soften the language or cite the debate more carefully.
*Resolution:* §5.2 language softened ("largely attributed to", "largely addressed by", "remains debated"). Now cites Sales et al. (2022). Conclusion rephrased to note this is an active area of research and that W-solitons make no additional predictions beyond standard CDM.

**6. Mass Value Inconsistency (Moderate)** — ✅ RESOLVED
Prop 4.3.4 uses M_W = 1620 GeV throughout (the Faddeev lower bound), while Thm 4.3.2 gives M_W = 1800 ± 500 GeV. The dependency header (line 8) says "M_W = 1620 GeV." The proposition should use the full range or clearly state it is using the lower bound.
*Resolution:* Dependency header now states M_W = 1800 ± 500 GeV with "Faddeev lower bound 1620 GeV used as conservative benchmark." New §8 (Mass Range Robustness) shows all conclusions hold across M_W = 1300–2400 GeV with a robustness table.

**7. Higgs Portal Effects (Minor)** — ✅ NOTED (no action needed)
W-solitons interact via Higgs portal with coupling y_W ~ 10⁻¹. At the QCD phase transition (T ~ 150 MeV), Higgs-mediated interactions are negligible (Higgs is heavy and integrated out). No observable structure formation effects are expected.

### Limit Checks

| Limit | Test | Result |
|-------|------|--------|
| CDM limit (M → ∞) | v → 0, λ_fs → 0 | ✅ Correct behavior |
| SIDM limit (σ/m → 0) | Collisionless | ✅ Satisfied by 10⁻¹² cm²/g |
| ADM limit (no antiparticles) | No annihilation | ✅ Correctly argued |
| Standard Model recovery | TeV-scale particle consistent | ✅ No conflict |
| ΛCDM on large scales | Indistinguishable | ✅ Correct (cold + collisionless) |

### Framework Consistency

- **Thm 4.3.2 → Prop 4.3.4:** Self-interaction value ✅ CONSISTENT (Issue #1 resolved)
- **Prop 4.3.3 → Prop 4.3.4:** Ω_W h² ✅ CONSISTENT (Issue #7 resolved: now uses 0.14 ± 0.05)
- **Def 4.3.1 → Prop 4.3.4:** "Gauge singlet" claim consistent ✅
- **Def 4.3.1 → Prop 4.3.4:** Higgs portal coupling λ_HΦ = 0.036 now used in T_kd derivation ✅
- **Thm 4.1.1 topology → Prop 4.3.4:** Topological stability consistent ✅

---

## Recommended Corrections

### Priority 1 (Critical — must fix)

**Issue #1: Self-interaction cross-section (§3.2, §1b, §8 summary table, dependency header)**
- Replace σ_WW/M_W ≈ 2 × 10⁻⁴ cm²/g with **1.4 × 10⁻¹² cm²/g** everywhere
- Update safety factor from "~3500" to "~5 × 10¹¹"
- Update ratio from "3 × 10⁻⁴" to "2 × 10⁻¹²"
- Update dependency header line 8

**Issue #2: Free-streaming length (§2.2, §2.3 table, §4.1, §8 summary table)**
- Recompute λ_fs properly for M_W = 1620 GeV
- Expected result: ~10⁻¹³ Mpc (with comoving corrections) or simply state λ_fs ≪ 10⁻⁶ Mpc
- Update comparison table and summary table accordingly

### Priority 2 (Significant — should fix)

**Issue #3: Velocity arithmetic (§2.1)**
- Simplify to v/c = T_eq/M_W = 0.75 eV / 1620 GeV = 4.6 × 10⁻¹³
- Remove confusing intermediate step through T_f

**Issue #4: Interaction range (§3.3)**
- Replace r ≈ 0.004 fm with r ≈ 0.00036 fm (consistent with Thm 4.3.2)

**Issue #5: Markevitch citation (§3.1)**
- Change to σ/m < 1 cm²/g (Markevitch et al. 2004) or add Randall et al. (2008) for 1.25 cm²/g

**Issue #6: Harvey et al. value (§3.1)**
- Fix to σ/m < 0.47 cm²/g; add note about Wittman et al. (2018) revision

### Priority 3 (Minor — nice to fix)

**Issue #7:** Clarify Ω_W h² in §6.3 table (distinguish observation from prediction)
**Issue #8:** Fix k_fs value in §4.1
**Issue #9:** Note ⟨σv⟩_late ≈ 0 (suppressed by δ_sym²), not exactly 0
**Issue #10:** Add missing references (Randall et al., Wittman et al., Robertson et al.)
**Issue #11:** Soften Born regime claim or add quantitative check

---

## Impact on Proposition Validity

**Despite 11 issues, the core scientific conclusions are VALID:**
- W-solitons are cold dark matter ✅ (even colder than stated)
- W-solitons are effectively collisionless ✅ (even more collisionless than stated)
- W-solitons are indistinguishable from ΛCDM ✅
- CMB compatibility holds ✅
- No conflict with small-scale structure observations ✅

All numerical errors go in the direction that **strengthens** the conclusions. The W-soliton is more extreme as a CDM candidate than the document states.

---

## Verification Agents

| Agent | Verdict | Confidence | Key Finding |
|-------|---------|------------|-------------|
| Literature | Partial | Medium-High | Two citation errors (Markevitch, Harvey); values don't affect conclusions |
| Mathematical | Partial | Medium | σ/m off by 10⁸, λ_fs off by ~10⁹, velocity off by ~20; arithmetic errors |
| Physics | Partial | Medium | Framework inconsistency (σ/m); freeze-out subtlety; small-scale claims debatable |
