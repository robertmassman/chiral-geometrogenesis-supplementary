# Proposition 7.8.3: Bethe-Salpeter Glueball Mass Ratio — Multi-Agent Verification Report

**Date:** 2026-02-23
**Target:** Proposition 7.8.3 (Statement, Derivation, Applications)
**Method:** Three-agent adversarial review (Literature, Mathematics, Physics)
**Model:** Claude Opus 4.6 (all three agents)

---

## Executive Summary

| Agent | Verdict | Confidence | Key Finding |
|-------|---------|------------|-------------|
| **Literature** | Partial | Medium-High | Several citation issues (arXiv numbers, reference details); $b_0$ formula typo; core physics citations verified |
| **Mathematics** | Yes (with warnings) | High | All equations independently re-derived and verified; two presentation errors found; uncertainty may be underestimated |
| **Physics** | Partial | Medium-High | Derivation correct; $\alpha_s = 0.38$ self-consistency overstated; uncertainty likely 10-11% rather than 7% |

**Overall Verdict: PARTIAL VERIFICATION**
**Overall Confidence: Medium-High**

The core mathematical derivation $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ is **correct** — verified independently by all three agents. The formula is genuinely novel and the agreement with lattice QCD ($0.01\sigma$) is striking. However, the self-consistency of the coupling determination ($\alpha_s = 0.38$) is weaker than claimed, and the uncertainty may be underestimated. Several citation errors need correction.

---

## Consolidated Findings

### Critical Issues (0)

None. No errors that invalidate the core result.

### Moderate Issues (4)

| ID | Source | Description | Impact |
|----|--------|-------------|--------|
| **M-1** | Literature, Math | **$b_0$ formula typo in §9.2:** States $b_0 = 11N_c/(12\pi) = 2.626$, but $11 \times 3/(12\pi) = 0.875$. Correct formula: $b_0 = 11N_c/(4\pi)$. Numerical value 2.626 is correct; only the displayed formula is wrong. | Presentation only; no propagation to results. |
| **M-2** | Physics | **Self-consistency of $\alpha_s = 0.38$ overstated (§9.6):** One-loop running at both natural scales gives $\alpha_s = 0.42$–$0.47$, significantly above the adopted 0.38. The text claims two-loop corrections reduce this, but no explicit computation is shown. | The "self-consistent" label overstates rigor. More honest: "consistent within scale uncertainty." |
| **M-3** | Physics | **$\delta\alpha_s = 0.04$ may be underestimated (§10.1):** If the true coupling uncertainty is $\pm 0.06$, the $R_\text{BS}$ uncertainty rises from 7% to ~11%, and the combined uncertainty from 5.3% to ~6.5%. | Moderate impact on precision claims but not on the qualitative conclusion ($R \sim 3.4$, consistent with lattice). |
| **M-4** | Math | **Intermediate algebra display in Eq 7.5:** The prefactor $-4\beta^3/\pi$ and integral factor $\pi/(4\beta^3)$ have inconsistent $\pi$ insertions. The final result $\langle p^2\rangle = \beta^2$ is correct (verified numerically). | Presentation only; no propagation. |

### Minor Issues (7)

| ID | Source | Description |
|----|--------|-------------|
| **m-1** | Literature | **Reference [9] wrong arXiv number:** Listed as arXiv:0806.3875 (a SUSY paper). Should be **arXiv:0806.3174**. |
| **m-2** | Literature | **Reference [12] publication details possibly incorrect:** "J. Math. Phys. 46 (2005) 032302" may actually be JMP 52 (2011) 052107. Needs verification against original source. |
| **m-3** | Literature, Physics | **Reference [13] cites three-gluon paper for two-gluon systematics:** PRD 77 (2008) 094009 studies three-gluon glueballs. The two-gluon AFM benchmark paper is Mathieu et al. PRD 70 (2004) 014017. |
| **m-4** | Literature | **Symbol table vs derivation convention mismatch for $b_0$:** Symbol table gives $b_0 = 11/(16\pi^2) \approx 0.070$ (from Thm 7.5.2), while derivation uses $b_0 = 2.626$. These are different conventions for the same physics, but this is confusing without explanation. |
| **m-5** | Literature | **$\sqrt{\sigma}/\Lambda_{\overline{MS}}$ tension with newer determinations:** Necco & Sommer (2002): $1.994 \pm 0.021$. Ishikawa et al. (2017): $1.934 \pm 0.049$ ($1.2\sigma$ lower). Impact on $c_\text{FI}$: ~3% shift in central value. |
| **m-6** | Physics | **Glueball size vs Cornell regime not explicitly verified:** The glueball RMS radius (~0.1–0.2 fm) is well below the adjoint string-breaking distance (~1.25 fm), but this should be stated explicitly. |
| **m-7** | Physics | **Weighted average shares two-constituent model assumption:** Both Props 7.8.2 and 7.8.3 assume a two-constituent glueball picture. This is well-supported by lattice operator analysis but should be noted. |

---

## Agent Reports

### 1. Literature Verification Agent

**Verdict:** Partial | **Confidence:** Medium-High

#### Citation Accuracy

| Reference | Claim | Status |
|-----------|-------|--------|
| [1] Athenodorou & Teper (2020) | $R_\text{cont} = 3.405 \pm 0.021$ | LIKELY CORRECT (paper exists; value plausible; most current determination) |
| [2] Necco & Sommer (2002) | $\sqrt{\sigma}/\Lambda_{\overline{MS}} = 1.994 \pm 0.021$ | LIKELY CORRECT but $1.2\sigma$ tension with Ishikawa et al. (2017) |
| [5] Bali (2000) | $\sigma_8/\sigma_3 = 2.26 \pm 0.06$ | **VERIFIED** |
| [9] Boulanger et al. (2008) | arXiv:0806.3875 | **WRONG** arXiv number (should be 0806.3174) |
| [11] Semay (2012) | AFM method | VERIFIED (paper exists, method correctly described) |
| [12] Silvestre-Brac & Semay (2005) | JMP 46 032302 | POSSIBLY INCORRECT publication details |
| [13] Mathieu et al. (2008) | ~5% AFM error | EXISTS but is a three-gluon paper, not two-gluon |

#### Standard Results Verified

- SU(3) Casimirs: $C_2(\mathbf{3}) = 4/3$, $C_2(\mathbf{8}) = 3$ — **VERIFIED**
- Color singlet factor $\langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle = -3$ — **VERIFIED**
- Casimir scaling $\sigma_\text{adj}/\sigma_\text{fund} = 9/4$ — **VERIFIED**
- $\sqrt{\sigma} = 440$ MeV — **VERIFIED** (FLAG 2024)
- $\alpha_s = 0.38 \pm 0.04$ at glueball scale — **REASONABLE**
- $\Lambda_{\overline{MS}} \approx 220$ MeV for pure SU(3) — **APPROXIMATELY CORRECT**

#### Novelty Assessment

The closed-form formula $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ was **not found in prior literature**. The novel status is justified.

---

### 2. Mathematical Verification Agent

**Verdict:** Yes (with warnings) | **Confidence:** High

#### Re-Derived Equations (All Verified)

| Equation | Claim | Status |
|----------|-------|--------|
| Eq 5.3–5.4: Color factor | $\langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle = -3$ | **VERIFIED** |
| Eq 6.1: AFM identity | $\min_{\nu>0}[p^2/(2\nu)+\nu/2] = |p|$ | **VERIFIED** (analytic + 2nd derivative) |
| Eq 7.2: $\langle p^2\rangle = \beta^2$ | Matrix element | **VERIFIED** (scipy quad) |
| Eq 7.3: $\langle 1/r\rangle = \beta$ | Matrix element | **VERIFIED** (scipy quad) |
| Eq 7.4: $\langle r\rangle = 3/(2\beta)$ | Matrix element | **VERIFIED** (scipy quad) |
| Eq 7.7: Energy functional | $\beta^2/\nu + \nu + 27\sigma_3/(8\beta) - 3\alpha_s\beta$ | **VERIFIED** |
| Eq 7.8: $\nu^* = \beta$ | AFM optimization | **VERIFIED** |
| Eq 7.9: $E = (2-3\alpha_s)\beta + 27\sigma_3/(8\beta)$ | After $\nu$ opt | **VERIFIED** |
| Eq 7.11: $\beta^{*2} = 27\sigma_3/(8(2-3\alpha_s))$ | $\beta$ optimization | **VERIFIED** (analytic + numerical scan) |
| Eq 8.1–8.4: $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ | Final formula | **VERIFIED** |
| Eq 10.1–10.2: $|dR/d\alpha_s| = 5.94$ | Derivative | **VERIFIED** (analytic + finite difference) |
| Eq 11.1–11.3: Weighted average | $R_\text{combined} = 3.40 \pm 0.18$ | **VERIFIED** |
| Eq 11.6–11.8: $c_\text{FI} = 6.78 \pm 0.38$ | Error propagation | **VERIFIED** |

#### Numerical Spot-Checks

| Check | Expected | Computed | Status |
|-------|----------|----------|--------|
| $R_\text{BS}(0.38)$ | 3.407 | 3.4073 | **PASS** |
| $R_\text{BS}(0)$ | $3\sqrt{3} = 5.196$ | 5.196 | **PASS** |
| $w_1 = 1/0.27^2$ | 13.72 | 13.717 | **PASS** |
| $w_2 = 1/0.24^2$ | 17.36 | 17.361 | **PASS** |
| $1/\sqrt{31.08}$ | 0.179 | 0.1794 | **PASS** |

#### Dimensional Analysis

All equations verified for dimensional consistency. $R_\text{BS}$ is confirmed dimensionless.

#### Warning: Uncertainty Underestimate

If AFM+variational systematics are added in quadrature with $\alpha_s$ uncertainty: $\sqrt{0.238^2 + 0.197^2} = 0.31$ (9.1%). The quoted 7% is a lower bound. Standard practice, but should be acknowledged.

---

### 3. Physics Verification Agent

**Verdict:** Partial | **Confidence:** Medium-High

#### Limit Checks

| Limit | Prediction | Expectation | Assessment |
|-------|-----------|-------------|------------|
| $\alpha_s \to 0$ (pure confinement) | $R_\text{BS} \to 5.196$ | Large mass from confinement | **PASS** |
| $\alpha_s \to 2/3$ (critical) | $R_\text{BS} \to 0$ | Coulomb catastrophe | **PASS** |
| $\alpha_s = 0.38$ (central) | $R_\text{BS} = 3.407$ | Lattice: $3.405 \pm 0.021$ | **PASS** ($0.01\sigma$) |
| $\sigma$ cancellation | $R_\text{BS}$ independent of $\sigma$ | Dimensional analysis | **PASS** |
| $N_c$ dependence | Through color factors | Large-$N$ well-defined | **PASS** |

#### Symmetry and Quantum Numbers

- $\mathbf{8} \otimes \mathbf{8}$ decomposition: **CORRECT** (dimensions sum to 64)
- $J^{PC} = 0^{++}$ from $s$-wave singlet: **CORRECT** ($L=0$, $P=(-1)^L=+1$, $C=(-1)^{L+S}=+1$)
- Color factor $-3$: **CORRECT**

#### Framework Consistency

| Cross-reference | Status |
|----------------|--------|
| Casimir invariants (Prop 0.0.38) | **CONSISTENT** |
| One-loop beta function (Thm 7.5.2) | **CONSISTENT** (different convention, same physics) |
| Updated $c_\text{FI}$ (Thm 7.7.3) | **CONSISTENT** ($6.78 \pm 0.38$ matches lattice-input $6.78 \pm 0.31$) |
| Prop 7.8.2 inputs | **CONSISTENT** (correctly quoted and combined) |

#### Key Physics Concern

The self-consistency of $\alpha_s = 0.38$ is the main weakness. One-loop running at the glueball scale gives $0.42$–$0.47$, and the claim that two-loop corrections bring this down to $0.38$ is not demonstrated. The formula $R_\text{BS}(\alpha_s)$ is valid for any $\alpha_s$, but the precision claim depends on how well $\alpha_s$ is determined.

---

## Recommendations

### Corrections Required

1. **Fix $b_0$ formula in §9.2:** Change `$b_0 = 11N_c/(12\pi)$` to `$b_0 = 11N_c/(4\pi)$` (numerical value 2.626 is already correct).
2. **Fix arXiv number for reference [9]:** Change `arXiv:0806.3875` to `arXiv:0806.3174`.
3. **Fix intermediate algebra in Eq 7.5:** Remove spurious $\pi$ factors in the displayed intermediate steps.

### Recommended Improvements

4. **Verify reference [12] publication details:** Confirm JMP 46 (2005) 032302 vs JMP 52 (2011) 052107.
5. **Cite two-gluon paper for AFM benchmarks:** Add Mathieu et al. PRD 70 (2004) 014017 alongside or instead of [13].
6. **Soften self-consistency language in §9.6:** Replace "self-consistent" with "consistent within the scale uncertainty."
7. **Compute two-loop $\alpha_s$ explicitly** or expand uncertainty to $\delta\alpha_s = 0.06$.
8. **Add glueball RMS radius computation** and verify it lies within the Cornell potential validity regime.
9. **Note the $\sqrt{\sigma}/\Lambda_{\overline{MS}}$ tension** with Ishikawa et al. (2017) value ($1.934 \pm 0.049$).

### Optional Enhancements

10. **Add a note** about the shared two-constituent model assumption in §11.2.
11. **Clarify the $b_0$ convention difference** between symbol table and derivation.

---

## Verification Script Results

The existing verification script (`verification/Phase7/prop_7_8_3_bethe_salpeter_glueball_ratio.py`) reports:
- **14/14 standard tests PASS** (C-1 through C-14)
- **6/6 adversarial tests PASS** (ADV-1 through ADV-6)

An additional adversarial verification script has been created:
- `verification/Phase7/prop_7_8_3_adversarial_verification.py` — Extended adversarial tests including the issues identified in this review

---

## Status Recommendation

**Current status:** 🔶 NOVEL (pending multi-agent adversarial review)

**Recommended status after corrections:** 🔶 NOVEL ✅ VERIFIED (pending Lean 4 formalization)

The core mathematical derivation is sound and independently verified. The issues identified are presentation-level (citation errors, formula typo) and uncertainty-related (possibly optimistic precision claims). None invalidate the central result $R_\text{BS} \approx 3.4$, consistent with lattice QCD.

---

*Verification completed: 2026-02-23*
*Agents: Claude Opus 4.6 (Literature, Mathematics, Physics — independent adversarial review)*
*Overall: PARTIAL VERIFICATION — derivation correct, citations need fixes, uncertainty may be underestimated*
