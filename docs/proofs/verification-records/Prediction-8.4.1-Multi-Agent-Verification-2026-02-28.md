# Prediction 8.4.1: Proton Decay from Geometric GUT — Multi-Agent Verification Report

**Document:** [`Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md`](../Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md)

**Verification Date:** 2026-02-28

**Methodology:** Three independent adversarial agents (Literature, Mathematics, Physics) + adversarial Python verification (13 tests)

---

## Executive Summary

| Agent | Verdict | Confidence | Key Findings |
|-------|---------|------------|--------------|
| **Literature** | Partial | Medium | 2 citation errors, 1 outdated bound, missing references |
| **Mathematics** | Partial | Medium-High | Core calc correct; 2 formula display errors found |
| **Physics** | Partial | Medium-High | Physically sound; SUSY tension with Prop 0.0.25 noted |
| **Adversarial Script** | **PASSED** (13/13) | High | All numerical tests pass; A_R formula issue confirmed |

**Overall Assessment:** The core physics calculation is **CORRECT**. The central prediction $\tau(p \to e^+\pi^0) = 5.1^{+6.6}_{-2.8} \times 10^{36}$ years is verified independently by all three agents and 13 adversarial tests. Issues found are presentational (formula display errors, citation mistakes) and one conceptual tension (SUSY status), none of which affect the numerical result.

---

## Issues Requiring Correction

### CRITICAL: None

### MODERATE (3 issues)

#### Issue 1: A_R Formula Inverted in Section 3.2

**Found by:** Math Agent, Physics Agent, Adversarial Script (Test 6)

The RG running formula displayed in section 3.2:

$$A_R = \left(\frac{\alpha_s(M_{GUT})}{\alpha_s(m_b)}\right)^{6/23} \left(\frac{\alpha_s(m_b)}{\alpha_s(m_c)}\right)^{6/25} \left(\frac{\alpha_s(m_c)}{\alpha_s(2\text{ GeV})}\right)^{6/27}$$

has the ratios **inverted** compared to the standard convention (Nihei & Arafune 1995, Nath & Perez 2007). Since $\alpha_s(M_{GUT}) \ll \alpha_s(m_b)$, this formula gives $A_R \approx 0.5$ (suppression), not the $A_R \approx 2.5$ (enhancement) stated and used in the calculation.

**Correct formula:**

$$A_R = \left(\frac{\alpha_s(m_b)}{\alpha_s(M_{GUT})}\right)^{6/23} \left(\frac{\alpha_s(m_c)}{\alpha_s(m_b)}\right)^{6/25} \left(\frac{\alpha_s(2\text{ GeV})}{\alpha_s(m_c)}\right)^{6/27}$$

**Impact:** The VALUE $A_R = 2.5$ used in all calculations is correct (standard literature value). Only the displayed formula needs correction. No numerical results are affected.

#### Issue 2: SUSY Tension Between Prop 0.0.25 and Non-SUSY Treatment

**Found by:** Physics Agent

Prediction 8.4.1 treats the model as "non-SUSY" (no dimension-5 operators, $e^+\pi^0$ dominance). However, Proposition 0.0.25 constructs a heterotic $E_8 \times E_8$ model with $N=1$ SUSY in 4D (K3 has SU(2) holonomy). The unification parameters ($\alpha_{GUT}^{-1} = 24.4$, $M_{GUT} = 2 \times 10^{16}$ GeV) are characteristic of the SUSY unification trajectory.

**Impact:** This creates a conceptual tension that should be addressed: if the underlying model has $N=1$ SUSY, dimension-5 operators should exist unless SUSY is broken well above $M_{GUT}$. The document should specify how and where SUSY breaks and why dimension-5 operators are absent.

#### Issue 3: Babu-Mohapatra Citation Year Error

**Found by:** Literature Agent, Math Agent

Reference 11 cites "Babu, K.S. & Mohapatra, R.N. (2012)" but Phys. Rev. Lett. 70, 2845 was published in **1993**, not 2012. Table 8.4 also labels this as "Babu-Mohapatra (2012)."

**Fix:** Change to "(1993)" or replace with the appropriate 2012 Babu-Mohapatra paper on B-L violating proton decay (PRL 109, 091803, 2012).

### MINOR (7 issues)

#### Issue 4: Aoki et al. Title Incorrect

**Found by:** Literature Agent

The correct title of arXiv:1705.01338 is "Improved lattice computation of proton decay matrix elements," not "Proton lifetime bounds from chirally symmetric lattice QCD."

#### Issue 5: Uncertainty Expression Typo in Section 4.4

**Found by:** Math Agent

The $\alpha_{GUT}$ uncertainty row contains: "$2 \times 0.3/24.4 / (1/24.4) = 0.025$" — parsing this literally gives $2 \times 0.3 = 0.6$, not 0.025. The correct expression is simply $2 \times 0.3/24.4 = 0.025$. Remove the spurious "/ (1/24.4)."

#### Issue 6: Executive Summary Table Mixes Total and Partial Lifetimes

**Found by:** Math Agent, Physics Agent

The first row uses the total lifetime ($5.1 \times 10^{36}$ yr, margin 213x), while subsequent rows use partial lifetimes. The Super-K bound applies to specific channels. The correct partial lifetime for $p \to e^+\pi^0$ is $1.3 \times 10^{37}$ yr with margin 560x (as correctly stated in section 5.2).

#### Issue 7: $p \to e^+\eta$ Bound Outdated

**Found by:** Literature Agent

The document uses $> 1.0 \times 10^{34}$ yr, but Super-K updated this to $> 1.4 \times 10^{34}$ yr in September 2024 (arXiv:2409.19633). Does not affect conclusions.

#### Issue 8: Falsification Threshold Error in Section 10.2

**Found by:** Physics Agent

Section 10.2 states "Proton stable beyond $10^{40}$ years — would require $M_{GUT} > 5 \times 10^{16}$ GeV." The correct threshold is $M_{GUT} > 1.3 \times 10^{17}$ GeV (since $\tau \propto M^4$: $2.0 \times 10^{16} \times (10^{40}/5.1 \times 10^{36})^{1/4} = 1.33 \times 10^{17}$ GeV).

#### Issue 9: JUNO Sensitivity Value Uncertain

**Found by:** Literature Agent

The 1.9 x 10^34 yr value for JUNO should be verified. The JUNO sensitivity paper (arXiv:2212.08502) reports $9.6 \times 10^{33}$ yr for 200 kton-year exposure.

#### Issue 10: Missing References

**Found by:** Literature Agent

- Claudson, Wise & Hall (1982) — original chiral Lagrangian proton decay derivation
- Aoki et al. (2022) — updated lattice QCD at physical pion mass (PRD 105, 074501)
- JUNO Collaboration (2023) — JUNO sensitivity paper (arXiv:2212.08502)

---

## Literature Agent Report

### Verified Values

| Parameter | Document Value | Verified | Status |
|-----------|---------------|----------|--------|
| $m_p$ | 0.938272 GeV | PDG 2024 | CORRECT |
| $f_\pi$ | 0.1302 GeV | PDG standard convention | CORRECT (note: CG elsewhere uses 0.0921 GeV Peskin-Schroeder convention) |
| $|\alpha_H|$ | 0.0118 GeV^3 | RBC-UKQCD 2017 | CORRECT |
| $D$ | 0.804 | Hyperon semileptonic | CORRECT |
| $F$ | 0.463 | $D+F \approx g_A/2$ | CORRECT |
| $|V_{ud}|^2$ | 0.949 | PDG 2024 | CORRECT |
| $|V_{us}|^2$ | 0.051 | PDG 2024 | CORRECT |
| $A_R$ | 2.5 | Nihei-Arafune, Nath-Perez | CORRECT |

### Experimental Bounds Verified

| Channel | Document | Verified | Status |
|---------|----------|----------|--------|
| $p \to e^+\pi^0$ | $> 2.4 \times 10^{34}$ yr | Super-K (2020) PRD 102, 112011 | CORRECT |
| $p \to \mu^+\pi^0$ | $> 1.6 \times 10^{34}$ yr | Super-K (2020) | CORRECT |
| $p \to \bar{\nu}K^+$ | $> 5.9 \times 10^{33}$ yr | Super-K (2014) | CORRECT |
| $p \to e^+\eta$ | $> 1.0 \times 10^{34}$ yr | Super-K (2024): now $> 1.4 \times 10^{34}$ | **OUTDATED** |
| Hyper-K $p \to e^+\pi^0$ | $\sim 10^{35}$ yr | Hyper-K Design Report | CORRECT |

### Citations Verified

| Reference | Status |
|-----------|--------|
| Nath & Perez (2007), Phys. Rept. 441 | CORRECT |
| Georgi & Glashow (1974), PRL 32, 438 | CORRECT |
| Babu & Mohapatra, PRL 70, 2845 | Year WRONG (1993, not 2012) |
| Aoki et al. (2017), arXiv:1705.01338 | Title WRONG |
| Super-K (2020), PRD 102, 112011 | CORRECT |
| Hyper-K Design Report, arXiv:1805.04163 | CORRECT |
| DUNE CDR, arXiv:2002.03005 | CORRECT |

---

## Mathematics Agent Report

### Step-by-Step Re-Derivation

| Step | Claimed | Computed | Relative Diff | Status |
|------|---------|----------|---------------|--------|
| Numerator | $4.95 \times 10^{-3}$ | $4.951 \times 10^{-3}$ | 0.02% | VERIFIED |
| Denominator | $5.42 \times 10^{63}$ | $5.425 \times 10^{63}$ | 0.09% | VERIFIED |
| Matrix factor | $4.47 \times 10^{-3}$ | $4.472 \times 10^{-3}$ | 0.06% | VERIFIED |
| Decay rate | $4.08 \times 10^{-69}$ | $4.082 \times 10^{-69}$ | 0.05% | VERIFIED |
| Lifetime | $5.1 \times 10^{36}$ yr | $5.11 \times 10^{36}$ yr | 0.19% | VERIFIED |

### Dimensional Analysis

$$[\Gamma] = \frac{[\text{GeV}]^1 \cdot [1]^2}{[\text{GeV}]^2 \cdot [\text{GeV}]^4} \times [1]^2 \cdot [1]^2 \cdot [\text{GeV}]^6 = [\text{GeV}]^1 \quad \checkmark$$

### Uncertainty Propagation

| Source | Contribution | Verified |
|--------|-------------|----------|
| $M_{GUT}$ ($\times 4$) | 55% | CORRECT |
| $A_R$ ($\times 2$) | 25% | CORRECT |
| $|\alpha_H|$ ($\times 2$) | 20% | CORRECT |
| $\alpha_{GUT}$ ($\times 2$) | $<1\%$ | CORRECT |
| Combined $\sigma(\log_{10}\tau)$ | 0.36 | CORRECT (MC gives 0.35-0.37) |

### Reconciliation Arithmetic (Section 7.2)

| Factor | Claimed | Computed | Status |
|--------|---------|----------|--------|
| $(24.4/44.5)^2$ | 0.30 | 0.3006 | VERIFIED |
| $(2.0)^4$ | 16 | 16.0 | VERIFIED |
| $(0.015/0.0118)^2$ | 1.62 | 1.616 | VERIFIED |
| Net scaling | ~7.8 | 7.77 | VERIFIED |

---

## Physics Agent Report

### Limit Checks

| Limit | Expected | Result | Status |
|-------|----------|--------|--------|
| $M_X \to \infty$ | $\tau \to \infty$ | $\tau \to \infty$ | PASS |
| $\alpha_{GUT} \to 0$ | $\Gamma \to 0$ | $\Gamma \to 0$ | PASS |
| $M_X \to M_Z$ | Rapid decay | $\tau \sim 10^{-14}$ s | PASS |
| $M_X$ doubled | $\tau \to 16\tau$ | Verified | PASS |
| $\alpha_{GUT}$ halved | $\tau \to 4\tau$ | Verified | PASS |

### Symmetry Verification

| Check | Status |
|-------|--------|
| SO(10) $\to$ SU(5) $\times$ U(1) chain | STANDARD, CORRECT |
| **45** decomposition: $24 + 10 + \overline{10} + 1$ | CORRECT (24+10+10+1 = 45) |
| X/Y boson quantum numbers $(3,2)_{5/6}$ | CORRECT |
| Dimension-6 operator structure | STANDARD |

### Framework Consistency

| Cross-reference | Status |
|----------------|--------|
| Prop 0.0.25 ($\alpha_{GUT}$, $M_{GUT}$) | CONSISTENT |
| Thm 0.0.4 (SO(10) embedding) | CONSISTENT |
| Prop 2.4.2 Section 8.3 (old estimate) | RECONCILED |
| Thm 2.4.1 (X/Y non-propagation) | QUALITATIVE |
| Thm 4.2.2 (Sakharov conditions) | CONSISTENT |
| Prop 4.2.4 (sphaleron rate) | CONSISTENT |
| Pred 8.3.1 (dark matter stability) | CONSISTENT |

### Experimental Tensions

**None.** All channels exceed Super-K bounds by factors of 100-250,000x.

---

## Adversarial Python Verification Report

**Script:** [`prediction_8_4_1_proton_decay_adversarial.py`](../../../verification/Phase8/prediction_8_4_1_proton_decay_adversarial.py)

**Result: 13/13 tests PASS**

| Test | Description | Result |
|------|-------------|--------|
| 1 | Independent step-by-step re-derivation | PASS |
| 2 | Alternative formula cross-check (Nath-Perez) | PASS (ratio 0.82) |
| 3 | $M_{GUT}$ exclusion boundary analysis | PASS (3.8x above minimum) |
| 4 | 2D parameter space scan ($M_{GUT}$ vs $\alpha_{GUT}$) | PASS (73% allowed) |
| 5 | Hadronic matrix element sensitivity | PASS (all $|\alpha_H|$ values safe) |
| 6 | RG running factor verification | PASS ($A_R$ correct; formula display issue found) |
| 7 | Branching ratio robustness | PASS (dominant channel stable) |
| 8 | SUSY vs non-SUSY discrimination | PASS (889x discrimination) |
| 9 | Monte Carlo with correlated uncertainties | PASS (all scenarios safe) |
| 10 | Pre-geometric form factor impact | PASS ($\kappa_{crit} = 14.6 > 1$) |
| 11 | Deep dimensional analysis | PASS (all checks) |
| 12 | Reconciliation arithmetic | PASS (net scaling 7.77 vs claimed ~7.8) |
| 13 | Comprehensive GUT model comparison | PASS (within SO(10) range) |

### Generated Plots

| Plot | Description |
|------|-------------|
| [`pred_8_4_1_mgut_exclusion.png`](../../../verification/plots/pred_8_4_1_mgut_exclusion.png) | Lifetime vs. $M_{GUT}$ with Super-K/Hyper-K bounds |
| [`pred_8_4_1_parameter_space.png`](../../../verification/plots/pred_8_4_1_parameter_space.png) | 2D contour of $\tau$ in $(M_{GUT}, \alpha_{GUT}^{-1})$ space |
| [`pred_8_4_1_alpha_h_sensitivity.png`](../../../verification/plots/pred_8_4_1_alpha_h_sensitivity.png) | Sensitivity to hadronic matrix element $|\alpha_H|$ |
| [`pred_8_4_1_ar_sensitivity.png`](../../../verification/plots/pred_8_4_1_ar_sensitivity.png) | Sensitivity to RG running factor $A_R$ |
| [`pred_8_4_1_correlated_mc.png`](../../../verification/plots/pred_8_4_1_correlated_mc.png) | Monte Carlo distributions with parameter correlations |
| [`pred_8_4_1_form_factor.png`](../../../verification/plots/pred_8_4_1_form_factor.png) | Pre-geometric form factor $\kappa_{geo}$ impact |
| [`pred_8_4_1_model_comparison.png`](../../../verification/plots/pred_8_4_1_model_comparison.png) | CG vs. other GUT model predictions |

---

## Recommended Actions

### Must Fix (before any status upgrade)

1. **Invert A_R formula** in section 3.2 (swap numerator/denominator in each factor)
2. **Fix Babu-Mohapatra year** — change "(2012)" to "(1993)" in Ref 11 and Table 8.4
3. **Fix Aoki et al. title** — "Improved lattice computation of proton decay matrix elements"
4. **Fix alpha_GUT uncertainty expression** — remove spurious "/ (1/24.4)"
5. **Fix Executive Summary table** — use partial lifetime for $p \to e^+\pi^0$ (margin 560x)
6. **Fix falsification threshold** — $M_{GUT} > 1.3 \times 10^{17}$ GeV for $\tau > 10^{40}$ yr

### Should Address

7. **Discuss SUSY tension** with Prop 0.0.25's $N=1$ SUSY heterotic model
8. **Update $p \to e^+\eta$ bound** to $> 1.4 \times 10^{34}$ yr (Super-K 2024)
9. **Verify JUNO sensitivity** value (1.9 vs 0.96 $\times 10^{34}$ yr)
10. **Add missing references** (Claudson-Wise-Hall 1982, Aoki et al. 2022)

---

*Verification performed by: Multi-Agent Adversarial Review System*
*Date: 2026-02-28*
*Status: Core calculation VERIFIED; presentational corrections needed*
