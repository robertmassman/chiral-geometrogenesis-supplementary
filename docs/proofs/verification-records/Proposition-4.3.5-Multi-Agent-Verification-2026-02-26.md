# Multi-Agent Verification Report: Proposition 4.3.5 (Second Re-Review)

## Skyrme Parameter from Pressure-Kurtosis Geometry

**Date:** 2026-02-26 (second re-review)
**Target:** `docs/proofs/Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md`
**Agents:** Mathematical (adversarial), Physics (adversarial), Literature (reference verification)
**Overall Verdict:** Partial — analytical machinery verified correct; matching derivation (sections 3.3-3.4) has a critical algebraic inconsistency
**Prior Reviews:** 2026-02-25 initial review (15 issues, all resolved); this re-review examines the revised version

---

## Executive Summary

Three independent verification agents reviewed Proposition 4.3.5 in its current (post-revision) state. The **analytical content from section 4 onward** — cap integrals, closed-form kurtosis formula, Monte Carlo verification, numerical tables, limiting cases, dimensional analysis, GL-Skyrme matching, NJL cross-checks — is mathematically correct, internally self-consistent, and well-documented. All algebra was independently re-derived and verified.

However, a **critical algebraic inconsistency** was identified in the matching derivation (sections 3.3-3.4) that links the pressure kurtosis to the physical Skyrme parameter. The boxed kurtosis formula does not follow from the matching equations as written — it is the reciprocal of what the matching produces. The independent cross-checks (NJL bosonization, GL-Skyrme matching) support the final value $e_W \approx 4.5$ but bypass the kurtosis derivation entirely.

| Agent | Verdict | Confidence | Key Finding |
|-------|---------|------------|-------------|
| Mathematical | Partial | Medium | All algebra from section 4 onward verified; matching in sections 3.3-3.4 contains reciprocal error |
| Physics | Partial | Medium | All limiting cases pass; $\tilde{\epsilon} = 0.130$ is calibrated not predicted |
| Literature | Partial | High | All citations verified; one minor title issue (Espriu & de Rafael 1986) |

---

## Issue Tracker

| # | Severity | Agent(s) | Section | Issue | Status |
|---|----------|----------|---------|-------|--------|
| 1 | **CRITICAL** | Math | sections 3.3-3.4 | Matching equations inconsistent with boxed formula (reciprocal error) | **OPEN** |
| 2 | **CRITICAL** | Physics | sections 3.5, 5.1 | $\tilde{\epsilon} = 0.130$ is calibrated to match QCD, not derived from physical $\epsilon = 0.50$ | ACKNOWLEDGED (proof is transparent) |
| 3 | MODERATE | Math | section 3.4 | $e_0 = 1$ assumption significance understated | **OPEN** |
| 4 | MODERATE | Math+Phys | sections 5.1, 5.4 | Verification script uses broader $\tilde{\epsilon}$ range [0.08, 0.18] giving 46% uncertainty vs proof's 27% | **OPEN** |
| 5 | MODERATE | Phys | section 6.7.5 | GL-Skyrme scale dependence (40% variation across natural scales) not in error budget | NOTED |
| 6 | MODERATE | Phys | section 2.1 | EFT validity: soliton mass at/above cutoff ($M_W/\Lambda_W \approx 1.0$-$1.3$) | ACKNOWLEDGED |
| 7 | Minor | Lit | section 8 | Espriu & de Rafael (1986) title may be slightly misquoted | **OPEN** |
| 8 | Minor | Lit | section 8 | Gudnason & Halcrow JHEP reference should specify month (JHEP **08** (2022) 117) | **OPEN** |
| 9 | Minor | Math | section 4.5 | Cap approximation 0.3% is a numerical finding, not an analytical bound | NOTED |

---

## Detailed Issue Descriptions

### CRITICAL Issues (2)

**Issue 1: Matching equations inconsistent with boxed formula (sections 3.3-3.4)** [Math]

This is the most significant finding. The proof contains three equations for the Skyrme parameter that are mutually inconsistent:

**Equation A** (line 158, matching from section 3.3):
$$\frac{1}{e_W^2} = \frac{1}{e_0^2} \cdot \frac{\int P_W^4 \, d\Omega}{(\int P_W^2 \, d\Omega)^2 / \Omega_W} \cdot \frac{1}{\Omega_W}$$

Parsing algebraically: the $\Omega_W$ factors cancel, giving $1/e_W^2 = I_4/(e_0^2 I_2^2)$.

**Equation B** (line 166, section 3.4):
$$\frac{1}{e_W^2} = \frac{1}{e_0^2} \cdot \frac{\Omega_W \int P_W^4 \, d\Omega}{(\int P_W^2 \, d\Omega)^2}$$

This gives $1/e_W^2 = \Omega_W I_4/(e_0^2 I_2^2)$, differing from Equation A by a factor of $\Omega_W = \pi$.

**Equation C** (line 170, boxed kurtosis formula with $e_0 = 1$):
$$e_W^2 = \frac{\Omega_W \int P_W^4 \, d\Omega}{(\int P_W^2 \, d\Omega)^2}$$

For Equation C to follow from Equation B, we would need $e_W^2 = I_2^2/(\Omega_W I_4)$, which is the **reciprocal** of the boxed formula.

**Concrete numerical test** (with $e_0 = 1$, $c = \tilde{\epsilon}^2 = 0.0169$, $I_2 = 182.8$, $I_4 = 216953$, $\Omega_W = \pi$):

| Expression | $e_W^2$ value | $e_W$ |
|-----------|--------------|-------|
| From Eq A: $e_W^2 = I_2^2/I_4$ | 0.154 | 0.39 |
| From Eq B: $e_W^2 = I_2^2/(\Omega_W I_4)$ | 0.049 | 0.22 |
| Eq C (boxed): $e_W^2 = \Omega_W I_4/I_2^2$ | 20.4 | **4.52** |

The boxed formula gives the physically reasonable value but does not follow from the matching. The "normalization logic" paragraph (line 160) attempts to bridge this gap but does not show explicit algebra.

**Impact:** The boxed kurtosis formula is a well-defined mathematical object and its evaluation is correct. But the derivation linking it to the physical Skyrme parameter has a gap. The cross-checks (NJL: $e = 4.44$, GL-Skyrme: $e = 4.64$) provide independent support but bypass the kurtosis derivation.

**Recommendation:** Either (a) fix the matching algebra with explicit step-by-step derivation, or (b) reframe the kurtosis formula as a geometrically motivated definition validated by the NJL and GL cross-checks.

---

**Issue 2: $\tilde{\epsilon}$ is calibrated, not predicted** [Physics]

The physical regularization $\epsilon = 0.50$ from Definition 0.1.3 yields $e_W = 1.44$ — far outside the QCD range. The effective $\tilde{\epsilon} = 0.130$ that gives $e_W = 4.5$ is determined by matching to QCD phenomenology. The proposition is transparent about this (section 3.5: "consistency check rather than a pure prediction") and provides two supporting routes:

- GL-Skyrme matching: $\tilde{\epsilon} = 0.127$ (from Prop 0.0.17k2 LECs)
- NJL bosonization inversion: $\tilde{\epsilon} = 0.132$

Both bracket the central value. However, both routes incorporate QCD phenomenological input. The proposition does not constitute a pure prediction of the Skyrme parameter from geometry alone.

**Impact:** The structural content (functional form, domain geometry dependence, limiting behavior) is genuine and novel. The numerical output depends on external input.

**Resolution:** This is acknowledged honestly in the proof. No correction needed, but the "geometric determination" framing should be understood as a consistency check.

---

### MODERATE Issues (4)

**Issue 3: $e_0 = 1$ assumption significance understated** [Math]

The proof frames $e_0 = 1$ as a normalization convention. However, to reconcile the section 3.3 matching with the kurtosis formula, $e_0$ would need to be $\approx 11.5$ (or its reciprocal) — far from unity. This is not an $O(1)$ normalization choice.

**Recommendation:** If the matching derivation is fixed (Issue 1), this issue may resolve naturally. Otherwise, acknowledge the magnitude of the convention choice.

---

**Issue 4: Verification script vs proof error budget discrepancy** [Math + Physics]

The verification script (`prop_4_3_5_corrected_derivation.py`) uses $\tilde{\epsilon} \in [0.08, 0.18]$, giving 44% regularization uncertainty and 46% total. The proof uses $[0.10, 0.16]$, giving 24% regularization and 27% total. These should be reconciled or the proof should explain the narrower range.

---

**Issue 5: GL-Skyrme scale dependence** [Physics]

The GL-Skyrme result varies from $e = 3.63$ at $\mu = m_\pi$ to $e = 5.02$ at $\mu = 4\pi f_\pi$ — a 40% variation across natural scales. The choice $\mu = M_V$ is standard for resonance saturation but adds systematic uncertainty not fully captured in the error budget.

---

**Issue 6: EFT validity boundary** [Physics]

$M_W^{(ANW)}/\Lambda_W \approx 1.29$ means the soliton mass exceeds the EFT cutoff. The 12% uncertainty for higher-order terms may be optimistic when $M/\Lambda > 1$. Adequately caveatted in the proof (sections 2.1, 5.3) but fundamentally limits the precision of any Skyrme-based calculation.

---

### Minor Issues (3)

**Issue 7:** Espriu & de Rafael (1986) title "On bosonization and chiral symmetry breaking" could not be confirmed by the literature agent. The journal (Nucl. Phys. B 274, 399-428) and physics content are correct. Verify exact title.

**Issue 8:** Gudnason & Halcrow reference should be "JHEP **08** (2022) 117" rather than "JHEP 2022, 117."

**Issue 9:** The 0.3% cap-vs-Voronoi agreement is verified numerically by Monte Carlo but is not bounded analytically. The azimuthal symmetry of the cap is broken by the true triangular Voronoi cell boundary.

---

## Agent-Specific Reports

### Mathematical Verification Agent

**VERIFIED: Partial** | **Confidence: Medium**

**Verified correct:**
- All cap integrals (section 4.3): $\int P_W^2 \, d\Omega = \pi/(c(1+c))$, $\int P_W^4 \, d\Omega = (\pi/3)(1/c^3 - 1/(1+c)^3)$
- Kurtosis simplification: $(1+c)^3 - c^3 = 1 + 3c(1+c)$, giving $e_W^2 = 1 + 1/(3\tilde{\epsilon}^2(1+\tilde{\epsilon}^2))$
- All numerical table values (section 4.6) to within rounding
- Step 2 inversion: $e_W = 4.50 \to \tilde{\epsilon} = 0.1305$ (verified by back-substitution)
- GL-Skyrme identity: $e^2 = 1/(8(\ell_2^r - \ell_1^r))$
- GL running: $\ell_1^r(M_V) = -4.11 \times 10^{-3}$, $\ell_2^r(M_V) = 1.70 \times 10^{-3}$, $e_{GL} = 4.64$
- NJL values: $e_{NJL}^2 = 6\pi^2/3 = 19.74$, $e_{NJL} = 4.44$
- Error budget quadrature: $\sqrt{24^2 + 12^2 + 3^2 + 2^2} = 27.07\%$
- Dimensional analysis: kurtosis is manifestly dimensionless
- Scale independence: $P_W \to \alpha P_W$ leaves $e_W^2$ invariant
- All integrals converge for $\tilde{\epsilon} > 0$
- Limiting cases: $\tilde{\epsilon} \to 0 \Rightarrow e_W \to \infty$, $\tilde{\epsilon} \to \infty \Rightarrow e_W \to 1$

**Errors found:**
1. CRITICAL: Matching inconsistency (sections 3.3-3.4) — see Issue 1 above

**Re-derived equations:**

| Equation | Location | Status |
|----------|----------|--------|
| $\int_{\text{cap}} P_W^2 \, d\Omega = \pi/(c(1+c))$ | section 4.3 | VERIFIED |
| $\int_{\text{cap}} P_W^4 \, d\Omega = (\pi/3)(1/c^3 - 1/(1+c)^3)$ | section 4.3 | VERIFIED |
| $e_W^2 = 1 + 1/(3\tilde{\epsilon}^2(1+\tilde{\epsilon}^2))$ | section 4.3 | VERIFIED |
| $\tilde{\epsilon}(e_W = 4.50) = 0.1305$ | section 4.6 | VERIFIED |
| $e^2 = 1/(8(\ell_2^r - \ell_1^r))$ | section 6.7.1 | VERIFIED |
| $\ell_1^r(M_V) = -4.11 \times 10^{-3}$, $\ell_2^r(M_V) = 1.70 \times 10^{-3}$ | section 6.7.2 | VERIFIED |
| $e_{GL} = 4.64$, $\tilde{\epsilon}_{GL} = 0.127$ | section 6.7.2 | VERIFIED |
| $e_{NJL} = 4.44$, $\tilde{\epsilon}_{NJL} = 0.132$ | section 6.6.1, 6.7.3 | VERIFIED |
| $M_W^{(FB)} = 1619$ GeV, $M_W^{(ANW)} = 1994$ GeV | section 6.5 | VERIFIED |
| $6\pi^2 = 59.22$, $72.96/(6\pi^2) = 1.232$ | section 6.5 | VERIFIED |

---

### Physics Verification Agent

**VERIFIED: Partial** | **Confidence: Medium**

**Limiting cases (all pass):**

| Limit | Expected | Actual | Status |
|-------|----------|--------|--------|
| $\tilde{\epsilon} \to 0$ (point-like) | $e_W \to \infty$ | $e_W \sim 1/(\sqrt{3}\,\tilde{\epsilon}) \to \infty$ | PASS |
| $\tilde{\epsilon} \to \infty$ (uniform) | $e_W \to 1$ | $e_W(100) = 1.000000$ | PASS |
| Uniform $P_W = \text{const}$ | $e_W = 1$ (Jensen) | Exact | PASS |
| Delta-function pressure | $e_W \to \infty$ | Consistent | PASS |
| Larger domain ($\Omega = 2\pi$) | Larger $e_W$ | $e_W = 6.33 > 4.5$ | PASS |
| Smaller domain ($\Omega = 2\pi/3$) | Smaller $e_W$ | $e_W = 3.72 < 4.5$ | PASS |
| Monotonicity in $\tilde{\epsilon}$ | Strictly decreasing | Verified | PASS |
| Jensen lower bound | $e_W \geq 1$ | Verified | PASS |

**Symmetry checks (all pass):**
- $S_4$ permutation symmetry of Voronoi cells: PASS
- $\mathbb{Z}_3$ boundary correction symmetry: PASS
- Scale independence ($P_W \to \alpha P_W$): PASS (variation $< 2 \times 10^{-16}$)

**Physical issues:**
1. $\tilde{\epsilon} = 0.130$ is calibrated, not predicted (Issue 2)
2. Soliton mass at EFT cutoff boundary (Issue 6)
3. Assumption A-PW4 is physically motivated but not derived

---

### Literature Verification Agent

**VERIFIED: Partial** | **Confidence: High**

**Citations verified:**

| Reference | Journal | Content | Status |
|-----------|---------|---------|--------|
| Adkins, Nappi & Witten (1983) | Nucl. Phys. B 228, 552 | $e = 4.25$ (chiral limit) | VERIFIED |
| Adkins & Nappi (1984) | Nucl. Phys. B 233, 109 | $e = 5.45$ (massive pions) | VERIFIED |
| Espriu & de Rafael (1986) | Nucl. Phys. B 274, 399 | $e^2 = 6\pi^2/N_c$ | VERIFIED (title unconfirmed) |
| Ebert & Reinhardt (1986) | Nucl. Phys. B 271, 188 | NJL Skyrme coefficient | VERIFIED |
| Sakai & Sugimoto (2005) | Prog. Theor. Phys. 113, 843 | Holographic $e \sim 7.3$ | VERIFIED (journal) |
| Holzwarth & Schwesinger (1986) | Rep. Prog. Phys. 49, 825 | $e = 4.84$ | VERIFIED |
| EGPR (1989) | Nucl. Phys. B 321, 311 | Resonance saturation | VERIFIED |
| Colangelo et al. (2001) | Nucl. Phys. B 603, 125 | $\bar{\ell}_1 = -0.4 \pm 0.6$, $\bar{\ell}_2 = 4.3 \pm 0.1$ | VERIFIED (current) |
| Gudnason & Halcrow (2022) | JHEP 08 (2022) 117 | 409 Skyrmion solutions | VERIFIED |
| Manton & Sutcliffe (2004) | CUP textbook | Fierz identity, conventions | VERIFIED |

**Standard results verified:**
- Faddeev-Bogomolny bound $M^{(FB)} = 6\pi^2 v/e$ in ANW convention: CORRECT
- ANW numerical factor 72.96 and ratio 1.232: CORRECT
- GL Fierz identity $\text{Tr}[L_\mu, L_\nu]^2 = 2(O_2 - O_1)$: CORRECT
- GL running coefficients $\gamma_1 = 1/3$, $\gamma_2 = 2/3$: CORRECT
- Lagrangian convention ($v^2/4$ kinetic, $1/(32e^2)$ Skyrme): Standard ANW

**Novelty assessment:** No prior work found deriving the Skyrme parameter from pressure-kurtosis geometry. The approach is genuinely novel.

**Experimental data status:** GL LECs remain current. No major updates needed. $\bar{\ell}_1$ and $\bar{\ell}_2$ are still primarily determined by Roy equations, not lattice.

---

## Overall Assessment

The proposition is a carefully constructed piece of work with excellent algebraic content and commendable honesty about its assumptions and limitations. The analytical machinery (sections 4-6) is verified correct in every detail. The cross-checks against NJL bosonization ($e = 4.44$, within 1.3%) and GL-Skyrme matching ($e = 4.64$, within 3%) provide strong independent support for $e_W \approx 4.5$.

The primary issue requiring attention is the matching derivation in sections 3.3-3.4, where the algebra leading to the boxed kurtosis formula contains an inconsistency (the boxed formula is the reciprocal of what the matching equations produce). This can likely be resolved by rewriting the matching with explicit step-by-step algebra, or by reframing the kurtosis as a motivated geometric definition validated by the cross-checks.

The secondary concern — that $\tilde{\epsilon} = 0.130$ is calibrated rather than predicted — is honestly acknowledged in the proof and is mitigated by the GL-Skyrme and NJL determinations. The proposition is best understood as a geometric consistency check of the Skyrme parameter with genuine structural content, rather than a pure prediction.

---

## Recommendations

1. **Fix the matching derivation (Issue 1):** Rewrite sections 3.3-3.4 with explicit step-by-step algebra from the microscopic action to the kurtosis formula, or reframe the kurtosis as a definition validated by cross-checks
2. **Reconcile error budgets (Issue 4):** Align the verification script range with the proof's $\tilde{\epsilon}$ range, or explain the narrower choice
3. **Verify Espriu & de Rafael title (Issue 7):** Check against original publication
4. **Add JHEP month (Issue 8):** Gudnason & Halcrow is JHEP **08** (2022) 117
