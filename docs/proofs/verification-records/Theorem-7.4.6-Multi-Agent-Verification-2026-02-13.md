# Theorem 7.4.6: Osterwalder-Schrader Axioms for CG Yang-Mills — Multi-Agent Verification Report

**Date:** 2026-02-13
**Theorem:** Theorem 7.4.6 — OS Axioms for CG Yang-Mills
**Files Reviewed:**
- `docs/proofs/Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills.md` (Statement)
- `docs/proofs/Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills-Derivation.md` (Derivation)
- `docs/proofs/Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills-Applications.md` (Applications)

**Verification Protocol:** Three independent adversarial agents (Mathematical, Physics, Literature) run in parallel.

---

## Executive Summary

| Agent | Verdict | Confidence | Findings |
|-------|---------|------------|----------|
| **Mathematical** | Partial | Medium-High | 2 errors, 7 warnings |
| **Physics** | Partial | Medium | 12 issues (1 major, 1 significant, 4 moderate, 6 minor) |
| **Literature** | Partial | Medium-High | 4 citation issues, 5 missing references |

**Overall Assessment:** The theorem is well-constructed with exemplary honesty about what is proven vs. conjectural. The core results (OS2 and OS4 rigorously established on the FCC lattice, survival under subsequential limits via Seiler compactness) are mathematically sound. The main issues are: (1) an algebraic error in the analyticity gap formula, (2) status labeling inconsistencies for OS3 and OS4, (3) the D₄ isotropy claim needs clarification, and (4) several missing references.

---

## Finding Summary Table

| ID | Agent | Severity | Description | Location |
|----|-------|----------|-------------|----------|
| **F4** | Math | **HIGH** | Analyticity gap formula missing 3 ln(3/8) term | Applications line 131 |
| **P4** | Physics | **SIGNIFICANT** | D₄ isotropy claimed exact but verification shows ratio 2 not 3 | Derivation §6.4 |
| **P6** | Physics | **MAJOR** | Global label constraint physical implications need discussion | All files |
| **F1** | Math | MEDIUM | OS0 analyticity conflates β-analyticity with position-analyticity | Statement line 91, Derivation §5.2 |
| **F2** | Math | MEDIUM | OS3 has independent proof (commuting observables) but classified as dependent on OS1 | Statement line 267 |
| **F7** | Math | MEDIUM | "Subsequential limits" vs "the continuum limit" distinction needed | Throughout |
| **F9/P7** | Math+Phys | MEDIUM | OS4 labeled ESTABLISHED unconditionally; continuum is conditional on C2 | Statement lines 12, 268 |
| **P9** | Physics | MODERATE | "Automatic Symanzik improvement" needs qualification (rotational part only) | Derivation App C.3 |
| **P10** | Physics | MODERATE | Comparison table understates standard lattice QCD results (RP is proven, not assumed) | Applications §8.6 |
| **L1** | Literature | MODERATE | OS0 naming: should be "Temperedness" not "Analyticity" in standard convention | Statement §1 |
| **L2** | Literature | MODERATE | Mass gap value ~1.5 GeV slightly low; lattice consensus ~1.7 GeV for 0⁺⁺ | Applications §8.3 |
| **L3** | Literature | MINOR | Balaban citation incomplete (only 2 of 6+ papers cited) | References §10 |
| **L4** | Literature | MINOR | Lüscher-Weisz (1985) referenced in text but missing from formal references | References §10 |
| **L5** | Literature | MINOR | Menetti-Pelissetto (1987) CMP 113 not cited — general OS positivity for Wilson action | Missing |
| **F3** | Math | LOW | Seiler compactness tightness argument: link to measure tightness not explicit | Derivation App B.2 |
| **F5** | Math | LOW | Arzelà-Ascoli needs distributional framework clarification | Derivation §5.3 |
| **F6** | Math | LOW | OS0' growth condition not explicitly verified (C=3, α=0) | Derivation App A.2 |
| **P1** | Physics | MINOR | √3 factor inconsistency between Statement and Applications mass gap formula | Apps §8.2 |
| **P5** | Physics | MINOR | 4D symmetry group may be larger than O_h × Z₂ | Derivation §6.3 |
| **P8** | Physics | MINOR | Improvement factor comparison assumes unit coefficients | Applications §8.4 |

---

## 1. Mathematical Verification Report

### Verdict: PARTIAL — Confidence: Medium-High

### Errors Found

**F4 (HIGH) — Analyticity Gap Formula:**
The Applications file (line 131) states:
$$\Delta E_{12} = E_{\mathbf{8}} - E_{\mathbf{3}} = 8\ln(u_{\mathbf{3}}/u_{\mathbf{8}})$$

Independent re-derivation gives:
$$E_R = -3\ln d_R - 8\ln a_R$$
$$\Delta E_{12} = E_{\mathbf{8}} - E_{\mathbf{3}} = 3\ln(3/8) + 8\ln(u_{\mathbf{3}}/u_{\mathbf{8}})$$

The 3 ln(3/8) ≈ -2.94 term is negative and non-negligible, meaning the actual gap is *smaller* than claimed.

**F1 (MEDIUM) — OS0 Analyticity Argument:**
The proof conflates analyticity in the coupling β with analyticity in spatial position. At finite lattice spacing, Schwinger functions are defined only on discrete lattice sites — they are not analytic functions of continuous position. The proof must specify the interpolation scheme or use the distributional framework (Glimm-Jaffe Ch. 19).

### Warnings

- **F2:** OS3 can be proven independently via commuting observables in the path integral, without requiring OS1 (which is conjectural). Current classification creates a contradiction.
- **F7:** Throughout the proof, "the continuum limit" should be replaced with "any subsequential limit" when C1 is not assumed.
- **F9:** OS4 should be "ESTABLISHED (lattice) / CONDITIONAL (continuum, requires C2)."
- **F3, F5, F8:** Tightness arguments and distributional convergence framework need more explicit treatment.
- **F6:** OS0' growth condition (C=3, α=0) should be stated as a proposition.

### Re-Derived Equations

| Equation | Verified? |
|----------|-----------|
| λ_R = d_R^{3N_s} [a_R(β)]^{8N_s} | ✅ Yes |
| μ(β) = -3 ln 3 - 8 ln u₃(β) | ✅ Yes |
| μ > 0 iff u₃ < 3^{-3/8} | ✅ Yes |
| m_phys = √3 μ/a | ✅ Yes |
| δ_iso ∼ (ap)^4 ≈ 0.066 at a=0.1 fm | ✅ Yes |
| ΔE₁₂ = 8 ln(u₃/u₈) | ❌ Missing 3 ln(3/8) term |
| \|S_n^{(a)}\| ≤ 3^n | ✅ Yes |

---

## 2. Physics Verification Report

### Verdict: PARTIAL — Confidence: Medium

### Major Issues

**P6 (MAJOR) — Global Label Constraint:**
The diagonal transfer matrix is a consequence of the global label constraint from Prop 2.5.2b, which forces all cells to carry the same SU(3) representation. In standard lattice QCD, no such constraint exists — the transfer matrix is dense. This means the FCC lattice theory is a *different* theory from standard SU(3) lattice gauge theory on a hypercubic lattice. Equivalence in the continuum limit requires universality (C3).

The comparison table (Applications §8.6) entry "OS2 (RP): Standard Lattice QCD = Assumed (Wilson action)" is **incorrect** — RP for the Wilson action on hypercubic lattices is PROVEN by Osterwalder-Seiler (1978).

**P4 (SIGNIFICANT) — D₄ Isotropy:**
The verification script (test C5) computes the D₄ fourth-moment tensor for 3D FCC nearest-neighbor vectors and finds ratio = 2 (ideal would be 3). This means the FCC lattice does NOT have exact D₄ isotropy in 3D. The claim may hold for the full 4D lattice including the temporal [111] direction, but this needs explicit verification against Prop 7.4.3.

### Limit Checks

| Limit | Result | Status |
|-------|--------|--------|
| Strong coupling (β → 0) | μ → ∞ (confinement) | ✅ PASS |
| Weak coupling (β → β_c) | μ → 0 (deconfinement) | ✅ PASS |
| Thermodynamic limit (N_s → ∞) | μ N_s-independent | ✅ PASS |
| Continuum limit (a → 0) | Conditional on C1-C3 | CONDITIONAL |
| Large N_c | Not tested | NOT TESTED |

### Experimental Tensions
- CG string tension √σ = 440 MeV is below standard pure-gauge lattice value ~485 MeV (known convention difference)
- Mass gap ~1.5 GeV is below lattice estimates of ~1.7 GeV (consequence of above)
- No other experimental tensions identified

### Framework Consistency
- Dependency chain stella → SU(3) → FCC → Z_FCC → T̂ → RP → mass gap → OS: **consistent**
- Transfer matrix formula used consistently across Thms 7.4.1-7.4.6
- Conjectures C1-C3 clearly enumerated and honestly classified

---

## 3. Literature Verification Report

### Verdict: PARTIAL — Confidence: Medium-High

### Citation Accuracy

| Reference | Verified? | Issue |
|-----------|-----------|-------|
| Osterwalder-Schrader 1973 (CMP 31, 83) | ✅ Verified | — |
| Osterwalder-Schrader 1975 (CMP 42, 281) | ✅ Verified | — |
| Seiler 1982 (LNP 159) | ✅ Verified | Thm 3.1 number unconfirmed |
| Glimm-Jaffe 1987 (Springer) | ✅ Verified | Ch. 19, Prop 6.1.3 unconfirmed |
| Jaffe-Witten 2000 (Clay) | ✅ Verified | — |
| Symanzik 1983 (NPB 226, 187) | ✅ Verified | — |
| Balaban 1987 (CMP 109, 249) | ✅ Verified | Incomplete (2 of 6+ papers) |
| Balaban 1988 (CMP 116, 1) | ✅ Verified | See above |
| Osterwalder-Seiler 1978 (AP 110, 440) | ✅ Verified | — |
| Brydges-Fröhlich-Seiler 1979 (AP 121, 227) | ✅ Verified | — |
| Streater-Wightman 1964 (Princeton) | ✅ Verified | — |

### Missing References
1. **Menetti & Pelissetto, CMP 113 (1987) 369-373** — General proof of OS positivity for Wilson action
2. **Lüscher & Weisz, CMP 97 (1985) 59-77** — Referenced in text but missing from §10
3. **Morningstar & Peardon, PRD 60 (1999) 034509** — Glueball spectrum
4. **Athenodorou & Teper, JHEP 11 (2020) 172** — Updated glueball spectrum
5. **A lattice Boltzmann reference** for D₄ fourth-moment isotropy claim

### Key Issues
- **OS0 naming:** "Analyticity" should be "Temperedness" per standard OS convention (E0)
- **Mass gap:** ~1.5 GeV should be updated to ~1.7 GeV per lattice consensus
- **Edge-of-the-wedge for OS3:** The direct path integral commutativity argument is cleaner and standard
- **D₄ isotropy claim:** Result imported from lattice Boltzmann community without citation
- **Clay Millennium Problem connection:** Accurately and honestly characterized

---

## 4. Consolidated Recommendations

### Priority 1 (Critical — fix before next verification)
1. **Fix analyticity gap formula** (F4): Replace ΔE₁₂ = 8 ln(u₃/u₈) with ΔE₁₂ = 3 ln(3/8) + 8 ln(u₃/u₈)
2. **Resolve D₄ isotropy discrepancy** (P4): Verify whether Prop 7.4.3 establishes exact isotropy in 4D or only in 3D
3. **Fix comparison table** (P10): RP is PROVEN for standard Wilson action (Osterwalder-Seiler 1978), not "assumed"

### Priority 2 (Important — improve rigor)
4. **Clarify OS0 argument** (F1): Use distributional framework for lattice-to-continuum analyticity
5. **Fix OS3 classification** (F2): Use commuting observables as primary proof; ESTABLISHED independently of OS1
6. **Fix OS4 status** (F9/P7): "ESTABLISHED (lattice) / CONDITIONAL (continuum, requires C2)"
7. **Distinguish subsequential limits from the continuum limit** (F7) throughout

### Priority 3 (Moderate — improve completeness)
8. **Add missing references** (L3-L5): Lüscher-Weisz 1985, Menetti-Pelissetto 1987, Morningstar-Peardon 1999
9. **Qualify "automatic Symanzik improvement"** (P9): Rotational part only; O(a²) scalar artifacts remain
10. **Discuss global label constraint implications** (P6): Beyond citing universality C3
11. **Correct OS0 naming convention** (L1) or note deviation from standard
12. **Update mass gap value** (L2) to ~1.7 GeV per lattice consensus

### Priority 4 (Minor — polish)
13. **State OS0' explicitly** (F6): |S_n| ≤ 3^n implies OS0' with C=3, α=0
14. **Make tightness argument explicit** (F3, F8): Cite Glimm-Jaffe Ch. 6
15. **Add large-N_c consistency check** (P3)
16. **Complete Balaban citation** (L3): Note "and subsequent papers"

---

## 5. Verification Scripts

- **Standard verification:** `verification/Phase7/thm_7_4_6_os_axioms.py` (10/10 pass)
- **Adversarial verification:** `verification/Phase7/thm_7_4_6_adversarial_verification.py` (created this session)
- **Plots:** `verification/plots/thm_7_4_6_adversarial_os_axioms.png`

---

## 6. Resolution Status

**All 20 findings resolved: 2026-02-13**

| ID | Severity | Resolution | File(s) Modified |
|----|----------|------------|-----------------|
| F4 | HIGH | Fixed formula: added $3\ln(3/8)$ term | Applications |
| P4 | SIGNIFICANT | Clarified: D₄ isotropy is 4D (24 NN), not 3D (12 NN) | Statement, Derivation |
| P6 | MAJOR | New §3.4 discussing global label constraint implications | Statement |
| F1 | MEDIUM | Distributional framework for lattice-to-continuum analyticity | Statement, Derivation §5.2 |
| F2 | MEDIUM | Commuting-observables proof is primary; OS3 independent of OS1 | All three files |
| F7 | MEDIUM | "Subsequential limits" used where C1 not assumed | Statement, Derivation |
| F9/P7 | MEDIUM | OS4 status split: ✅ lattice / 🔮 continuum (requires C2) | Statement, Applications |
| P9 | MODERATE | "Automatic improvement" qualified: rotational part only | Derivation App C.3 |
| P10 | MODERATE | RP correctly attributed as "Proven (Osterwalder-Seiler 1978)" | Applications §8.6 |
| L1 | MODERATE | Footnote on OS0 naming convention | Statement §3.1 |
| L2 | MODERATE | New §8.3.1 on mass gap scale convention | Applications |
| L3 | MINOR | Balaban citation completed with "and subsequent papers" | Statement §10 |
| L4 | MINOR | Lüscher-Weisz 1985 added as Ref. 11 | Statement §10 |
| L5 | MINOR | Menotti-Pelissetto 1987 added as Ref. 12 | Statement §10 |
| F3/F5 | LOW | Tightness argument made explicit with distributional framework | Derivation App B.2, §5.3 |
| F6 | LOW | New Prop A.2.1: OS0' with C=3, α=0 | Derivation App A.2 |
| P1 | MINOR | $m_\text{lat}$ vs $m_\text{phys}$ clarified with √3 factor | Applications §8.2 |
| P5 | MINOR | 4D FCC symmetry verified computationally | Derivation §6.4 |
| P8 | MINOR | Noted: table shows $\sim$ scaling; exact coefficients geometry-dependent | No change needed |
| P3 | MINOR | N/A: CG is specific to $N_c = 3$ | No change needed |

---

*Verification performed: 2026-02-13*
*Findings resolved: 2026-02-13*
*Protocol: Multi-agent adversarial (3 agents: Math, Physics, Literature)*
*Agents: Claude Opus 4.6*
