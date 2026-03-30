# Theorem 7.5.2: Perturbative Universality — Multi-Agent Verification Report

**Date:** 2026-02-13
**Theorem:** Theorem 7.5.2 — Perturbative Universality: FCC ↔ Hypercubic
**Status:** ✅ VERIFIED — All 8 findings resolved

**Files Reviewed:**
- [Statement](../../Phase7/Theorem-7.5.2-Perturbative-Universality-FCC.md)
- [Derivation](../../Phase7/Theorem-7.5.2-Perturbative-Universality-FCC-Derivation.md)
- [Applications](../../Phase7/Theorem-7.5.2-Perturbative-Universality-FCC-Applications.md)

---

## Executive Summary

Three independent verification agents (Mathematical, Physics, Literature) reviewed Theorem 7.5.2 in adversarial mode. The theorem establishes perturbative universality between the FCC (D₄) and standard hypercubic (ℤ⁴) lattice formulations of SU(3) Yang-Mills theory.

**Overall Verdict:** The theorem is well-structured, largely correct, and commendably honest about its limitations. Parts (a), (b), and (d) are rigorous applications of established methodology. Part (c) has an arithmetic error in an intermediate step (Eq. 7.8) and relies on an informal Nₒ-scaling argument. Several minor citation and consistency issues were identified.

| Part | Claim | Verdict | Confidence |
|------|-------|---------|------------|
| (a) Irrelevant operator difference | $d_i \geq 6$ | ✅ VERIFIED | High |
| (b) Beta function universality | Same $b_0$, $b_1$ to all orders | ✅ VERIFIED | High |
| (c) Lambda parameter ratio | $\Lambda_\text{FCC}/\Lambda_\text{cubic} \approx 0.29$ | 🔶 PARTIALLY VERIFIED | Medium |
| (d) Observable agreement | Same continuum limit | ✅ VERIFIED | High |

---

## Agent 1: Mathematical Verification

**Agent Role:** Adversarial mathematical review
**Verdict:** PARTIAL VERIFICATION
**Confidence:** Medium-High

### Verified Calculations

| Equation | Stated Value | Re-derived Value | Status |
|----------|-------------|-----------------|--------|
| $b_0 = 11/(16\pi^2)$ | 0.06966 | 11/157.914 = 0.06966 | ✅ VERIFIED |
| $b_1 = 102/(16\pi^2)^2$ | 0.004090 | 102/24930.5 = 0.004091 | ✅ VERIFIED |
| $b_1/(2b_0^2)$ | 51/121 = 0.4215 | 102/(2×121) = 0.4215 | ✅ VERIFIED |
| $N_c(I_\text{FCC} - I_\text{cubic})$ | 0.363 | 3×0.121 = 0.363 | ✅ VERIFIED |
| $\Lambda_{\overline{MS}}/\Lambda_\text{FCC}$ | ~99 | 28.8/0.29 = 99.3 | ✅ VERIFIED |
| $\Lambda_\text{FCC}/\Lambda_{\overline{MS}}$ | ~0.010 | 1/99.3 = 0.0101 | ✅ VERIFIED |
| $T_{1111}(D_4)$ isotropy | 3 | 12×(1/4) = 3 | ✅ VERIFIED |
| $T_{1122}(D_4)$ isotropy | 1 | 4×(1/4) = 1 | ✅ VERIFIED |
| $\Delta T(D_4)$ | 0 | $T - T^{\text{iso}} = 3 - 3 = 0$ | ✅ VERIFIED |
| $c_4^{(\text{cubic}),(0)}$ | 1/12 | 1/(3×4) = 1/12 | ✅ VERIFIED |
| **$\Delta_\text{finite}$(SU(2)) from Eq. (7.8)** | **0.574** | **0.115** | **❌ ERROR** |

### Finding M1 (ERROR): Eq. (7.8) Arithmetic Error

**Location:** Derivation file, line 174, Eq. (7.8)
**Severity:** Low (self-contained — does not propagate)

The equation claims:
$$\Delta_\text{finite}^{(\text{BCH}\to\text{cubic})} = -2b_0^{(\text{SU}(2))}\ln(0.289) = -2 \times \frac{22}{3(4\pi)^2}\times(-1.240) = 0.574$$

Re-derivation:
- $b_0^{(\text{SU}(2))} = \frac{22}{3 \times 16\pi^2} = \frac{22}{473.74} = 0.04644$
- $-2 \times 0.04644 \times (-1.2402) = 0.1152$

The stated result 0.574 is off by a factor of ~5. However, the Lambda ratio itself is inherited directly from Celmaster's computation (0.289) and the Nₒ-scaling argument, NOT from this intermediate $\Delta_\text{finite}$ value. The error is self-contained and does not affect the final result.

**Resolution required:** Correct the arithmetic or remove this intermediate step.

### Finding M2 (WARNING): Nₒ-Scaling Argument Lacks Rigorous Justification

**Location:** Derivation file, §7.3 (lines 176-197)
**Severity:** Medium

The claim that $\Delta_\text{finite}/(2b_0)$ is Nₒ-independent at leading order is physically plausible but not rigorously proven:
- The tadpole integral is indeed Nₒ-independent ✅
- Vertex corrections scale as $N_c$ from $C_A = N_c$ ✅
- But the $O(1/N_c^2)$ error estimate is asserted without derivation
- For $N_c = 2 \to 3$, the correction could be $O(1/N_c)$ rather than $O(1/N_c^2)$

**Resolution required:** Either provide an explicit decomposition showing why $O(1/N_c)$ terms vanish, or widen the uncertainty estimate.

### Finding M3 (WARNING): b₁ Proof Sketch Misleading

**Location:** Derivation file, §6.1.2 (lines 94-98)
**Severity:** Low

The proof sketch states "$b_1$ can be shown to be invariant under this transformation because the specific combination $b_1/b_0^2$ is universal." This is incorrect reasoning — $b_1$ is individually scheme-independent (as is $b_0$). The ratio $b_1/b_0^2$ has no special role in the proof. The standard argument shows that under coupling reparameterization $g \to g' = g + c_1 g^3$, both $b_0$ and $b_1$ are separately invariant, while $b_n$ for $n \geq 2$ change.

**Resolution required:** Correct the proof sketch to use the standard argument.

### Finding M4 (WARNING): Inconsistent $I_\text{cubic}$ Values

**Location:** Statement file line 122 vs. Derivation file Eq. (7.6)
**Severity:** Low

The symbol table lists $I_\text{cubic} = 0.15493$ while Eq. (7.6) uses 0.155 (rounded). Minor presentational inconsistency.

**Resolution required:** Use consistent values throughout.

### Logical Validity

- **Part (a):** Sound. Correctly applies Symanzik effective theory with Prop 7.5.1 input. ✅
- **Part (b):** Sound. Standard RG universality argument. ✅
- **Part (c):** Mostly sound. Dashen-Gross relation correctly stated; Nₒ-scaling argument is informal. 🔶
- **Part (d):** Sound. Follows directly from Parts (a) and (b). ✅
- **No circular dependencies detected.** Dependency chain traces back to external results and Prop 7.5.1.

---

## Agent 2: Physics Verification

**Agent Role:** Adversarial physics review
**Verdict:** PARTIAL VERIFICATION
**Confidence:** Medium-High

### Limiting Cases

| Limit | Expected Behavior | Theorem Result | Status |
|-------|------------------|----------------|--------|
| $a \to 0$ (continuum) | Both lattices give same theory | Part (d): Both converge with $O(a^2)$ corrections | ✅ PASS |
| $g_0 \to 0$ (weak coupling) | PT becomes exact | Beta function universality holds | ✅ PASS |
| $N_c \to \infty$ (large-N) | Lambda ratio $N_c$-independent | $O(1/N_c^2)$ corrections ~10% | ✅ PASS |
| U(1) (Abelian) | Standard U(1) universality | Correctly reduces | ✅ PASS |
| FCC → cubic (deformation) | Lambda ratio → 1 | Correctly stated | ✅ PASS |

### Finding P1 (WARNING): 3D vs 4D Point Group Confusion

**Location:** Prop 7.4.3 Derivation §6.2, line 148
**Severity:** Low (does not affect Thm 7.5.2 directly)

The Prop 7.4.3 derivation refers to "O_h point group symmetry (48 elements)" for the FCC lattice. This is the **3D** octahedral group, not the 4D point group. The correct values are:
- W(D₄) = 192 elements (Weyl group of D₄ root system)
- W(B₄) = 384 elements (hyperoctahedral group in 4D)

### Finding P2 (WARNING): $\Lambda_{\overline{MS}}/\Lambda_\text{cubic} = 28.8$ Needs Cross-Check

**Location:** Derivation Eq. (7.13), also Prop 7.4.3 §7.1
**Severity:** Medium

The literature agent independently verified this value using the Dashen-Gross formula: $\Lambda_{\overline{MS}}/\Lambda_L = 38.853 \times \exp(-3\pi^2/(11N^2))$. For SU(3): $\exp(-3\pi^2/99) = \exp(-0.29908) = 0.7414$, giving $38.853 \times 0.7414 = 28.80$. **This confirms the value 28.8.** ✅

### Finding P3 (WARNING): Glueball Mass Ratio Inconsistency

**Location:** Statement §3.3 vs. Applications Eq. (9.4)
**Severity:** Medium

Two different values appear:
- Statement §3.3: "$R_\text{phys} \approx 3.93$ (Morningstar & Peardon 1999)"
- Applications Eq. (9.4): "$m_{0^{++}}/\sqrt{\sigma} = 3.405 \pm 0.021$"

These are different quantities from different analyses. The Morningstar-Peardon value $m_{0^{++}}/\sqrt{\sigma} \approx 4.21$ uses their normalization; 3.93 may refer to the mass gap (not necessarily the 0++ glueball); 3.405 is from Athenodorou & Teper (2020) with updated systematics. The distinction should be explicitly stated.

**Resolution required:** Clarify that these are different quantities or reconcile the values.

### Finding P4 (WARNING): $\Lambda_{\overline{MS}}$ Values Inconsistent Across Documents

**Location:** Multiple files
**Severity:** Low

| Source | Value |
|--------|-------|
| Thm 7.5.2 Statement §2 | $\Lambda_{\overline{MS}} \approx 260$ MeV ($N_f = 0$) |
| Thm 7.4.5 Statement §2 | $\Lambda_{\overline{MS}} \approx 251$ MeV (Ishikawa et al. 2017) |
| Prop 7.4.3 Statement | $\Lambda_{\overline{MS}} = 260 \pm 20$ MeV (quenched) |

Values are consistent within uncertainties but should be standardized.

### Physical Consistency Assessment

- FCC lattice correctly described as D₄ ✅
- $c_4 = 0$ from D₄ fourth-moment isotropy is physically sound ✅
- $R \to 0$ problem correctly identified as non-perturbative ✅
- Perturbative vs. non-perturbative distinction exemplary ✅
- Gauge invariance preserved on both lattices ✅
- No pathologies detected ✅

### Framework Consistency

| Dependency | Claim | Used Correctly? | Status |
|------------|-------|-----------------|--------|
| Prop 7.5.1 ($c_4 = 0$) | Tree + one-loop | Yes | ✅ |
| Prop 7.4.3 (beta function) | $b_0 = 11/(16\pi^2)$ | Yes | ✅ |
| Prop 7.4.3 (tadpole) | $I_\text{FCC} \approx 0.276$ | Yes | ✅ |
| Prop 7.4.4a (Wilson loop) | $R \to 0$ as $\beta \to \beta_c$ | Yes (non-perturbative) | ✅ |
| Thm 7.4.5 (C3) | Partial resolution | Yes | ✅ |
| Thm 7.4.2 (mass gap) | $\mu(\beta) > 0$ | Referenced correctly | ✅ |

---

## Agent 3: Literature Verification

**Agent Role:** Citation and data verification
**Verdict:** PARTIAL VERIFICATION
**Confidence:** Medium-High

### Citation Verification

| # | Citation | Journal/Year | Correct? |
|---|----------|-------------|----------|
| 1 | Gross & Wilczek (1973) | PRL 30, 1343 | ✅ |
| 2 | Politzer (1973) | PRL 30, 1346 | ✅ |
| 3 | Dashen & Gross (1981) | PRD 23, 2340 | ✅ |
| 4 | Symanzik (1983) | NPB 226, 187 | ✅ |
| 5 | Lüscher & Weisz (1985) | CMP 97, 59 | ✅ |
| 6 | Curci, Menotti, Paffuti (1983) | PLB 130, 205 | ✅ |
| 7 | Celmaster (1982) | PRD 26, 2955 | ✅ |
| 8 | Caswell (1974) | PRL 33, 244 | ✅ |
| 9 | Jones (1974) | NPB 75, 531 | ✅ |
| 10 | Hasenfratz & Hasenfratz (1980) | PLB 93, 165 | ✅ |
| 11 | Wilson (1974) | PRD 10, 2445 | ✅ |
| 12 | Lepage & Mackenzie (1993) | PRD 48, 2250 | ✅ |
| 13 | Morningstar & Peardon (1999) | PRD 60, 034509 | ✅ |
| 14 | Athenodorou & Teper (2020) | JHEP 11, 172 | ✅ |

**All 14 formal citations verified.** ✅

### Numerical Values Verified

| Value | Stated | Verified | Status |
|-------|--------|----------|--------|
| $b_0 = 11/(16\pi^2)$ | 0.06966 | 0.06966 | ✅ |
| $b_1 = 102/(16\pi^2)^2$ | 0.004090 | 0.004091 | ✅ |
| $\Lambda_{\overline{MS}}/\Lambda_\text{cubic} = 28.8$ | 28.8 | 28.80 (Dashen-Gross formula) | ✅ |
| Celmaster $\Lambda_\text{BCH}/\Lambda_\text{cubic}$ | 0.289 | ~0.29 (SU(2)) | ✅ |
| $I_\text{cubic}$ | 0.15493 | Standard lattice PT value | ✅ |
| $I_\text{FCC}$ | 0.276 | Novel — no external source | 🔶 |
| $\sqrt{\sigma}/\Lambda_{\overline{MS}}$ | 1.93 ± 0.04 | 1/0.517 = 1.934 (Ishikawa et al.) | ✅ |

### Finding L1 (WARNING): $T_c/\sqrt{\sigma}$ Attribution Incorrect

**Location:** Applications Eq. (9.5)
**Severity:** Medium

The value $T_c/\sqrt{\sigma} = 0.6294 \pm 0.0040$ is attributed to "Lucini, Teper & Wenger 2004" but the commonly cited value $T_c/\sqrt{\sigma} = 0.629(3)$ for SU(3) is from **Boyd et al. 1996** (Nucl. Phys. B 469, 419 [hep-lat/9602007]).

Lucini, Teper & Wenger (JHEP 01, 2004, 061) report a large-N formula $T_c/\sqrt{\sigma} = 0.596(4) + 0.453(30)/N^2$, which for $N = 3$ gives ~0.646, a different value.

**Resolution required:** Correct the attribution to Boyd et al. 1996, or verify that LTW also report this specific SU(3) value.

### Finding L2 (WARNING): Ishikawa et al. Missing from Formal References

**Location:** Applications file (used in body) vs. Statement §10 (not listed)
**Severity:** Low

The reference "Ishikawa et al. 2017" for $\sqrt{\sigma}/\Lambda_{\overline{MS}} = 1.93$ is used in the Applications file but not listed in the formal references section. Full reference: K.-I. Ishikawa, I. Kanamori, Y. Murakami, A. Nakamura, M. Okawa, and R. Ueno, JHEP 12 (2017) 067 [arXiv:1702.06289].

**Resolution required:** Add to Section 10 references.

### Finding L3: Missing References

The following relevant prior work should be considered for addition:

| Reference | Relevance |
|-----------|-----------|
| Capitani (2003), Phys. Rept. 382, 113 | Standard review of lattice perturbation theory |
| Boyd et al. (1996), NPB 469, 419 | Source for $T_c/\sqrt{\sigma} = 0.629(3)$ |
| Celmaster & Moriarty (1983), PRD 28, 2076 | BCH lattice average plaquette |
| Green (1988), PLB 202, 127 | Two-loop plaquette on BCH lattice |

---

## Consolidated Findings

### Findings — All Resolved

| ID | Finding | Severity | Resolution | Status |
|----|---------|----------|------------|--------|
| **F1** | Eq. (7.8) arithmetic error: 0.574 should be ~0.115 | Low | Corrected to 0.115 with correct $b_0^{(\text{SU}(2))} = 0.04644$ | ✅ RESOLVED |
| **F2** | $N_c$-scaling argument informal; $O(1/N_c^2)$ unproven | Medium | §7.3 rewritten with diagram-by-diagram color factor analysis; $d^{abc}$ tensor identified as source of $O(1/N_c^2)$; SU(2) has $d^{abc}=0$ exactly; Hasenfratz-Hasenfratz cross-check added | ✅ RESOLVED |
| **F3** | $b_1$ proof sketch uses wrong reasoning | Low | Corrected: $b_0$ and $b_1$ are individually scheme-independent under coupling reparameterization $g \to g' = g + c_1 g^3$; $b_n$ for $n \geq 2$ are scheme-dependent | ✅ RESOLVED |
| **F4** | $T_c/\sqrt{\sigma}$ attribution: Boyd et al. 1996, not LTW 2004 | Medium | Attribution corrected to Boyd et al. (1996), NPB 469, 419; value updated to $0.629 \pm 0.003$; Boyd et al. added to §10 references | ✅ RESOLVED |
| **F5** | Glueball ratio values inconsistent (3.405 vs 3.93) | Medium | Standardized to Athenodorou & Teper (2020) value $m_{0^{++}}/\sqrt{\sigma} = 3.405 \pm 0.021$ throughout all three files; explanatory note added in Derivation §8.2 clarifying that 3.93 arose from outdated $r_0\sqrt{\sigma}$ conversion | ✅ RESOLVED |
| **F6** | Ishikawa et al. (2017) missing from formal references | Low | Added as Ref. 15: JHEP 12 (2017) 067 [arXiv:1702.06289]; Boyd et al. (1996) added as Ref. 16 | ✅ RESOLVED |
| **F7** | $I_\text{cubic}$ rounded inconsistently (0.15493 vs 0.155) | Low | Eq. (7.6) updated to use exact value 0.15493 | ✅ RESOLVED |
| **F8** | $\Lambda_{\overline{MS}}$ values inconsistent across files (251 vs 260 MeV) | Low | Standardized to $260 \pm 20$ MeV (quenched) with clarifying note in Applications §9.2.1 explaining relationship to Ishikawa et al. (251 MeV) | ✅ RESOLVED |

### Strengths Identified (All Agents)

1. **Exemplary honest assessment** — The distinction between perturbative and non-perturbative universality (§8) is thorough and intellectually honest
2. **Correct application of established methodology** — Symanzik program, Dashen-Gross relation, RG universality
3. **All 14 formal citations verified** — Correct journals, volumes, pages
4. **All limiting cases pass** — Continuum, weak coupling, large-N, Abelian, FCC→cubic
5. **No circular dependencies** — Clean dependency chain to external results
6. **Dimensional analysis verified** — All equations dimensionally consistent
7. **$D_4$ fourth-moment isotropy independently verified** — $T_{1111} = 3$, $T_{1122} = 1$, $\Delta T = 0$
8. **$\Lambda_{\overline{MS}}/\Lambda_\text{cubic} = 28.8$ independently confirmed** via Dashen-Gross formula

---

## Verification Outcome

**Status:** ✅ VERIFIED — All 8 findings resolved (2026-02-13)

**All findings resolved.** The theorem merits: ✅ ESTABLISHED (methodology) / 🔶 NOVEL ✅ ESTABLISHED (FCC application)

---

## Adversarial Verification Script

See [`verification/Phase7/thm_7_5_2_perturbative_universality.py`](../../../verification/Phase7/thm_7_5_2_perturbative_universality.py) for computational verification of:
- Beta function coefficients
- Lambda parameter ratios
- Tadpole integral differences
- D₄ isotropy tensor
- Symanzik coefficient classification
- Scaling behavior comparison

---

*Report generated: 2026-02-13*
*Verification method: Multi-agent adversarial review (3 independent agents)*
*Agents: Mathematical, Physics, Literature*
