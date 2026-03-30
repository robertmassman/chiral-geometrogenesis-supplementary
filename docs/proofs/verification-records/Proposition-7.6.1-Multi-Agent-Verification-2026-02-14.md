# Proposition 7.6.1: FCC Averaging Kernel — Multi-Agent Verification Report

**Date:** 2026-02-14
**Theorem:** Proposition 7.6.1 — FCC Averaging Kernel on the D₄ Lattice
**Classification:** 🔶 NOVEL (FCC-specific kernel construction) / ✅ ESTABLISHED (Balaban averaging framework)
**Overall Verdict:** ✅ VERIFIED — all 3 errors, 8 warnings, and 6 literature findings resolved (2026-02-14)

---

## Verification Agents

| Agent | Role | Verdict | Confidence |
|-------|------|---------|------------|
| **Literature** | Citation accuracy, prior work, standard results | Partial | Medium-High |
| **Mathematics** | Algebraic correctness, proof completeness, logical validity | Partial | Medium |
| **Physics** | Physical consistency, limiting cases, framework compatibility | Partial | Medium |

---

## Executive Summary

The core mathematical claims of Proposition 7.6.1 are **correct and well-established**:

- **[D₄ : 2D₄] = 16** — verified by two independent methods (algebraic and determinant)
- **Gauge covariance** of path-based averaging — standard result (Balaban Theorem 3.1)
- **D₄ self-coarsening** — verified through 3 levels of blocking
- **25 paths per direction** (1 straight + 24 detour) — verified for all 24 directions
- **Fourth-moment isotropy** — confirmed to machine precision

However, three significant findings require correction before the proposition is fully rigorous:

1. **E1 (SIGNIFICANT):** Incorrect explicit coset representatives in §5.3/Appendix A (duplicates present)
2. **E2 (SIGNIFICANT):** Unjustified transition from Eq. (7.15) to Eq. (7.17) in the smallness bound
3. **E3 (MODERATE):** Dimensional inconsistency in the formal statement of Part (c)

---

## Findings by Category

### ERRORS (Require Correction)

#### E1: Incorrect Explicit Coset Representatives
- **Severity:** SIGNIFICANT
- **Location:** Derivation file, §5.3, Appendix A
- **Agent:** Mathematics
- **Detail:** Representatives #15 (−1,−1,0,0) and #2 (1,1,0,0) are in the **same** 2D₄ coset because their difference (2,2,0,0) ∈ 2D₄. Similarly, representatives #16 (−1,−1,−1,−1) and #8 (1,1,1,1) are in the same coset because (2,2,2,2) ∈ 2D₄. The stated orbit decomposition 1+12+1+1+1=16 is also incorrect.
- **Impact:** The coset **count** (16) is correct by both algebraic methods. The explicit enumeration contains duplicates. Downstream results (Parts b–d) depend only on the count, not on specific representatives.
- **Resolution:** Replace the representative table with canonical representatives derived from the D₄ basis {e₁−e₂, e₂−e₃, e₃−e₄, e₃+e₄}: all 16 binary combinations Σᵢ εᵢbᵢ with εᵢ ∈ {0,1}. Also correct the claim that r_α ∈ {0,1}⁴ (some canonical representatives have coordinates outside this range, e.g., (0,0,2,0)).

#### E2: Unjustified Transition in Smallness Bound (Eqs. 7.15 → 7.17)
- **Severity:** SIGNIFICANT
- **Location:** Derivation file, §7.3; Statement file, Part (c)
- **Agents:** Mathematics, Physics
- **Detail:** Eq. (7.15) derives ‖Q̄ − U_γ₀‖ ≤ C_avg · g_k^{1−δ} (no η_k dependence in lattice units). Eq. (7.17) claims ‖Q − U_γ₀‖ ≤ C'_avg · g_k · η_k^{d/2} without proper justification. The exponent change from g_k^{1−δ} to g_k · η_k² and the absorption of the δ-dependent factor are not rigorously shown.
- **Impact:** The formal statement of Part (c) uses the Balaban form with g_k η_k^{d/2}, which is needed for the inductive RG argument but is not properly derived from the preceding analysis.
- **Resolution:** State the bound clearly in two forms: (i) lattice units: ‖Q − U_direct‖ ≤ C_avg g_k^{1−δ}; (ii) explain that the η_k^{d/2} form arises when tracking physical units. Preserve the δ exponent rather than claiming it can be "absorbed."

#### E3: Dimensional Inconsistency in Formal Statement
- **Severity:** MODERATE
- **Location:** Statement file, §1, Part (c), dimension check paragraph
- **Agent:** Mathematics
- **Detail:** The text claims η_k^{d/2} = η_k² has dimension [length]² while ‖Q − U‖ is dimensionless, making the inequality dimensionally invalid as written. The issue is that the bound is dimensionless in lattice units (η_k = 1) where writing η_k² is redundant.
- **Impact:** Confusing presentation but does not invalidate mathematical content.
- **Resolution:** Clarify that in lattice units η_k = 1 and the bound reduces to C_avg · g_k. In physical units, F_p carries dimension [mass]² which cancels the area factor, keeping the bound dimensionless.

---

### WARNINGS (Should Be Addressed)

| ID | Description | Agent | Location |
|----|-------------|-------|----------|
| W1 | Small-field region Ω not precisely defined relative to Balaban's framework | Math | Statement §1 |
| W2 | Exclusion of paths of length ≥ 4 is a design choice, not mathematically justified | Math | Derivation §6.1 |
| W3 | No explicit bound on g_k η_k for SU(3) projection to be well-defined | Math, Physics | Derivation §6.4 |
| W4 | Path count of 24 three-step paths numerically verified but not analytically proven | Math | Derivation §6.1 |
| W5 | Bound N_△^max ≤ 6 stated without proof | Math | Derivation §7.3 |
| W6 | §5.2 narrative about mod-2 → mod-4 refinement is misleading; basis argument is the correct approach | Math | Derivation §5.2 |
| W7 | Polar decomposition formula oversimplified (U(3) vs SU(3) correction) | Physics | Derivation §6.4 |
| W8 | C_avg ratio discrepancy: text claims ~2.7, script gives ~1.87 | Physics | Derivation §7.4, Test 12 |

---

### LITERATURE FINDINGS

| ID | Description | Severity |
|----|-------------|----------|
| L1 | Dimock's papers treat scalar ϕ⁴, NOT gauge theory; claim about "separating lattice-dependent parts" not supported | Medium |
| L2 | Celmaster (1982) characterized as "perturbative properties only" — inaccurate, follow-up papers include Monte Carlo | Low |
| L3 | W(D₄) (order 192) called "lattice point group" in symbol table — actually full automorphism group is W(F₄) of order 1152 (includes S₃ triality) | Low |
| L4 | Missing references: Celmaster (1983), Celmaster & Kovacs (1986), Celmaster & Moriarty (1986) for non-perturbative BCH results | Low |
| L5 | D₄ self-duality should say "up to scaling" not "up to rotation" | Low |
| L6 | "FCC" vs "BCH" (body-centered hypercubic) terminology in 4D should be noted | Low |

---

### POSITIVE CONFIRMATIONS

| Claim | Status | Verification Method |
|-------|--------|-------------------|
| [D₄ : 2D₄] = 16 | ✅ Confirmed | Algebraic + determinant + numerical (97,241 points) |
| 24 NN vectors for D₄ | ✅ Confirmed | Literature (Conway & Sloane, Nebe catalogue) |
| Voronoi cell = 24-cell | ✅ Confirmed | Literature |
| det(D₄) = 4 | ✅ Confirmed | Gram matrix computation |
| |W(D₄)| = 192 | ✅ Confirmed | Standard Weyl group formula 2^{n-1} · n! |
| 25 paths per direction (all 24 dirs) | ✅ Confirmed | Numerical enumeration |
| Gauge covariance | ✅ Confirmed | Analytic proof + numerical (error < 10⁻¹⁴) |
| D₄ fourth-moment isotropy | ✅ Confirmed | Numerical (deviation < 10⁻¹⁵) |
| Self-coarsening (3 levels) | ✅ Confirmed | Numerical |
| C_avg = 36√3/25 · C_F ≈ 2.494 C_F | ✅ Confirmed | Independent arithmetic |
| Novelty of FCC averaging kernel | ✅ Confirmed | Literature search (no prior work found) |

---

## Adversarial Physics Verification (Computational)

**Script:** `verification/Phase7/prop_7_6_1_adversarial_physics.py`
**Result:** 10/10 tests PASSED

| Test | Claim | Result |
|------|-------|--------|
| ADV-1 | Coset exhaustiveness (97,241 D₄ points in ±10) | PASS |
| ADV-2 | Path count = 25 for all 24 directions | PASS |
| ADV-3 | Gauge covariance under extreme transforms (50 trials) | PASS (max error 8.0×10⁻¹⁵) |
| ADV-4 | Smallness bound scaling (linear in ε) | PASS (slope = 1.018) |
| ADV-5 | SU(3) projection near Gribov horizon | PASS (200/200 valid in small-field) |
| ADV-6 | Multi-level self-coarsening (3 levels) | PASS |
| ADV-7 | BCH expansion accuracy (deviation ~ F) | PASS (ratio = 1.000) |
| ADV-8 | Fourth-moment isotropy after averaging | PASS (deviation < 10⁻¹⁵) |
| ADV-9 | FCC vs hypercubic C_avg ratio | PASS (ratio = 2.56) |
| ADV-10 | Large-field pathology scan (ε: 0.001 to 10) | PASS (no failures) |

**Plots:** `verification/plots/prop_7_6_1_adversarial_physics.png`

---

## Recommended Actions

### Priority 1 (Before status upgrade)
1. **Fix coset representatives** (E1): Replace table in §5.3/Appendix A with canonical basis-derived representatives
2. **Fix smallness bound transition** (E2): State bound in both lattice and physical units; preserve δ exponent
3. **Fix dimensional analysis** (E3): Clarify lattice-unit vs physical-unit conventions

### Priority 2 (Strengthening)
4. Prove path count = 24 analytically (W4)
5. Prove N_△^max ≤ 6 (W5)
6. Reconcile C_avg ratio (W8): text claims ~2.7, numerical gives ~2.56
7. Correct Celmaster characterization (L2)
8. Clarify Dimock's scope (L1)
9. Note W(D₄) vs Aut(D₄) = W(F₄) distinction (L3)

### Priority 3 (Optional improvements)
10. Add U(1) Abelian limit discussion
11. Add missing Celmaster follow-up references (L4)
12. Quantify "comparable or better" control claim for C_avg

---

## Verification Metadata

| Field | Value |
|-------|-------|
| Verification date | 2026-02-14 |
| Agents used | 3 (Literature, Mathematics, Physics) |
| Adversarial tests | 10/10 passed |
| Original verification | 12/12 passed |
| Files reviewed | 3 (Statement, Derivation, Applications) + Research Note |
| Status | 🔶 NOVEL ✅ VERIFIED — all findings resolved (2026-02-14) |

---

## Corrections Applied (2026-02-14)

All 3 errors (E1–E3), 8 warnings (W1–W8), and 6 literature findings (L1–L6) from this verification report have been resolved:

| Finding | Resolution |
|---------|-----------|
| **E1** | Coset representatives replaced with canonical $D_4$-basis construction ($r(\varepsilon) = \sum \varepsilon_i b_i$); 2 duplicate pairs removed; 2 missing cosets added; orbit decomposition corrected |
| **E2** | Smallness bound restated in lattice units with $\delta$ exponent preserved ($C_\text{avg} g_k^{1-\delta}$); physical-unit form explained separately; unjustified absorption removed |
| **E3** | Dimensional analysis rewritten — bound is dimensionless in lattice units ($\eta_k = 1$); $\eta_k^{d/2}$ factor identified as Balaban's physical-unit convention |
| **W1** | Small-field region $\Omega$ defined explicitly in Part (c) |
| **W2** | Path length $\geq 4$ exclusion justified (higher-order in $\eta_k$, larger $C_\text{avg}$, no isotropy benefit) |
| **W3** | Explicit well-definedness condition stated: $g_k < g_k^* \sim O(1)$ suffices for SU(3) projection |
| **W4** | Path count = 24 proven analytically via coordinate-slot argument (Cases A, B, C) |
| **W5** | $N_\triangle^{\max} = 3$ proven (tighter than claimed $\leq 6$): 16 paths have $N_\triangle = 1$, 8 have $N_\triangle = 3$. Triangle area corrected to $A_\triangle = \eta_k^2 \sqrt{3}/2$. $C_\text{avg} \approx 2.49\, C_F$ unchanged (area and $N_\triangle$ corrections cancel). |
| **W6** | §5.2 rewritten to lead with basis argument; mod-2/mod-4 narrative moved to remark |
| **W7** | Polar decomposition formula corrected: two-step process ($GL(3) \to U(3)$ via polar, then $U(3) \to SU(3)$ via determinant phase) |
| **W8** | $C_\text{avg}$ ratio reconciled: noted that $\mathbb{Z}^4$ detours are 4-step (not 3-step), making direct comparison convention-dependent; Test 12 value of $\approx 1.87$ identified as equal-weight convention |
| **L1** | Dimock scope corrected: scalar $\phi^4$ (not gauge theory); abstract framework applicability noted |
| **L2** | Celmaster characterization updated: includes Monte Carlo follow-up work |
| **L3** | $W(D_4)$ (order 192) vs $\text{Aut}(D_4) = W(F_4)$ (order 1152) distinction noted in symbol table |
| **L4** | Added Celmaster (1983), Celmaster & Kovacs (1986), Celmaster & Moriarty (1986) references |
| **L5** | $D_4$ self-duality corrected: "up to scaling" (not "up to rotation") |
| **L6** | FCC vs BCH terminology note added in §3.2 |

---

*Generated by multi-agent verification protocol. See [docs/verification-prompts/agent-prompts.md](../../verification-prompts/agent-prompts.md) for agent specifications.*
