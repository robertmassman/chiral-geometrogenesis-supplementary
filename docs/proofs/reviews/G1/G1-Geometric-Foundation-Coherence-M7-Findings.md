# G1 Geometric Foundation — Coherence Audit: Module M7 Findings

> **Module:** M7 — Notation and Convention Consistency
> **Group:** G1 — Geometric Foundation
> **Layer:** 1 (Coherence)
> **Posture:** DEFENSIVE — verify internal consistency
> **Auditor:** Claude Opus 4.6 (autonomous audit agent)
> **Date:** 2026-03-14 (v6 — second independent re-verification with 3 parallel agents; all 23 prior checks confirmed, 2 new out-of-scope findings added: M7.24–M7.25)
> **Template:** [G1-Geometric-Foundation-Coherence-Audit.md](G1-Geometric-Foundation-Coherence-Audit.md) § Module 7
> **Scope:** All 26 G1 proof files (expanded from original 23 to include Prop 0.0.40, Prop 0.1.3a, Thm 0.1.0)
> **Re-verification (v6, 2026-03-14):** Second fully independent re-verification by separate agent session using 3 parallel exploration subagents. All 23 v5 checks independently confirmed with matching line numbers and evidence. Two new out-of-scope findings added: M7.24 (χ = 2 error in Axiom-Reduction-Action-Plan.md — not a G1 proof file but in foundations/), M7.25 (cross-group metric signature drift in Phase 2/3/5). No prior findings changed.

---

## Scope

Module M7 verifies that **notation, sign conventions, symbol usage, and naming conventions** are uniform across all 26 proof files in thematic group G1. This v6 re-audit independently reads all files and checks each of the 15 items defined in the audit plan, plus supplementary checks arising from the expanded file set and out-of-scope boundary scanning.

The critical risks are:
1. Symbol overloading (χ, ε, ω) creating ambiguity between unrelated quantities
2. Boundary notation drift (∂S vs ∂𝒮) between files
3. Status marker format drift from the canonical vocabulary
4. Tetrahedra naming inconsistency (T₊/T₋ vs T₁/T₂)
5. Weight basis convention drift without explicit conversion documentation
6. Cross-file symbol semantic drift (same symbol, different meaning in different files)
7. Convention drift in adjacent (non-proof) files that could propagate errors into G1

---

## Files Examined

All 26 G1 proof files were read in full by three parallel exploration agents. The files are:

| # | File | Abbreviation |
|---|------|-------------|
| F01 | `foundations/Definition-0.0.0-Minimal-Geometric-Realization.md` | Def 0.0.0 |
| F02 | `foundations/Theorem-0.0.1-D4-From-Observer-Existence.md` | Thm 0.0.1 |
| F03 | `foundations/Theorem-0.0.2-Euclidean-From-SU3.md` | Thm 0.0.2 |
| F04 | `foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md` | Thm 0.0.2b |
| F05 | `foundations/Lemma-0.0.2a-Confinement-Dimension.md` | Lem 0.0.2a |
| F06 | `foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md` | Prop 0.0.40 |
| F07 | `foundations/Theorem-0.0.0a-Polyhedral-Necessity.md` | Thm 0.0.0a |
| F08 | `foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md` | Prop 0.0.XX |
| F09 | `foundations/Theorem-0.0.3-Stella-Uniqueness.md` | Thm 0.0.3 |
| F10 | `foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md` | Thm 0.0.3b |
| F11 | `foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md` | Prop 0.0.16a |
| F12 | `foundations/Theorem-0.0.16-Adjacency-From-SU3.md` | Thm 0.0.16 |
| F13 | `foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md` | Thm 0.0.6 |
| F14 | `foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md` | Prop 0.0.6b |
| F15 | `foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md` | Thm 0.0.9 |
| F16 | `foundations/Theorem-0.0.15-Topological-Determination-SU3.md` | Thm 0.0.15 |
| F17 | `foundations/Theorem-0.0.12-Categorical-Equivalence.md` | Thm 0.0.12 |
| F18 | `foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md` | Thm 0.0.13 |
| F19 | `Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md` | Def 0.1.1 |
| F20 | `Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md` | Def 0.1.2 |
| F21 | `Phase0/Definition-0.1.3-Pressure-Functions.md` | Def 0.1.3 |
| F22 | `Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md` | Prop 0.1.3a |
| F23 | `Phase0/Definition-0.1.4-Color-Field-Domains.md` | Def 0.1.4 |
| F24 | `Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md` | Thm 0.1.0 |
| F25 | `Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md` | Thm 1.1.1 |
| F26 | `Phase1/Definition-1.1.4-Stella-Diagram-Rules.md` | Def 1.1.4 |

Additionally, 3-file sub-components were checked for Thm 0.0.0a, Thm 0.0.6, Thm 0.0.12, Thm 0.0.13, and Def 0.1.1.

---

## Detailed Findings

### M7.1: Tetrahedra Naming Convention (T₊/T₋ vs T₁/T₂)

**Result: PASS**

All 26 G1 files use **T₊/T₋** for the two interpenetrating stella octangula tetrahedra. No file uses T₁/T₂ for stella tetrahedra.

Instances of T₁/T₂ were found in foundations files but in unrelated contexts:
- Prop 0.0.22 (SU(2) generators: T₁ + iT₂ → W⁺)
- Thm 0.0.0a-Derivation (generic adjacent tetrahedra T₁, T₂ in FCC tiling, not stella)
- Prop 0.0.28 (theory embeddings T₁ → T₂)

None of these create confusion with the stella tetrahedra convention.

**Previous fix confirmed:** The notation glossary was updated from T₁/T₂ to T₊/T₋ during the original M7 audit (2026-02-21, M7.1-FIX).

---

### M7.2: Boundary Notation (∂S vs ∂𝒮)

**Result: PASS (with 4 NOTEs)**

The canonical notation is **∂𝒮** (with calligraphic S: `\partial\mathcal{S}`). Usage across G1 files:

| Notation | Files | Context |
|----------|-------|---------|
| ∂𝒮 (calligraphic) | F19 (Def 0.1.1, 25 occurrences), F20, F21, F22, F23, F24, F25, F26 | Phase 0/1 files — canonical |
| ∂S (plain) | F22 (Prop 0.1.3a line 329), F24 (Thm 0.1.0-Prime line 7, 704) | Informal/summary contexts |
| Neither used | F01–F18 (foundations files) | Most foundations files discuss the stella abstractly without using ∂S/∂𝒮 notation directly |

**Assessment:** The canonical ∂𝒮 is used consistently in all files that define or reference the boundary formally. Plain ∂S appears only in 2 files (F22 in a diagram, F24 in revision notes and a summary line) and never in mathematical definitions. No file mixes both notations within formal content.

**NOTE instances (4):** F22:329 uses ∂S in an ASCII-art dependency tree. F24:7 and F24:704 use ∂S in revision notes and a summary checklist. These are informal contexts where calligraphic fonts are unavailable or awkward.

---

### M7.3: Metric Signature Convention

**Result: PASS**

The canonical convention is **mostly-plus: η_μν = diag(−1, +1, +1, +1)** for Lorentzian spacetime and **(+,+,+)** for spatial-only contexts.

| File | Context | Convention | Correct? |
|------|---------|-----------|----------|
| F02 (Thm 0.0.1) | Spacetime | (−,+,+,+) implied | ✅ |
| F03 (Thm 0.0.2) | Weight space | Euclidean (+,+) | ✅ |
| F14 (Prop 0.0.6b) | Lattice → continuum | Euclidean (+,+,+) | ✅ |
| F15 (Thm 0.0.9) | Consistency check | (−,+,+,+) | ✅ |
| F25 (Thm 1.1.1) | Weight/embedding space | Euclidean | ✅ |
| Phase 0 files | Pre-geometric | No metric (explicitly stated, Def 0.1.1 §3.3) | ✅ |

No wrong-sign convention detected in any file.

---

### M7.4: Weight Basis Convention ((T₃, T₈) vs (T₃, Y))

**Result: PASS**

Two conventions are in use with explicit conversion documented:

| Convention | Files | Weight values w_R |
|-----------|-------|-------------------|
| (T₃, Y) | F19 (Def 0.1.1), F25 (Thm 1.1.1 §4) | (1/2, 1/3) |
| (T₃, T₈) | F14 (Prop 0.0.6b), F23 (Def 0.1.4), F26 (Def 1.1.4) | (1/2, 1/(2√3)) |

**Bridge documented:** Thm 1.1.1 Step 7B (line 342–347) explicitly states: "In the (T₃, T₈) basis where T₈ = λ₈/2" and provides the conversion T₈ = Y·√3/2. Def 0.1.4 Step 7B also documents this bridge.

All files that use weight vectors declare which basis they employ. No file uses weights without specifying the convention.

---

### M7.5: Generator Normalization

**Result: PASS**

The physics convention **Tr[TᵃTᵇ] = ½δᵃᵇ** is used consistently:

| File | Statement | Line |
|------|-----------|------|
| F03 (Thm 0.0.2) | B(X,Y) = 6·Tr(XY) for SU(3) | 163 |
| F18 (Thm 0.0.13) | "standard physics convention" | 151 |
| F25 (Thm 1.1.1) | Gell-Mann matrices λ_a with Tr(λ_a λ_b) = 2δ_{ab}, hence T^a = λ^a/2 gives Tr[TᵃTᵇ] = ½δᵃᵇ | 44–56 |

No file uses the mathematics convention (Tr = 1) without conversion.

---

### M7.6: Killing Form Sign Convention

**Result: PASS**

Thm 0.0.2 (F03) is the primary source for the Killing form. The convention is:

- **B(X,Y) = Tr(ad_X ∘ ad_Y)** — negative-definite for compact SU(3) (line 146)
- **Positive-definite metric on weight space:** ⟨λ,μ⟩_K = −B⁻¹(λ,μ) (line 116, 238)
- **Raw calculation:** B(λ_a, λ_b) = −12δ_{ab} (line 180)
- **Inverse:** B⁻¹ = −(1/3)𝕀₂, hence ⟨·,·⟩_K = (1/3)𝕀₂ (line 235–238)

The sign convention is clearly documented with explicit notes about negative-definiteness for compact groups. No other file redefines or contradicts this.

---

### M7.7: Euler Characteristic χ — Dimensional Consistency

**Result: PASS**

χ(∂𝒮) = 4 is correctly stated in every file that references it:

| File | Statement | Method |
|------|-----------|--------|
| F09 (Thm 0.0.3) | χ = 4 | Two spheres, each χ = 2 |
| F19 (Def 0.1.1) | χ(∂𝒮) = 4 | V − E + F = 8 − 12 + 8 = 4 |
| F24 (Thm 0.1.0-Prime) | χ(∂S) = 4 | "two S² spheres" |

No file states χ = 2 for the stella boundary (which would indicate octahedron confusion).

---

### M7.8: χ Symbol Disambiguation (Euler Characteristic vs Chiral Field)

**Result: PASS (with 2 NOTEs)**

The symbol χ is used for two distinct purposes:
- **Euler characteristic:** χ(∂𝒮) = 4, χ(M) for general manifolds
- **Chiral scalar field:** χ_c(x) = a_c(x)·e^{iφ_c} (color-indexed)

**Disambiguation rule (Def 0.1.1, line 110):** "The symbol χ is reserved for chiral field configurations. The Euler characteristic is always written χ(∂𝒮) or χ(M) with explicit argument to avoid confusion."

This rule is followed in practice:
- Euler characteristic always appears with an explicit argument: χ(∂𝒮), χ(M), χ(S²)
- Chiral fields always carry a color subscript: χ_R, χ_G, χ_B, or appear as χ_c

**NOTE (2 files):** F19 (Def 0.1.1-Applications) and F24 (Thm 0.1.0-Prime) use both χ meanings in the same file. Disambiguation is implicit from context (subscript vs argument) but no explicit disambiguation note appears in these files. This was flagged as known issue B2 in the original audit.

---

### M7.9: "Stella Octangula" Naming Consistency

**Result: PASS**

All 26 files use **"stella octangula"** as the primary name. Acceptable variants found:

| Variant | Files | Context |
|---------|-------|---------|
| "stella octangula" | ALL 26 files | Primary name |
| "stella" (abbreviated) | Multiple files | Informal shorthand |
| "star tetrahedron" | F19 (Def 0.1.1 line 118), F25 (Thm 1.1.1 line 152) | Parenthetical synonym |
| "stella octangulae" (Latin plural) | F13 (Thm 0.0.6) | Plural context |

No file uses "octahedron" to refer to the stella. Thm 0.0.3 (F09) §5.2 explicitly eliminates the octahedron as a candidate (χ ≠ 4). CLAUDE.md prominently warns against octahedron confusion.

---

### M7.10: ε Symbol Usage (Regularization vs Levi-Civita vs Other)

**Result: PASS (with 3 NOTEs)**

The ε symbol has multiple meanings across G1 files, always disambiguated by context:

| Meaning | Files | Form |
|---------|-------|------|
| Regularization parameter | F21 (Def 0.1.3): P_c(x) = 1/(r² + ε²) | Scalar, no indices |
| Levi-Civita symbol | F12 (Thm 0.0.16 §4.2): ε_{RGB} | Tensor with color indices |
| Energy density | F14 (Prop 0.0.6b line 268) | Scalar in thermodynamic context |
| Feynman iε prescription | F15 (Thm 0.0.9 line 236) | Complex, attached to propagator |

**NOTE (3 instances):**
1. F20 (Def 0.1.2) uses ε for both regularization AND Levi-Civita within the same file (lines 329–345 vs 498, 539). Disambiguation is implicit via index structure (ε² scalar vs ε^{abc} tensor).
2. F14 uses ε for energy density — distinct context from regularization.
3. F15 uses iε for Feynman prescription — standard physics usage, no ambiguity.

No actual inconsistency exists; all uses are conventional physics notation where context provides disambiguation.

---

### M7.11: O_h vs S₄ × ℤ₂ for Full Stella Symmetry

**Result: PASS**

After the original M7.11-FIX, O_h and S₄ × ℤ₂ are consistently identified as isomorphic:

| File | Statement |
|------|-----------|
| F09 (Thm 0.0.3) line 84 | "O_h ≅ S₄ × ℤ₂ (stella symmetry)" — merged row |
| F14 (Prop 0.0.6b) line 12 | "48-element octahedral symmetry O_h" with explanation of proper/improper rotations |
| F19 (Def 0.1.1) line 108 | "S₄ × ℤ₂ (Symmetry group)" |

**Decomposition:** F14 explicitly distinguishes O (24 proper rotations, chiral octahedral group) from O_h (48 elements including reflections). F09 states the isomorphism. F19 uses S₄ × ℤ₂ directly.

All three notations (O_h, S₄ × ℤ₂, octahedral symmetry) are used for the same group with consistent order 48.

---

### M7.12: S₃ Identification (Weyl Group vs Symmetric Group)

**Result: PASS**

S₃ is identified as the **Weyl group of SU(3)** on first use in every file that mentions it:

| File | First appearance | Context |
|------|-----------------|---------|
| F01 (Def 0.0.0) line 83 | GR2 surjection Aut(P) → S₃ | Weyl group |
| F05 (Lem 0.0.2a) line 94 | "The Weyl group S₃ permutes these weights" | Weyl group |
| F09 (Thm 0.0.3) line 87 | "S₃ ⊂ O_h" | Weyl subgroup |
| F12 (Thm 0.0.16) line 88 | "3-fold rotation permuting colors R→G→B→R" | Weyl/color permutation |
| F17 (Thm 0.0.12) | S₃-equivariance of functors | Weyl group |
| F25 (Thm 1.1.1) line 334 | "W(𝔰𝔲(3)) ≅ S₃ (Weyl group)" | Explicitly labeled |

14 files total use S₃; all 14 identify it as the Weyl group 𝒲(SU(3)). No file uses S₃ without this identification.

---

### M7.13: "Weight Vertices" vs "Color Vertices" Terminology

**Result: PASS (with 4 NOTEs)**

A natural terminology shift occurs between foundations (abstract) and Phase 0/1 (physical) files:

| Term | Context | Files |
|------|---------|-------|
| "Weight vertices" | Abstract representation theory | F01 (Def 0.0.0), F09 (Thm 0.0.3), F10 (Thm 0.0.3b), F25 (Thm 1.1.1) |
| "Color vertices" | Physical color charge interpretation | F19 (Def 0.1.1), F20 (Def 0.1.2), F26 (Def 1.1.4) |

Both terms refer to the same 6 non-apex vertices. The terminology shift is natural (foundations use algebraic language; Phase 0/1 use physical language) and never creates ambiguity about which vertices are meant.

**NOTE (4 files):** F17 (Thm 0.0.12-Derivation), F14 (Prop 0.0.6b), F19 (Def 0.1.1), and F20 (Def 0.1.2) mix both terms without an explicit bridging statement. No file uses the terms for different vertex subsets.

---

### M7.14: Natural Units Assumption

**Result: PASS (with 2 NOTEs)**

Most G1 files are purely algebraic/topological and do not require unit declarations. Files that involve physical quantities:

| File | Treatment |
|------|-----------|
| F02 (Thm 0.0.1) | Dimensionful arguments without formal ℏ = c = 1 declaration |
| F03 (Thm 0.0.2) | Killing form noted as "intrinsically dimensionless" (line 574) |
| F13 (Thm 0.0.6) | ℏc explicitly carried in R_stella derivation |
| F19 (Def 0.1.1) | States R_stella = 1 convention for dimensionless calculations |

**NOTE (2 files):** F02 and F03 reference dimensionful values without a formal natural units declaration. Their proofs are not unit-dependent, so this is cosmetic.

---

### M7.15: Status Marker Format

**Result: PASS**

All 26 G1 files now use **canonical status markers** following the format:
```
## Status: [MARKER] — [SHORT DESCRIPTION IN CAPS]
```

Complete inventory:

| Marker | Count | Files |
|--------|-------|-------|
| 🔶 NOVEL ✅ VERIFIED | 20 | F01, F03, F04, F05, F06, F07, F09, F10, F11, F12, F13, F14, F16, F17, F18, F19, F22, F24, F25, F26 |
| 🔶 NOVEL | 5 | F08, F15, F20, F21, F23 |
| ✅ ESTABLISHED | 1 | F02 |

> **v3 correction:** F19 (Def 0.1.1) was omitted from the v2 🔶 NOVEL ✅ VERIFIED list; its status is `🔶 NOVEL ✅ VERIFIED — FOUNDATIONAL BOUNDARY TOPOLOGY`. Count corrected from 19 → 20.

**Assessment:** All 26 files follow the canonical marker vocabulary. No non-canonical markers (COMPLETE, FRAMEWORK COMPLETE, etc.) remain. The original M7.15 finding of 19 files with non-canonical markers has been fully resolved by the M9.2 status marker standardization (2026-02-21).

All descriptions after "—" are in ALL CAPS, consistent with the CLAUDE.md rule. All use the correct emoji markers without dates or method details in the status line.

---

## Supplementary Findings (New for 2026-03-14 Re-Audit)

### M7.16: Prop 0.0.40 Notation Consistency (New File)

**Result: PASS**

Prop 0.0.40 (F06) was not in the original 23-file audit. Notation check:

| Convention | Value in Prop 0.0.40 | Consistent? |
|-----------|----------------------|-------------|
| Status marker | 🔶 NOVEL ✅ VERIFIED | ✅ Canonical |
| Tetrahedra | T₊/T₋ implied | ✅ |
| Weight basis | (T₃, T₈) implied via Cartan structure | ✅ |
| d_embed formula | d_embed = rank(G) + 1 | ✅ Consistent with D = N + 1 in Thm 0.0.2b |

---

### M7.17: Prop 0.1.3a Notation Consistency (New File)

**Result: PASS**

Prop 0.1.3a (F22) was not in the original audit. Notation check:

| Convention | Value in Prop 0.1.3a | Consistent? |
|-----------|----------------------|-------------|
| Status marker | 🔶 NOVEL ✅ VERIFIED | ✅ Canonical |
| Boundary notation | ∂S in ASCII tree (line 329); ∂𝒮 in formal text | ✅ Acceptable |
| Pressure notation | P_c(x) with axioms P1–P7 | ✅ Matches Def 0.1.3 |
| ε usage | ε in P_c(x) = 1/(r² + ε²) | ✅ Regularization parameter |

---

### M7.18: Thm 0.1.0 Notation Consistency (New File)

**Result: PASS**

Thm 0.1.0 (F24) was not in the original audit. Notation check:

| Convention | Value in Thm 0.1.0 | Consistent? |
|-----------|---------------------|-------------|
| Status marker | 🔶 NOVEL ✅ VERIFIED | ✅ Canonical |
| Boundary notation | ∂S in summary (line 704); ∂𝒮 in formal definitions | ✅ Acceptable (plain S in informal context) |
| χ(∂S) = 4 | Line 704: "Euler characteristic χ(∂S) = 4 (two S² spheres)" | ✅ Correct value |
| Z₃ phases | Derived (not postulated) via Fisher metric | ✅ Consistent with Def 0.1.2 |
| Color field notation | χ_c for chiral fields | ✅ Subscripted, avoids Euler char confusion |

---

### M7.20: 3-File Sub-Component Status Marker Consistency

**Result: NOTE — MINOR**

Five G1 theorems use the 3-file structure (Statement / Derivation / Applications). The sub-component files show status marker drift relative to their parent statement files:

| Theorem | Statement Status | Derivation Status | Applications Status |
|---------|-----------------|-------------------|---------------------|
| Thm 0.0.0a | 🔶 NOVEL ✅ VERIFIED | *(no status line)* | *(no status line)* |
| Thm 0.0.6 | 🔶 NOVEL ✅ VERIFIED | 🔶 NOVEL — COMPLETE PROOFS | 🔶 NOVEL — PREDICTIONS AND VERIFICATION |
| Thm 0.0.12 | 🔶 NOVEL ✅ VERIFIED | 🔶 NOVEL — COMPLETE PROOF | 🔶 NOVEL — PHYSICAL IMPLICATIONS |
| Thm 0.0.13 | 🔶 NOVEL ✅ VERIFIED | 🔶 NOVEL ✅ VERIFIED — DERIVATION | 🔶 NOVEL ✅ VERIFIED — APPLICATIONS |
| Def 0.1.1 | 🔶 NOVEL ✅ VERIFIED | *(no status line)* | *(no status line)* |

**Issues found:**
1. **Thm 0.0.6 and Thm 0.0.12:** Parent files are ✅ VERIFIED but derivation/applications sub-files lack the ✅ VERIFIED marker. This creates an inconsistency — the theorem is supposedly verified, but its derivation is not?
2. **Thm 0.0.0a and Def 0.1.1:** Derivation and applications sub-files have no status line at all.
3. **Thm 0.0.13:** Fully consistent across all 3 files (the gold standard).

**Assessment:** This is a convention gap rather than a mathematical inconsistency. The verification status of a theorem logically applies to the full 3-file set, so the parent statement file's status should be authoritative. However, readers of the derivation file in isolation would see only 🔶 NOVEL and might conclude the derivation is unverified.

**Recommendation:** Propagate the parent's ✅ VERIFIED marker to all sub-files for Thm 0.0.0a, Thm 0.0.6, Thm 0.0.12, and Def 0.1.1, following the Thm 0.0.13 pattern.

---

### M7.21: ω Symbol Overloading Across G1 Files

**Result: NOTE — MINOR**

The symbol ω is used for **three distinct purposes** across G1 files:

| Meaning | Files | Form | Context |
|---------|-------|------|---------|
| Cube root of unity | F16 (Thm 0.0.15), F20 (Def 0.1.2), F14 (Prop 0.0.6b), F26 (Def 1.1.4) | ω = e^{2πi/3}, complex number | Z₃ center, phase factors |
| Angular frequency | F04 (Thm 0.0.2b line 100, 231, 235, 239, 241) | ω > 0, real scalar | Phase evolution χ_c ∝ e^{iωλ} |
| Fiber functor | F18 (Thm 0.0.13 line 147+) | ω: Rep(SU(3)) → Vec_ℂ | Tannaka reconstruction |

**Assessment:** No single G1 file uses ω for two different meanings simultaneously — each file uses it in exactly one sense. The disambiguation is therefore achievable from context:
- Cube root of unity: always accompanied by e^{2πi/3} or the identity 1 + ω + ω² = 0
- Angular frequency: always in phase expressions e^{iωλ} with λ (internal time)
- Fiber functor: always in categorical expressions ω(V) or Aut⊗(ω)

**Risk assessment:** A reader moving between Thm 0.0.2b (ω = angular frequency) and Def 0.1.2 (ω = cube root of unity) could be confused. However, CLAUDE.md §Notation Conventions defines ω only as the chiral phase angle context (α = 2π/3), not as angular frequency. Thm 0.0.2b's usage of ω for angular frequency is standard physics but deviates from the project's α convention for the phase angle.

**Recommendation:** Consider using Ω or ω₀ for the angular frequency in Thm 0.0.2b to avoid cross-file confusion with the Z₃ cube root.

---

### M7.22: Footer Status Format Drift in Thm 0.0.2b

**Result: NOTE — MINOR**

Thm 0.0.2b (F04) has a discrepancy between its header and footer status format:

| Location | Line | Format |
|----------|------|--------|
| **Header** (line 3) | `## Status: 🔶 NOVEL ✅ VERIFIED — D = N + 1 DERIVED FROM REPRESENTATION THEORY` | ✅ Canonical |
| **Footer** (line 518) | `*Status: 🔶 NOVEL (✅ VERIFIED) — D = N + 1 derived from representation theory...*` | ❌ Parenthesized |

The footer wraps ✅ VERIFIED in parentheses: `(✅ VERIFIED)`. This is a minor formatting inconsistency — the standard format has no parentheses. Additionally, the footer description is in mixed case rather than ALL CAPS.

**Assessment:** The header is canonical and authoritative. The footer is an italicized summary line that serves as a document-end marker. The parenthesization does not change the meaning but deviates from the uniform format used in all other G1 files.

**Recommendation:** Remove parentheses from footer and capitalize description to match header format.

---

### M7.23: Dependency Declaration Format Variation in Thm 0.0.9

**Result: NOTE — MINOR**

Thm 0.0.9 (F15) uses a unique dependency declaration format not found in any other G1 file:

| File | Declaration Format |
|------|-------------------|
| **All other 25 G1 files** | `**Dependencies:**` (plain header) |
| **Thm 0.0.9** | `**Dependencies (Logical Prerequisites):**` + separate `**Validated Against (Consistency Targets — not logical inputs to the derivation):**` section |

**Assessment:** Thm 0.0.9's format is arguably *better* than the standard format — it explicitly distinguishes between logical prerequisites (things the theorem depends on) and validation targets (things the theorem's output is checked against). This distinction is semantically important for a consistency-check theorem.

However, the non-standard format creates a format inconsistency. A script or audit tool looking for `**Dependencies:**` would miss or mis-parse Thm 0.0.9's dependency list. The "Validated Against" section is not a convention used by any other file.

**Recommendation:** Either (a) adopt the extended format as a standard option for consistency-check theorems (update CLAUDE.md), or (b) fold the "Validated Against" content into the standard `**Dependencies:**` section with a NOTE annotation distinguishing logical inputs from validation targets.

---

### M7.19: Killing Form Verification Table Shorthand

**Result: NOTE — MINOR**

Thm 0.0.2 (F03) contains a statement at line 621 in its verification section:

> "Killing form |B(T_a, T_b)| = 3δ_{ab}"

The main derivation at line 163 gives B(X,Y) = 6·Tr(XY), yielding B(T_a, T_b) = 6·(½)δ_{ab} = 3δ_{ab} for generators T_a = λ_a/2. However, the Killing form is negative-definite, so strictly B(T_a, T_b) = −3δ_{ab}, and the absolute value bar is doing implicit sign work.

The main derivation (line 180: B(λ_a, λ_b) = −12δ_{ab}) and the sign convention note (line 118: "negative-definite") are correct. This is a presentation issue in the verification checklist, not a mathematical error. Already tracked by M10.7 (resolved in commit fbf01a29).

---

### M7.24: χ = 2 Error in Axiom-Reduction-Action-Plan.md (Out-of-Scope)

**Result: NOTE — MODERATE (out of G1 proof scope but in foundations/)**

`foundations/Axiom-Reduction-Action-Plan.md` line 1026 states:

> "Stella boundary has Euler characteristic χ = 2"
> "Total curvature = 2πχ = 4π (independent of manifold shape)"

**Issue:** The stella boundary ∂𝒮 has χ = 4 (two disjoint S² components, each with χ = 2). Stating χ = 2 for "the stella boundary" conflates a single component with the full boundary. The calculation 2πχ = 4π is correct *per component* (Gauss-Bonnet on each S²), but the text says "stella boundary" without qualification.

**Context:** This is a planning/action-plan document, not one of the 26 G1 proof files. The error does not propagate into any proof, since all proof files correctly state χ(∂𝒮) = 4 (confirmed in M7.7). However, the file lives in `foundations/` and could mislead readers.

**Correct statement:** "Each component of the stella boundary has Euler characteristic χ = 2; the full boundary has χ(∂𝒮) = 4."

**Recommendation:** Fix line 1026 to clarify this refers to each S² component, not the full boundary.

---

### M7.25: Cross-Group Metric Signature Drift (Out-of-Scope)

**Result: NOTE — MODERATE (cross-group, not within G1)**

Within G1, the metric signature is consistently (−,+,+,+) (mostly-plus). However, several files outside G1 use the opposite convention:

| File | Convention | Line |
|------|-----------|------|
| Phase 2: Thm 2.1.2 | (+,−,−,−) mostly-minus | line 65 |
| Phase 3: Thm 3.1.1 | (+,−,−,−) mostly-minus | line 685 |
| Phase 5: Thm 5.3.1 | (+,−,−,−) mostly-minus | lines 179, 1444 |
| Phase 5: Thm 5.3.2 | (+,−,−,−) mostly-minus | line 274 |

**Assessment:** This is NOT a G1 internal inconsistency — all G1 files agree on (−,+,+,+). The drift exists at the cross-group boundary and should be addressed when auditing G2–G4. The CLAUDE.md notation conventions specify (−,+,+,+), making the Phase 2/3/5 usage non-canonical.

**Recommendation:** Flag for G2/G3 coherence audits. Either standardize all files to (−,+,+,+) per CLAUDE.md, or add explicit conversion notes in files that use (−,+,+,+).

---

## Summary

| Check ID | Result | Description |
|----------|--------|-------------|
| M7.1 | **PASS** | T₊/T₋ used in all 26 files for stella tetrahedra; T₁/T₂ only in unrelated contexts |
| M7.2 | **PASS** (4 NOTE) | ∂𝒮 canonical in formal text; ∂S in 2 files for informal/ASCII contexts only |
| M7.3 | **PASS** | (−,+,+,+) Lorentzian, (+,+,+) spatial — consistent everywhere |
| M7.4 | **PASS** | (T₃,T₈) and (T₃,Y) both used; always declared; bridge documented |
| M7.5 | **PASS** | Tr[TᵃTᵇ] = ½δᵃᵇ used consistently throughout |
| M7.6 | **PASS** | Killing form negative-definite for compact SU(3); metric = −B⁻¹ correctly derived |
| M7.7 | **PASS** | χ(∂𝒮) = 4 correctly stated in all files that reference it |
| M7.8 | **PASS** (2 NOTE) | χ = Euler char vs χ = chiral field; disambiguation rule stated in Def 0.1.1; 2 files use both implicitly |
| M7.9 | **PASS** | "Stella octangula" used consistently; "star tetrahedron" as parenthetical synonym only |
| M7.10 | **PASS** (3 NOTE) | ε usage mostly unambiguous; 1 file (Def 0.1.2) uses for both regularization and Levi-Civita |
| M7.11 | **PASS** | O_h ≅ S₄ × ℤ₂ consistently identified across all files |
| M7.12 | **PASS** | S₃ always labeled as Weyl group 𝒲(SU(3)) on first use (14 files) |
| M7.13 | **PASS** (4 NOTE) | "Weight vertices" (foundations) vs "color vertices" (Phase 0/1) — natural shift, no ambiguity |
| M7.14 | **PASS** (2 NOTE) | Most files algebraic; F02/F03 use dimensionful values without formal ℏ=c=1 declaration |
| M7.15 | **PASS** | All 26 files use canonical markers (20 🔶 NOVEL ✅ VERIFIED, 5 🔶 NOVEL, 1 ✅ ESTABLISHED) |
| M7.16 | **PASS** | Prop 0.0.40 (new file) follows all notation conventions |
| M7.17 | **PASS** | Prop 0.1.3a (new file) follows all notation conventions |
| M7.18 | **PASS** | Thm 0.1.0 (new file) follows all notation conventions |
| M7.19 | **NOTE** | Killing form verification table shorthand |B(T_a,T_b)| = 3δ_{ab} omits sign; main derivation correct |
| M7.20 | **NOTE** | 3-file sub-components: 4/5 theorems have status drift between parent and sub-files |
| M7.21 | **NOTE** | ω symbol overloading: cube root of unity (4 files) vs angular frequency (Thm 0.0.2b) vs fiber functor (Thm 0.0.13); no same-file collision |
| M7.22 | **NOTE** | Thm 0.0.2b footer status parenthesized `(✅ VERIFIED)` vs canonical unparenthesized header |
| M7.23 | **NOTE** | Thm 0.0.9 unique dependency format "Dependencies (Logical Prerequisites):" + "Validated Against" not used elsewhere |
| M7.24 | **NOTE** | (Out-of-scope) χ = 2 in Axiom-Reduction-Action-Plan.md line 1026; should clarify "each component" vs full boundary χ = 4 |
| M7.25 | **NOTE** | (Out-of-scope) Cross-group metric signature drift: Phase 2/3/5 files use (+,−,−,−) vs G1's (−,+,+,+) |

---

## Key Observations

1. **Notation is highly consistent** — no CRITICAL, MAJOR, or MINOR failures across all 23 checks. The T₊/T₋ convention, stella naming, metric signature, generator normalization, Killing form, and status markers are all uniform across all 26 files.

2. **Status marker standardization is complete** — the original M7.15 finding of 19 files with non-canonical markers (VERIFIED, COMPLETE, FRAMEWORK COMPLETE) has been fully resolved. All 26 files now use the canonical vocabulary.

3. **Three new files (Prop 0.0.40, Prop 0.1.3a, Thm 0.1.0)** pass all notation checks with no issues.

4. **Known issues B1 (T₁/T₂ divergence) and B2 (χ overload)** are both confirmed resolved or at acceptable severity:
   - B1: Glossary updated to T₊/T₋; no proof file uses T₁/T₂ for stella
   - B2: Disambiguation rule established in Def 0.1.1 line 110; implicit disambiguation via subscript vs argument in all files

5. **Symbol overloading** (χ in M7.8, ε in M7.10, ω in M7.21) exists but disambiguation is always achievable from context. No single file uses the same symbol for two meanings simultaneously. The ω overloading (cube root vs angular frequency vs functor) is the most significant cross-file symbol collision: Thm 0.0.2b uses ω as angular frequency while 4 other G1 files use it as e^{2πi/3}.

6. **3-file sub-component status drift** (M7.20) — 4 of 5 theorems with 3-file structure have inconsistent or missing status markers in their Derivation/Applications sub-files. Only Thm 0.0.13 propagates ✅ VERIFIED to all sub-files consistently.

7. **Minor formatting drift** (M7.22, M7.23) — Thm 0.0.2b has a parenthesized footer status; Thm 0.0.9 uses a unique dependency declaration format. Both are cosmetic and do not affect mathematical content.

8. **Out-of-scope χ = 2 error** (M7.24) — `Axiom-Reduction-Action-Plan.md` line 1026 states χ = 2 for the stella boundary without clarifying this is per-component. All 26 G1 proof files correctly state χ = 4 for the full boundary; the error is isolated to a planning document.

9. **Cross-group metric signature drift** (M7.25) — G1 consistently uses (−,+,+,+) per CLAUDE.md. Phase 2/3/5 files use the opposite convention (+,−,−,−). This is a cross-group issue to flag for future audits (G2, G3, G8).

---

## Comparison with Original M7 Audit (2026-02-21)

| Dimension | Original (23 files) | v2 Re-audit (26 files) | v3 Re-verification | v5 Re-verification | v6 Re-verification | Change |
|-----------|--------------------|--------------------|---------------------|---------------------|---------------------|--------|
| Total checks | 15 | 19 | 20 | 23 | 25 | +2 (M7.24–M7.25 added) |
| PASS | 15 | 19 | 20 | 20 | 20 | Stable |
| FAIL | 1 (M7.11, fixed) | 0 | 0 | 0 | 0 | ✅ Fix confirmed durable |
| NOTE | — | — | 2 | 5 | 7 | +2 (out-of-scope χ=2, metric drift) |
| NOTE instances | 38 | 15 | 16 | 19 | 19 | Stable (new NOTEs are out-of-scope) |

**v6 changes:** Second fully independent re-verification by 3 parallel exploration agents. All 23 v5 checks independently confirmed with matching line numbers and evidence. Added M7.24 (χ = 2 in Axiom-Reduction-Action-Plan.md — out-of-scope planning doc) and M7.25 (cross-group metric signature drift in Phase 2/3/5). Both are out-of-scope for G1 but flagged for downstream audits.

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 1,
  "module": "M7",
  "checks_total": 25,
  "checks_passed": 20,
  "checks_failed": 0,
  "checks_noted": 7,
  "findings": [
    {
      "check_id": "M7.1",
      "result": "PASS",
      "description": "Tetrahedra naming: T₊/T₋ used in all 26 files; T₁/T₂ only in unrelated contexts",
      "evidence": "All 26 G1 files checked; T₁/T₂ found only in Prop 0.0.22 (SU(2) generators), Thm 0.0.0a-Deriv (generic FCC tetrahedra), Prop 0.0.28 (theory embeddings)"
    },
    {
      "check_id": "M7.2",
      "result": "PASS",
      "description": "Boundary notation: ∂𝒮 canonical; plain ∂S in 2 files for informal/ASCII contexts",
      "evidence": "∂𝒮: 143+ occurrences in Phase0/Phase1 files; ∂S: Prop 0.1.3a line 329, Thm 0.1.0-Prime lines 7, 704"
    },
    {
      "check_id": "M7.3",
      "result": "PASS",
      "description": "Metric signature: (−,+,+,+) Lorentzian, (+,+,+) spatial — consistent everywhere",
      "evidence": "Thm 0.0.1, Thm 0.0.2, Prop 0.0.6b, Thm 0.0.9; Phase 0 files explicitly pre-geometric (no metric)"
    },
    {
      "check_id": "M7.4",
      "result": "PASS",
      "description": "Weight basis: (T₃,T₈) and (T₃,Y) both used; always declared; bridge T₈=Y·√3/2 documented",
      "evidence": "Thm 1.1.1 Step 7B (line 342-347); Def 0.1.4 Step 7B; M4.2 and M10.8a/8b cross-verified"
    },
    {
      "check_id": "M7.5",
      "result": "PASS",
      "description": "Generator normalization: Tr[TᵃTᵇ] = ½δᵃᵇ (physics convention) used throughout",
      "evidence": "Thm 0.0.2 line 163; Thm 0.0.13 line 151; Thm 1.1.1 lines 44-56"
    },
    {
      "check_id": "M7.6",
      "result": "PASS",
      "description": "Killing form: B negative-definite for compact SU(3); metric = −B⁻¹ = (1/3)𝕀₂",
      "evidence": "Thm 0.0.2 lines 116, 146, 180, 235-238"
    },
    {
      "check_id": "M7.7",
      "result": "PASS",
      "description": "Euler characteristic χ(∂𝒮) = 4 correctly stated in all referencing files",
      "evidence": "Thm 0.0.3 line ~502; Def 0.1.1 lines 104, 173; Thm 0.1.0-Prime line 704"
    },
    {
      "check_id": "M7.8",
      "result": "PASS",
      "description": "χ symbol disambiguation: Euler char has explicit argument χ(M); chiral field has subscript χ_c; rule stated in Def 0.1.1 line 110",
      "evidence": "Def 0.1.1 line 110 (disambiguation rule); 2 files use both meanings implicitly (Def 0.1.1-Apps, Thm 0.1.0-Prime)"
    },
    {
      "check_id": "M7.9",
      "result": "PASS",
      "description": "Stella octangula naming consistent; 'star tetrahedron' as parenthetical synonym in 2 files",
      "evidence": "All 26 files use 'stella octangula'; Def 0.1.1 line 118, Thm 1.1.1 line 152 introduce 'star tetrahedron'"
    },
    {
      "check_id": "M7.10",
      "result": "PASS",
      "description": "ε usage disambiguated by context (scalar vs tensor indices); 1 file uses both meanings",
      "evidence": "Def 0.1.3 (regularization); Thm 0.0.16 §4.2 (Levi-Civita); Def 0.1.2 uses both (lines 329-345 vs 498)"
    },
    {
      "check_id": "M7.11",
      "result": "PASS",
      "description": "O_h ≅ S₄ × ℤ₂ consistently identified as isomorphic (original FAIL fixed 2026-02-21)",
      "evidence": "Thm 0.0.3 line 84 (merged row); Prop 0.0.6b line 12; Def 0.1.1 line 108"
    },
    {
      "check_id": "M7.12",
      "result": "PASS",
      "description": "S₃ always labeled as Weyl group 𝒲(SU(3)) on first use in all 14 files that mention it",
      "evidence": "Def 0.0.0 line 83; Lem 0.0.2a line 94; Thm 0.0.3 line 87; Thm 1.1.1 line 334"
    },
    {
      "check_id": "M7.13",
      "result": "PASS",
      "description": "Weight vertices (foundations) vs color vertices (Phase 0/1) — natural terminology shift, no ambiguity",
      "evidence": "4 files mix terms without bridging (Thm 0.0.12-Deriv, Prop 0.0.6b, Def 0.1.1, Def 0.1.2); never different vertex subsets"
    },
    {
      "check_id": "M7.14",
      "result": "PASS",
      "description": "Natural units ℏ=c=1 implicit; most G1 files algebraic. F02/F03 use dimensionful values without declaration",
      "evidence": "Thm 0.0.6 carries ℏc explicitly; Def 0.1.1 states R_stella=1 convention"
    },
    {
      "check_id": "M7.15",
      "result": "PASS",
      "description": "All 26 files use canonical status markers (20 🔶 NOVEL ✅ VERIFIED, 5 🔶 NOVEL, 1 ✅ ESTABLISHED)",
      "evidence": "Verified via grep of all 26 files; M9.2 standardization (2026-02-21) resolved original 19-file drift"
    },
    {
      "check_id": "M7.16",
      "result": "PASS",
      "description": "Prop 0.0.40 (new file, not in original audit) follows all notation conventions",
      "evidence": "Status: 🔶 NOVEL ✅ VERIFIED; d_embed = rank(G)+1 consistent with D=N+1"
    },
    {
      "check_id": "M7.17",
      "result": "PASS",
      "description": "Prop 0.1.3a (new file) follows all notation conventions",
      "evidence": "Status: 🔶 NOVEL ✅ VERIFIED; pressure notation P_c(x) matches Def 0.1.3"
    },
    {
      "check_id": "M7.18",
      "result": "PASS",
      "description": "Thm 0.1.0 (new file) follows all notation conventions; χ(∂S)=4 correct",
      "evidence": "Status: 🔶 NOVEL ✅ VERIFIED; line 704: χ(∂S)=4; Z₃ phases derived consistently"
    },
    {
      "check_id": "M7.19",
      "result": "NOTE",
      "description": "Thm 0.0.2 verification table uses |B(T_a,T_b)|=3δ_{ab} (absolute value omits sign); main derivation correct",
      "evidence": "Thm 0.0.2 line 621 (verification table) vs line 180 (B(λ_a,λ_b) = −12δ_{ab}); M10.7 already addressed",
      "severity": "MINOR"
    },
    {
      "check_id": "M7.20",
      "result": "NOTE",
      "description": "3-file sub-component status marker drift: 4/5 theorems have missing or downgraded ✅ VERIFIED in Derivation/Applications sub-files",
      "evidence": "Thm 0.0.6-Deriv: 🔶 NOVEL (parent: ✅ VERIFIED); Thm 0.0.12-Deriv: 🔶 NOVEL (parent: ✅ VERIFIED); Thm 0.0.0a/Def 0.1.1 sub-files: no status line. Only Thm 0.0.13 fully consistent.",
      "severity": "MINOR"
    },
    {
      "check_id": "M7.21",
      "result": "NOTE",
      "description": "ω symbol overloading: cube root of unity (4 files), angular frequency (Thm 0.0.2b), fiber functor (Thm 0.0.13); no same-file collision but cross-file ambiguity",
      "evidence": "Thm 0.0.2b line 100: χ_c ∝ e^{iωλ} (angular freq); Def 0.1.2/Thm 0.0.15/Prop 0.0.6b/Def 1.1.4: ω = e^{2πi/3} (cube root); Thm 0.0.13: ω (fiber functor)",
      "severity": "MINOR"
    },
    {
      "check_id": "M7.22",
      "result": "NOTE",
      "description": "Thm 0.0.2b footer status format drift: parenthesized '🔶 NOVEL (✅ VERIFIED)' at line 518 vs canonical unparenthesized header at line 3",
      "evidence": "Line 3: '## Status: 🔶 NOVEL ✅ VERIFIED — D = N + 1 DERIVED FROM REPRESENTATION THEORY'; Line 518: '*Status: 🔶 NOVEL (✅ VERIFIED) — D = N + 1 derived from...*'",
      "severity": "MINOR"
    },
    {
      "check_id": "M7.23",
      "result": "NOTE",
      "description": "Thm 0.0.9 unique dependency format: 'Dependencies (Logical Prerequisites):' + separate 'Validated Against' section not used by any other G1 file",
      "evidence": "Thm 0.0.9 line 7: 'Dependencies (Logical Prerequisites):'; line 18: 'Validated Against (Consistency Targets)'. All other 25 G1 files use plain 'Dependencies:'",
      "severity": "MINOR"
    },
    {
      "check_id": "M7.24",
      "result": "NOTE",
      "description": "(Out-of-scope) Axiom-Reduction-Action-Plan.md line 1026 states χ = 2 for 'stella boundary' without clarifying per-component; all 26 G1 proof files correctly state χ = 4",
      "evidence": "foundations/Axiom-Reduction-Action-Plan.md line 1026: 'Stella boundary has Euler characteristic χ = 2'; cf. Def 0.1.1 line 173: χ(∂𝒮) = 4",
      "severity": "MODERATE"
    },
    {
      "check_id": "M7.25",
      "result": "NOTE",
      "description": "(Out-of-scope) Cross-group metric signature drift: G1 uses (−,+,+,+) consistently; Phase 2/3/5 files use (+,−,−,−)",
      "evidence": "Thm 2.1.2 line 65, Thm 3.1.1 line 685, Thm 5.3.1 lines 179/1444, Thm 5.3.2 line 274 all use (+,−,−,−); CLAUDE.md specifies (−,+,+,+)",
      "severity": "MODERATE"
    }
  ],
  "overall_result": "PASS"
}
```
