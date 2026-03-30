# G1 Geometric Foundation — Coherence Audit: Module M1 Findings

> **Module:** M1 — Geometric/Structural Identity — Core objects have consistent properties across all files
> **Group:** G1 — Geometric Foundation
> **Layer:** 1 (Coherence)
> **Posture:** DEFENSIVE — verify internal consistency
> **Auditor:** Claude Opus 4.6 (autonomous audit agent)
> **Date:** 2026-03-14
> **Template:** [G1-Geometric-Foundation-Coherence-Audit.md](G1-Geometric-Foundation-Coherence-Audit.md) § Module 1

---

## Scope

Module M1 verifies that the **stella octangula's combinatorial invariants** — vertex count, edge count, face count, Euler characteristic, connected components, and surface area — are stated **identically** across all 26 proof files in thematic group G1. It also checks that ∂S is never confused with a regular octahedron and that the octahedron is explicitly eliminated as a candidate.

The critical risks are:
1. A file stating vertex/edge/face counts that correspond to a single polyhedron (octahedron, cube) rather than the compound of two tetrahedra
2. The Euler characteristic written as χ = 2 (octahedron) instead of χ = 4 (two S²)
3. The 4+4 decomposition (T₊ ⊔ T₋) being omitted, leaving the structure ambiguous
4. The geometric intersection surface (central octahedron, V=6, χ=2) being conflated with ∂S

---

## Files Examined

All 26 G1 proof files were read in full. The files most relevant to M1 are:

| # | File | Abbreviation | Role in M1 |
|---|------|--------------|------------|
| F01 | `foundations/Definition-0.0.0-Minimal-Geometric-Realization.md` | Def 0.0.0 | Defines GR1–GR3, Lemma 0.0.0g (component structure) |
| F08 | `foundations/Theorem-0.0.3-Stella-Uniqueness.md` | Thm 0.0.3 | Proves stella is unique; eliminates octahedron |
| F09 | `foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md` | Thm 0.0.3b | Extends uniqueness to all topological spaces |
| F18 | `Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md` | Def 0.1.1 | **Canonical reference** for ∂S geometry |
| F23 | `Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md` | Thm 1.1.1 | SU(3) ↔ stella isomorphism |
| F26 | `Phase1/Definition-1.1.4-Stella-Diagram-Rules.md` | Def 1.1.4 | Diagram rules; distinguishes diagram from geometric edges |

Additionally checked (no M1-relevant issues found):

| Files | Result |
|-------|--------|
| F02 (Thm 0.0.1), F03 (Thm 0.0.2), F04 (Thm 0.0.2b) | D=4 and SU(3) derivations; no stella combinatorics stated |
| F05 (Lem 0.0.2a), F06 (Prop 0.0.40) | Dimension bounds; no stella combinatorics stated |
| F07 (Prop 0.0.XX) | SU(3) from distinguishability; references 8 vertices correctly |
| F10 (Thm 0.0.15) | Topological determination; references two components correctly |
| F11 (Thm 0.0.12), F12 (Thm 0.0.13) | Category/Tannaka reconstruction; minimal stella references |
| F13 (Prop 0.0.16a), F14 (Thm 0.0.16) | A₃ lattice; references stella vertex structure correctly |
| F15 (Thm 0.0.6) | FCC lattice; references 8 vertices correctly |
| F16 (Prop 0.0.6b) | Continuum limit; references Z₃ structure |
| F17 (Thm 0.0.9) | Framework-internal D=4; references stella combinatorics correctly |
| F19 (Def 0.1.2) | Color fields; references 3 colors on ∂S |
| F20 (Def 0.1.3) | Pressure functions; lists 8 vertex positions correctly |
| F21 (Prop 0.1.3a) | Form-independence; references ∂S topology |
| F22 (Def 0.1.4) | Color domains; references two tetrahedra correctly |
| F24 (Thm 0.1.0) | Field existence; references ∂S as domain |

---

## Detailed Findings

### M1.1: Vertex Count = 8 (4+4)

**Result: PASS**

Every file that states a vertex count agrees: the stella octangula has **8 vertices = 4 (T₊) + 4 (T₋)**, decomposed as 6 weight vertices + 2 apex vertices.

| File | Statement | 4+4 explicit? |
|------|-----------|--------------|
| Def 0.0.0 (F01) | "minimal vertex count is 8 (6 primary + 2 apex)" (§2.2) | ✅ Yes — Lemma 0.0.0a |
| Thm 0.0.3 (F08) | "8 vertices... 6 primary + 2 apex" (§1(a), §2.2) | ✅ Yes |
| Thm 0.0.3b (F09) | "at most 8 vertices" (vertex bound) | ✅ Yes — references 3+3̄+2 |
| Def 0.1.1 (F18) | "8 vertices: 4 from T₊ (colors R,G,B,W) and 4 from T₋" (§2.3) | ✅ Yes |
| Thm 1.1.1 (F23) | T₊ has 4 vertices, T₋ has 4 vertices | ✅ Yes |
| Def 1.1.4 (F26) | 6 color vertices + 2 not in diagram | ✅ Yes |

No file states V=6 (octahedron) or any other incorrect count.

---

### M1.2: Edge Count = 12 (6+6)

**Result: PASS**

All files that state an edge count agree: **12 edges = 6 (T₊) + 6 (T₋)** with no shared edges between the two tetrahedra.

| File | Statement | 6+6 explicit? |
|------|-----------|--------------|
| Def 0.0.0 (F01) | 12 edges from Lemma 0.0.0g edge structure (§4.6) | ✅ Yes — "T+: 6 edges, T-: 6 edges" |
| Thm 0.0.3 (F08) | References 12 edges in uniqueness proof | ✅ Yes |
| Def 0.1.1 (F18) | "12 edges: 6 from T₊ and 6 from T₋ (no shared edges)" (§2.3) | ✅ Yes |
| Def 1.1.4 (F26) | Distinguishes "9 diagram edges" from "12 geometric edges" (line 76) | ✅ Yes |

**Note on Def 1.1.4:** This file correctly distinguishes between the 9 edges used in the stella diagram (edges between color vertices only, excluding apex connections) and the 12 geometric edges. This distinction is well-documented and not a source of confusion.

---

### M1.3: Face Count = 8 (4+4)

**Result: PASS**

All files agree: **8 triangular faces = 4 (T₊) + 4 (T₋)**.

| File | Statement | 4+4 explicit? |
|------|-----------|--------------|
| Def 0.0.0 (F01) | 8 faces in polyhedral structure | ✅ Yes |
| Thm 0.0.3 (F08) | 8 faces in V−E+F computation | ✅ Yes |
| Def 0.1.1 (F18) | "8 triangular faces: 4 from ∂T₊ and 4 from ∂T₋" (§2.3) | ✅ Yes |

No file claims 8 faces on a single polyhedron without the 4+4 decomposition.

---

### M1.4: Connected Components = 2

**Result: PASS**

All files that discuss connectivity state that ∂S consists of **2 connected components**: ∂T₊ and ∂T₋, forming a disjoint union.

| File | Statement |
|------|-----------|
| Def 0.0.0 (F01) | Lemma 0.0.0g (§4.6): "The stella octangula has 2 geometric components" with careful distinction between geometric and symmetry-extended connectivity |
| Thm 0.0.3 (F08) | "two tetrahedra ... interpenetrate geometrically while remaining topologically distinct" |
| Thm 0.0.15 (F10) | References "two connected components" |
| Def 0.1.1 (F18) | "2 connected components: ∂T₊ and ∂T₋" (§2.3); "tetrahedra share no vertices, edges, or faces" |
| Thm 1.1.1 (F23) | Explicit distinction: intersection ≠ boundary |

No file claims ∂S is connected (single component).

---

### M1.5: Euler Characteristic χ = 4

**Result: PASS**

All files that compute or state χ agree: **χ(∂S) = χ(∂T₊) + χ(∂T₋) = 2 + 2 = 4**.

| File | Method | Value |
|------|--------|-------|
| Def 0.0.0 (F01) | Component sum | χ = 2 + 2 = 4 |
| Thm 0.0.3 (F08) | V − E + F = 8 − 12 + 8 | χ = 4 |
| Def 0.1.1 (F18) | Both methods: component sum AND direct counting | χ = 4 ✓ |
| Def 1.1.4 (F26) | Correctly distinguishes diagram χ from boundary χ = 4 (lines 328–332) |

No file states χ = 2 (which would indicate a single closed surface / octahedron).

---

### M1.6: Surface Area = 2√3 · a²

**Result: PASS**

The canonical surface area formula appears in Def 0.1.1 (F18). Each regular tetrahedron with edge length a has surface area √3 · a², so two tetrahedra give 2√3 · a². No file states the octahedron surface area 4√3 · R².

---

### M1.7: ∂S Never Described as Octahedron

**Result: PASS**

Comprehensive search across all 26 files: **no file models ∂S as an octahedron.** The word "octahedron" appears in several files, but always in one of these contexts:

1. **Elimination of alternatives** — octahedron shown to fail GR2 (Def 0.0.0, Thm 0.0.3, Thm 0.0.3b, Prop 0.0.16a)
2. **Intersection region** — "central octahedral region where the tetrahedra intersect" (Def 0.1.1 §2.3), always explicitly distinguished from ∂S
3. **Symmetry group name** — "octahedral group O_h" as the name of the symmetry group S₄ × ℤ₂ (Thm 0.0.3 §1.1)
4. **Lattice geometry** — "octet truss" / octahedral-tetrahedral honeycomb (Thm 0.0.6)

No instance of ∂S being equated to, described as, or confused with an octahedron.

---

### M1.8: Octahedron Explicitly Eliminated

**Result: PASS**

The regular octahedron is **explicitly eliminated** as a candidate geometric realization in multiple files with rigorous mathematical arguments:

| File | Elimination Method |
|------|-------------------|
| Def 0.0.0 (F01, §4.4 lines 562–573) | "Octahedron fails GR2... Aut(octahedron) = O_h contains S₄... No surjective homomorphism φ: S₄ ↠ S₃ compatible with weight labeling" |
| Thm 0.0.3 (F08, §2.5) | Three-pronged elimination: (i) root-edge mismatch, (ii) face structure incompatibility, (iii) GR2 symmetry failure |
| Thm 0.0.3b (F09) | Extended elimination to all topological spaces including octahedron |
| Prop 0.0.16a (F13) | Octahedron eliminated from lattice tiling perspective |

---

### M1.9: Intersection Surface Distinguished from ∂S

**Result: PASS**

The geometric intersection surface (where T₊ and T₋ cut each other, forming a regular octahedron with V=6, E=12, F=8, χ=2) is always explicitly distinguished from ∂S.

| File | Distinction |
|------|------------|
| Def 0.1.1 (F18, §2.3) | "Two tetrahedra T₊ and T₋ interpenetrate geometrically, creating a central octahedral region. However, **topologically they remain two separate closed surfaces**." |
| Thm 1.1.1 (F23, lines 193–196) | Explicit clarification that intersection ≠ boundary |

No file conflates the two objects.

---

### M1.10: Vertex Coordinate Convention Consistency

**Result: PASS**

The canonical vertex coordinates for T₊ are:

$$v_R = (1,-1,-1)/\sqrt{3}, \quad v_G = (-1,1,-1)/\sqrt{3}, \quad v_B = (-1,-1,1)/\sqrt{3}, \quad v_W = (1,1,1)/\sqrt{3}$$

with T₋ vertices at $v_{\bar{c}} = -v_c$.

| File | Convention | Consistent? |
|------|-----------|------------|
| Def 0.1.1 (F18, §2.2) | $(1,-1,-1)/\sqrt{3}$ etc. | ✅ |
| Def 0.1.3 (F20, §2.1) | Same convention | ✅ |
| Thm 1.1.1 (F23) | Same convention | ✅ |

All files use the same unit-sphere normalization with centroid at origin.

---

### M1.11: Symmetry Group Description

**Result: NOTE**

The full symmetry group of the stella octangula is consistently identified as **O_h ≅ S₄ × ℤ₂** (order 48) across all files. However, one natural-language description is imprecise:

**Def 0.1.1 (F18), line 108:**
> `$S_4 \times \mathbb{Z}_2$ | Symmetry group | $S_4$ permutes colors, $\mathbb{Z}_2$ is charge conjugation`

**Issue:** S₄ permutes the **4 vertices of each tetrahedron** {R, G, B, W}, not "colors." Only S₃ ⊂ S₄ permutes the 3 colors {R, G, B}; the full S₄ also permutes the apex vertex W. The ℤ₂ description (charge conjugation) is correct.

**Impact:** MINOR. The abstract group identification is correct; only the natural-language gloss is imprecise. No downstream proof depends on this description.

---

### M1.12: Connectivity Statement in Thm 0.0.3

**Result: NOTE**

**Thm 0.0.3 (F08), line 178:**
> "By (GR2), the surjection Aut(K) → S₃ requires transitive action on colors. Combined with (GR3) antipodal symmetry, this implies all vertices lie in one connected component."

**Issue:** This statement is ambiguous. The stella octangula has **2 geometric connected components** (T₊ and T₋). What the text means is that all vertices lie in a single **orbit under the symmetry group** Aut(P) including τ. Definition 0.0.0 (F01, Lemma 0.0.0g, lines 454–461) carefully distinguishes between:

1. **Geometric connectivity:** 2 components (the tetrahedra share no vertices/edges)
2. **Symmetry-extended connectivity:** 1 orbit (τ swaps T₊ ↔ T₋)

The Thm 0.0.3 statement references Lemma 0.0.0g but does not reproduce its careful distinction. A reader encountering this line without reading Lemma 0.0.0g could incorrectly conclude the stella is geometrically connected.

**Impact:** MINOR. The mathematical argument is correct (it is proving that the structure cannot split into 3+ symmetry orbits). Lemma 0.0.0g provides the full clarification. No downstream proof is affected.

---

## Summary Table

| Check ID | Result | Description | Evidence | Severity |
|----------|--------|-------------|----------|----------|
| M1.1 | **PASS** | Vertex count = 8 (4+4) everywhere | F01, F08, F09, F18, F23, F26 | — |
| M1.2 | **PASS** | Edge count = 12 (6+6) everywhere | F01, F08, F18, F26 | — |
| M1.3 | **PASS** | Face count = 8 (4+4) everywhere | F01, F08, F18 | — |
| M1.4 | **PASS** | Connected components = 2 (disjoint union) | F01, F08, F10, F18, F23 | — |
| M1.5 | **PASS** | Euler characteristic χ = 4 everywhere | F01, F08, F18, F26 | — |
| M1.6 | **PASS** | Surface area = 2√3·a² (not octahedron value) | F18 | — |
| M1.7 | **PASS** | ∂S never described as octahedron | All 26 files | — |
| M1.8 | **PASS** | Octahedron explicitly eliminated | F01, F08, F09, F13 | — |
| M1.9 | **PASS** | Intersection surface distinguished from ∂S | F18, F23 | — |
| M1.10 | **PASS** | Vertex coordinates consistent | F18, F20, F23 | — |
| M1.11 | **NOTE** | S₄ description says "permutes colors" — should say "permutes tetrahedron vertices" | F18 line 108 | MINOR |
| M1.12 | **NOTE** | "One connected component" ambiguous — should say "one symmetry orbit" | F08 line 178 | MINOR |

---

## Overall Assessment

**M1 is COHERENT.** All 9 checks from the audit plan (M1.1–M1.9) PASS with specific evidence from multiple files. The stella octangula's combinatorial invariants are stated identically everywhere. The octahedron is never confused with ∂S and is rigorously eliminated. The intersection surface is properly distinguished.

The 3 additional checks (M1.10–M1.12) reveal 2 MINOR notes — imprecise natural-language descriptions that do not affect mathematical correctness or downstream proofs.

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 1,
  "module": "M1",
  "checks_total": 12,
  "checks_passed": 10,
  "checks_failed": 0,
  "checks_noted": 2,
  "findings": [
    {
      "check_id": "M1.1",
      "result": "PASS",
      "description": "Vertex count = 8 (4+4) consistent across all files",
      "evidence": "Def 0.0.0 §2.2, Thm 0.0.3 §1(a)/§2.2, Thm 0.0.3b, Def 0.1.1 §2.3, Thm 1.1.1, Def 1.1.4"
    },
    {
      "check_id": "M1.2",
      "result": "PASS",
      "description": "Edge count = 12 (6+6) consistent across all files",
      "evidence": "Def 0.0.0 Lemma 0.0.0g, Thm 0.0.3, Def 0.1.1 §2.3, Def 1.1.4 line 76"
    },
    {
      "check_id": "M1.3",
      "result": "PASS",
      "description": "Face count = 8 (4+4) consistent across all files",
      "evidence": "Def 0.0.0, Thm 0.0.3, Def 0.1.1 §2.3"
    },
    {
      "check_id": "M1.4",
      "result": "PASS",
      "description": "Connected components = 2 (disjoint union ∂T₊ ⊔ ∂T₋)",
      "evidence": "Def 0.0.0 Lemma 0.0.0g lines 454-461, Thm 0.0.3, Thm 0.0.15, Def 0.1.1 §2.3, Thm 1.1.1"
    },
    {
      "check_id": "M1.5",
      "result": "PASS",
      "description": "Euler characteristic χ = 4 (= 2+2) via both component sum and V-E+F",
      "evidence": "Def 0.0.0, Thm 0.0.3 (8-12+8=4), Def 0.1.1 §2.3 (both methods), Def 1.1.4 lines 328-332"
    },
    {
      "check_id": "M1.6",
      "result": "PASS",
      "description": "Surface area = 2√3·a² (not octahedron value 4√3·R²)",
      "evidence": "Def 0.1.1 and Def 0.1.1-Applications §12.3"
    },
    {
      "check_id": "M1.7",
      "result": "PASS",
      "description": "∂S never described as octahedron in any file",
      "evidence": "Full search of all 26 G1 files — octahedron appears only in elimination proofs, intersection descriptions, symmetry group names, lattice geometry"
    },
    {
      "check_id": "M1.8",
      "result": "PASS",
      "description": "Octahedron explicitly eliminated with rigorous proofs",
      "evidence": "Def 0.0.0 §4.4 lines 562-573, Thm 0.0.3 §2.5, Thm 0.0.3b, Prop 0.0.16a"
    },
    {
      "check_id": "M1.9",
      "result": "PASS",
      "description": "Intersection surface (V=6, χ=2) properly distinguished from ∂S (V=8, χ=4)",
      "evidence": "Def 0.1.1 §2.3, Thm 1.1.1 lines 193-196"
    },
    {
      "check_id": "M1.10",
      "result": "PASS",
      "description": "Vertex coordinate convention consistent across files",
      "evidence": "Def 0.1.1 §2.2, Def 0.1.3 §2.1, Thm 1.1.1 — all use (1,-1,-1)/√3 convention"
    },
    {
      "check_id": "M1.11",
      "result": "NOTE",
      "description": "S₄ description 'permutes colors' is imprecise — S₄ permutes tetrahedron vertices {R,G,B,W}, only S₃⊂S₄ permutes colors {R,G,B}",
      "evidence": "Def 0.1.1 line 108",
      "severity": "MINOR"
    },
    {
      "check_id": "M1.12",
      "result": "NOTE",
      "description": "'All vertices lie in one connected component' ambiguous — stella has 2 geometric components; should say 'one symmetry orbit'",
      "evidence": "Thm 0.0.3 line 178 vs Def 0.0.0 Lemma 0.0.0g lines 454-461",
      "severity": "MINOR"
    }
  ],
  "overall_result": "PASS"
}
```
