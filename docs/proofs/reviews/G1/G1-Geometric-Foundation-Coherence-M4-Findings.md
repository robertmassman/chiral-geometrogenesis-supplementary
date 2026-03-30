# G1 Geometric Foundation — Coherence Audit: Module M4 Findings

> **Module:** M4 — Key Correspondence Structures
> **Group:** G1 — Geometric Foundation
> **Layer:** 1 (Coherence)
> **Posture:** DEFENSIVE — verify internal consistency
> **Auditor:** Claude Opus 4.6 (autonomous audit agent)
> **Date:** 2026-03-14 (re-verified 2026-03-14)
> **Template:** [G1-Geometric-Foundation-Coherence-Audit.md](G1-Geometric-Foundation-Coherence-Audit.md) § Module 4
> **Re-verification (v2, 2026-03-14):** Second independent re-read of all key correspondence files (Def 0.0.0, Thm 0.0.2b, Thm 0.0.3, Thm 0.0.3b, Thm 0.0.12, Thm 0.0.13, Thm 0.0.15, Thm 0.0.16, Thm 1.1.1) confirms all 18 findings current. Weight vectors verified in both (T₃,Y) and (T₃,T₈) conventions across files. M4.17 residual (Corollary 0.0.13.1 line 119 still reads "Theorem 0.0.13" for Cartan data) and M4.18 (rank ≤ 2 attribution to Lem 0.0.2a instead of Prop 0.0.40) remain MINOR/unresolved in source files. No new findings.
> **Re-verification (v3, 2026-03-14):** Third independent full audit. Read Def 0.0.0, Thm 0.0.2b, Thm 0.0.3, Thm 0.0.3b, Thm 0.0.9, Thm 0.0.12, Thm 0.0.13, Thm 0.0.15, Lem 0.0.2a, Def 0.1.1, Def 0.1.4, Prop 0.0.6b, Thm 1.1.1, Def 1.1.4. All 18 findings independently confirmed. Weight convention bridge verified numerically: T₈ = Y·√3/2 maps w_R(T₃,Y)=(1/2,1/3) → w_R(T₃,T₈)=(1/2,1/(2√3)) ✓. Lem 0.0.2a §1 confirmed to give D_space ≥ N−1 (rank ≤ 3 for D_space=3), not rank ≤ 2 — M4.18 correct. Thm 0.0.13 Corollary 0.0.13.1 line 119 confirmed still reads "Theorem 0.0.13" for Cartan data — M4.17 correct. Additional instance found: Thm 0.0.15 line 586 also attributes "rank ≤ 2" to "Lemma 0.0.2a" in classification table (same issue as M4.18). No new findings beyond existing 18 checks.
> **Re-verification (v4, 2026-03-14):** Fourth independent audit using parallel subagent verification. (1) M4.17 confirmed: Corollary 0.0.13.1 line 119 still reads "Theorem 0.0.13" for Cartan data; all other cross-refs in Thm 0.0.13 (lines 159, 264-269, 24, 17-18) are correct. (2) M4.18 confirmed: Lem 0.0.2a gives D_space ≥ N−1 (lower bound → N ≤ 4 → rank ≤ 3); Prop 0.0.40 gives d_embed = N (exact → rank = 2). Thm 0.0.15 line 586 attribution "From D = 4 spacetime (Lemma 0.0.2a)" is technically incomplete — full chain requires Prop 0.0.40. (3) Weight conventions verified across 5 files: Def 0.1.1 uses (T₃,Y) with w_R=(1/2,1/3); Thm 1.1.1, Def 1.1.4, Def 0.1.4 use (T₃,T₈) with w_R=(1/2,1/(2√3)); bridge T₈=Y·√3/2 documented in Thm 1.1.1 §1.3 line 347. (4) Three SU(3) derivation paths independently verified: dimensional (Thm 0.0.2b selects N=3 from D=4), topological (Thm 0.0.15 determines SU(3) from Z₃+rank), categorical (Thm 0.0.12 Cartan-level only + Thm 0.0.13 consistency). All scope boundaries respected. No new findings; all 18 checks confirmed.
> **Re-verification (v5, 2026-03-14):** Fifth independent audit with parallel subagent verification of all key files. (1) M4.17 confirmed: Corollary 0.0.13.1 line 119 still reads "Theorem 0.0.13" for Cartan data — MINOR, unresolved. (2) M4.18 confirmed: Lem 0.0.2a §1 gives D_space ≥ N−1 → rank ≤ 3; Prop 0.0.40 gives d_embed = N → rank = 2. Thm 0.0.15 line 586 "rank ≤ 2? — From D = 4 spacetime (Lemma 0.0.2a)" still present — MINOR, unresolved. (3) Weight conventions verified across 5 files: Def 0.1.1 uses (T₃,Y) with w_R=(1/2,1/3); Thm 1.1.1 documents both conventions with bridge T₈=Y·√3/2 at line 347; Def 1.1.4 and Def 0.1.4 use (T₃,T₈) exclusively. Bridge formula documented ONLY in Thm 1.1.1 Step 7B — latent drift risk but no actual inconsistency. (4) M4.16 confirmed resolved: Thm 0.0.12 correctly references Thm 0.0.13 at §8.2 (line 274), §9.1 (line 308), §10.1 (line 330). (5) Three SU(3) paths confirmed independent: Path 1 (Thm 0.0.2b, D=N+1) and Path 2 (Thm 0.0.15, Z₃+rank) are fully independent; Path 3 (Thm 0.0.13, Tannaka) is properly self-classified as consistency result requiring Path 1/2 input. Scope boundaries explicitly declared and respected in all files. (6) Explored Thm 0.0.0a, Prop 0.0.XX, Thm 0.1.0, Thm 0.0.9 for missed correspondences — Thm 0.3.1 (W-direction) and Thm 0.2.2 (phase evolution) contain novel correspondences but are NOT in G1 file list, hence out of scope. No new in-scope findings; all 18 checks confirmed.

---

## Scope

Module M4 verifies that the **claimed isomorphisms and mappings** between geometric structures (stella octangula) and algebraic structures (SU(3) representation theory) are **mutually consistent** across all 26 proof files in thematic group G1.

The critical risks are:
1. Two files claiming the same correspondence with incompatible definitions
2. Mappings that are well-defined in one file but ill-defined when imported by another
3. Scope confusion — a mapping proved at Cartan-data level being cited as a full group isomorphism
4. Weight-vector normalization drift between physics (T₃, Y) and root-system (T₃, T₈) conventions

---

## Files Examined

All 26 G1 proof files were read in full. The files most relevant to M4 are:

| # | File | Abbreviation | Role in M4 |
|---|------|--------------|------------|
| F01 | `foundations/Definition-0.0.0-Minimal-Geometric-Realization.md` | Def 0.0.0 | Defines GR1–GR3 (weight map ι, symmetry map φ, conjugation τ) |
| F03 | `foundations/Theorem-0.0.2-Euclidean-From-SU3.md` | Thm 0.0.2 | Maps Killing form → Euclidean metric on weight space |
| F04 | `foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md` | Thm 0.0.2b | Establishes D = N + 1 formula |
| F05 | `foundations/Lemma-0.0.2a-Confinement-Dimension.md` | Lem 0.0.2a | Lower bound D_space ≥ N − 1 from affine independence |
| F06 | `foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md` | Prop 0.0.40 | Proves d_embed = N |
| F09 | `foundations/Theorem-0.0.3-Stella-Uniqueness.md` | Thm 0.0.3 | Uniqueness under GR1–GR3 |
| F10 | `foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md` | Thm 0.0.3b | Extends uniqueness to all topological spaces |
| F14 | `foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md` | Prop 0.0.6b | Discrete → continuous via exp map, Z₃ preservation |
| F15 | `foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md` | Thm 0.0.9 | Self-consistency loop GR1–GR3 → D=4 → SU(3) → stella |
| F16 | `foundations/Theorem-0.0.15-Topological-Determination-SU3.md` | Thm 0.0.15 | Z₃ phases + rank constraint → SU(3) |
| F17 | `foundations/Theorem-0.0.12-Categorical-Equivalence.md` | Thm 0.0.12 | A₂-Dec ≃ W(A₂)-Mod (Cartan data level) |
| F18 | `foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md` | Thm 0.0.13 | SU(3) ≅ Aut⊗(ω) via Tannaka–Krein |
| F19 | `Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md` | Def 0.1.1 | Vertex ↔ weight bijection table |
| F23 | `Phase0/Definition-0.1.4-Color-Field-Domains.md` | Def 0.1.4 | Domain boundaries ⊥ root vectors |
| F25 | `Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md` | Thm 1.1.1 | Full vertex ↔ weight map with transformation matrix A |
| F26 | `Phase1/Definition-1.1.4-Stella-Diagram-Rules.md` | Def 1.1.4 | Diagram rules with vertex weight table |

Additionally referenced:
- `verification-records/Theorem-1.1.1-Multi-Agent-Verification-2026-02-21.md` (W-3 convention fix)
- `reviews/G1/G1-Geometric-Foundation-Coherence-M10-Findings.md` (M10.8a/8b on weight normalization)

---

## Detailed Findings

### M4.1: Vertex ↔ Weight Map (ι) Consistency Across Files

**Result: PASS**

The core mapping — stella octangula vertices to SU(3) weight vectors — is stated in six files. In all cases, the structure is identical: 6 non-zero weight vertices (3 colors + 3 anti-colors) plus 2 apex vertices at zero weight.

| File | Map notation | Vertex structure | Zero-weight treatment |
|------|-------------|-----------------|----------------------|
| Def 0.0.0 (F01) | ι: V(P) → h* | 6 non-zero + 2 apex | ι(v_W) = 0 (Lemma 0.0.0c) |
| Thm 0.0.3 (F09) | GR1 encoding | 6 weight + 2 apex | Apex uniquely determined (equidistant) |
| Thm 0.0.3b (F10) | Cardinality bound | ≤ 6 + 2 = 8 | Zero weight not in 3⊕3̄ |
| Def 0.1.1 (F19) | Bijection table | 4 per tetrahedron | W vertices ↔ Cartan generators |
| Thm 1.1.1 (F25) | φ: Vertices → h* | v₁,v₂,v₃ → w_R,w_G,w_B; v₀ → 0 | Singlet direction |
| Def 1.1.4 (F26) | Diagram vertex table | R,G,B,R̄,Ḡ,B̄ | Not in diagram rules |

All six files agree on the 6+2 decomposition. The apex vertices are consistently identified as zero-weight states (singlet direction). No file contradicts this structure.

---

### M4.2: Weight Vector Normalization Convention

**Result: NOTE**

Two distinct normalization conventions are used across G1 files:

| Convention | Basis | w_R | w_G | w_B | Files using |
|-----------|-------|-----|-----|-----|-------------|
| **Physics** | (T₃, Y) | (1/2, 1/3) | (−1/2, 1/3) | (0, −2/3) | F19 (Def 0.1.1), F25 (Thm 1.1.1) |
| **Root-system** | (T₃, T₈) | (1/2, 1/(2√3)) | (−1/2, 1/(2√3)) | (0, −1/√3) | F14 (Prop 0.0.6b), F26 (Def 1.1.4), Lean code |

The bridge between conventions is: T₈ = Y·√3/2, or equivalently Y = 2T₈/√3.

**Key distinction:** In the (T₃, T₈) basis the weight triangle is equilateral in Euclidean metric; in the (T₃, Y) basis it is not. This was flagged as W-3 in the Thm 1.1.1 verification report and a convention bridge (T₈ = Y·√3/2) was explicitly documented in Def 0.1.4 (F23) Step 7B. Module M10 (checks M10.8a, M10.8b) also verified this and passed.

**Assessment:** The two conventions are physically equivalent and the bridge is documented, but the dual-convention usage creates a latent risk for downstream proofs that import weight vectors without specifying which basis. No actual inconsistency exists, but the convention drift warrants a NOTE.

---

### M4.3: Three SU(3) Derivation Paths Agree

**Result: PASS**

SU(3) is derived via three independent paths. All three converge on the same group:

| Path | Theorem | Method | What it establishes |
|------|---------|--------|-------------------|
| **Dimensional** | Thm 0.0.2 + 0.0.2b | D=4 → rank ≤ 2 + confinement → SU(3) | SU(3) is the unique confining SU(N) for D=4 |
| **Topological** | Thm 0.0.15 | Z₃ center + rank ≤ 2 → Cartan enumeration | SU(3) uniquely survives constraints |
| **Categorical** | Thm 0.0.12 + 0.0.13 | Stella Cartan data → Tannaka reconstruction | Stella data IS SU(3) data (consistency) |

**Cross-check:** The dimensional path selects SU(3) from D=4 input. The topological path selects SU(3) from Z₃ phases + dimension constraint. The categorical path confirms stella encodes SU(3) Cartan data. All three output the same group.

**Scope consistency:** Thm 0.0.12 explicitly states it operates at "Cartan data level only" — root system, weight lattice, Weyl group. Thm 0.0.13 extends this to the full continuous group via Tannaka–Krein, using the fiber functor ω constructed from the vertex ↔ weight identification. This division of labor is cleanly stated with no over-claiming.

---

### M4.4: Categorical Equivalence Scope Properly Bounded

**Result: PASS**

Thm 0.0.12 claims:
$$\mathbf{A_2\text{-Dec}} \simeq \mathbf{W(A_2)\text{-Mod}}$$

The proof explicitly lists what this does and does NOT establish:

| Preserved | Not preserved |
|-----------|--------------|
| ✅ Root system Φ(A₂) | ❌ Full continuous Lie group |
| ✅ Weight lattice | ❌ Tensor product structure |
| ✅ Weyl group W = S₃ | ❌ 8 gluon generators |
| ✅ Discrete/combinatorial structures | ❌ Continuous group parameters |

No downstream file in G1 cites Thm 0.0.12 as establishing the full SU(3) Lie group. Files that need the full group (e.g., Prop 0.0.6b for the exponential map) cite Thm 0.0.13 (Tannaka reconstruction) instead. The scope boundary is respected.

---

### M4.5: Tannaka Reconstruction — Not Circular

**Result: PASS**

Thm 0.0.13 (§0) explicitly addresses the circularity concern. The logical chain is:

```
Step 1: D = 4 established (Thm 0.0.1) — independent of SU(3)
Step 2: SU(3) SELECTED (Thm 0.0.2) — unique SU(N) for D=4
Step 3: Stella constructed (Thm 0.0.3) — unique minimal realization
Step 4: Fiber functor ω defined (this theorem) — using vertex ↔ weight
Step 5: Tannaka reconstruction CONFIRMS consistency
```

The theorem self-classifies as a **consistency result**, not a pure derivation. It does NOT claim to derive SU(3) from geometry alone. The fiber functor ω uses knowledge that "vertices ARE weights" — this comes from the D=4 → SU(3) selection chain, not from this theorem.

**Cross-check with Thm 0.0.9:** The self-consistency loop (GR1–GR3 → GR+QM → D=4 → SU(3) → stella → GR1–GR3) is explicitly described as a consistency check, not a derivation. Both theorems agree on the logical status.

---

### M4.6: Weyl Group ↔ Geometric Symmetry Homomorphism

**Result: PASS**

The Weyl group correspondence is stated in three files:

| File | Claim | Groups |
|------|-------|--------|
| Def 0.0.0 (F01) | GR2: ∃ φ: Aut(P) → S₃ surjective | Polyhedron automorphisms → Weyl group |
| Thm 1.1.1 (F25) | Φ: Stab_{S₄}(v_W) ≅ W(su(3)) | Apex stabilizer ≅ Weyl group |
| Thm 0.0.12 (F17) | S₃-equivariance of functors F, G | Categories respect Weyl action |

All three consistently identify S₃ as the relevant symmetry group. The generator correspondence is explicit in Thm 1.1.1 (§7):
- σ₁ (tetrahedron reflection swapping v_R ↔ v_G) ↔ s₁ (Weyl reflection in H_{α₁})
- σ₂ (tetrahedron reflection swapping v_G ↔ v_B) ↔ s₂ (Weyl reflection in H_{α₂})

These generators satisfy the A₂ Coxeter relations (s₁² = s₂² = (s₁s₂)³ = 1), consistent across all files.

---

### M4.7: Antipodal/Conjugation Map Consistency

**Result: PASS**

The charge conjugation / antipodal map is defined in four files:

| File | Notation | Definition | Weight effect |
|------|----------|------------|---------------|
| Def 0.0.0 (F01) | τ: V → V | Involution | ι(τ(v)) = −ι(v) |
| Def 0.1.1 (F19) | I: v ↦ v̄ | T₊ ↔ T₋ exchange | Reverses weights |
| Thm 1.1.1 (F25) | v₁' = −v₁ | Point reflection through origin | φ(v') = −φ(v) |
| Def 1.1.4 (F26) | I: v ↦ v̄ | Rule 4 | w_{v̄} = −w_v |

All four consistently define conjugation as an involution that negates weight vectors and exchanges T₊ ↔ T₋. The notation varies (τ vs I vs point reflection) but the mathematical content is identical.

---

### M4.8: Root System ↔ Edge Mapping

**Result: PASS**

The correspondence between stella edges and A₂ roots is stated consistently:

| File | Claim | Root count |
|------|-------|-----------|
| Thm 0.0.12 (F17) | Edges encode Φ(A₂) | 6 roots: ±α₁, ±α₂, ±(α₁+α₂) |
| Thm 0.0.13 (F18) | 6 edges = 6 charged gluons | 6 off-diagonal in adjoint |
| Thm 0.0.16 (F12) | 12 FCC neighbors = 6_intra + 6_inter | 6 roots within 3 or 3̄ |
| Def 1.1.4 (F26) | Directed edges carry phase ω^{Δc} | 6 color-changing edges |
| Def 0.1.4 (F23) | Domain boundaries ⊥ root vectors | 3 boundary planes at 120° |

The 6 roots are consistently identified with 6 edges (or color-changing gluons) across all files. The 120° angular structure is preserved in the domain boundary perpendicularity (F23 §8.2).

---

### M4.9: Apex ↔ Adjoint Decomposition

**Result: PASS**

The apex vertices play a dual role: they are zero-weight singlet directions AND correspond to Cartan generators. These are checked for consistency:

| File | Apex interpretation | Context |
|------|-------------------|---------|
| Thm 1.1.1 (F25) | φ(v₀) = 0, singlet direction | Weight map |
| Def 0.1.1 (F19) | 2 apex ↔ 2 Cartan generators (T₃, T₈) | Gauge structure |
| Thm 0.0.13 (F18) | 6 edges + 2 apexes = 8 gluons | Adjoint decomposition |
| Thm 0.0.3b (F10) | Zero weight not in 3⊕3̄ | Representation theory |

**Consistency check:** In the adjoint representation **8**, there are 6 root vectors (non-zero weight) and 2 zero-weight states (Cartan generators). The apex vertices sit at zero weight in the fundamental representation weight space, which is exactly where the Cartan generators appear in the adjoint. All files agree: 6 + 2 = 8 for the adjoint.

Thm 0.0.3b correctly notes that zero weight does NOT appear in the **3⊕3̄** fundamental representation — the apex vertices are additional geometric structure beyond the weight encoding. This is consistent with Def 0.0.0 Lemma 0.0.0c (apex weights are zero) and the 6+2 vertex count.

---

### M4.10: D = N + 1 Formula — Logical Status

**Result: NOTE**

The D = N + 1 formula appears with different logical status in different files:

| File | Status of D = N + 1 | Logical role |
|------|---------------------|-------------|
| Thm 0.0.2b (F04) | **Derived** from representation theory + physical hypotheses | Primary derivation |
| Thm 0.0.15 (F16) | **Output** — "D = N + 1 is now OUTPUT, not input" | Derived as consequence |
| Thm 0.0.9 (F15) | Used within self-consistency loop | Part of closed loop |
| Prop 0.0.40 (F06) | **Derived** d_embed = N (equivalent to D = N + 1 with time) | Independent derivation |

**Assessment:** The formula is derived independently in two places (Thm 0.0.2b from angular/radial/temporal decomposition, and Prop 0.0.40 from the confinement squeeze argument). In Thm 0.0.15, it emerges as an output of the topological determination rather than being assumed. In Thm 0.0.9, it appears in a self-consistency loop that is explicitly labeled as a consistency check, not a derivation.

These roles are logically compatible: a formula can be derived in one theorem, confirmed as output in another, and verified in a consistency loop. However, the subtlety of these distinct logical roles warrants a NOTE — a careless reader could mistake the consistency loop for a circular derivation.

---

### M4.11: Z₃ Phase Mapping Consistency

**Result: PASS**

The Z₃ center correspondence is checked across all files that mention it:

| File | Z₃ source | Values | Role |
|------|-----------|--------|------|
| Thm 0.0.15 (F16) | Stella 3-fold rotation | {1, ω, ω²}, ω = e^{2πi/3} | Selects SU(3) |
| Def 0.1.2 (F20) | Color field phases | {0, 2π/3, 4π/3} | Phase assignment |
| Prop 0.0.6b (F14) | Center Z(SU(3)) | {1, ω, ω²} | Preserved in continuum limit |
| Def 1.1.4 (F26) | Edge phase factors | ω^{Δc} | Diagram rules |
| Thm 0.1.0 (F24) | Fisher metric derivation | Derived, not postulated | Information-geometric |

All files agree: the Z₃ structure is {1, ω, ω²} with ω = e^{2πi/3}, corresponding to phases {0, 2π/3, 4π/3}. The continuum limit (F14) explicitly proves Z₃ is preserved as an algebraic invariant through all three limit procedures (spatial, gauge, thermodynamic).

---

### M4.12: FCC Lattice ↔ A₃ Root Lattice Correspondence

**Result: PASS**

The identification of the FCC lattice with the A₃ root lattice is stated consistently:

| File | Claim | Evidence |
|------|-------|---------|
| Thm 0.0.6 (F13) | FCC vertex set: Λ = {(n₁,n₂,n₃) ∈ ℤ³ : n₁+n₂+n₃ ≡ 0 mod 2} | Direct construction |
| Prop 0.0.16a (F11) | A₃ uniquely forced among rank-3 root lattices | B₃, C₃ eliminated by coordination number and simply-laced requirement |
| Thm 0.0.16 (F12) | Coordination number 12 derived from SU(3) rep theory | 6_intra + 6_inter |
| Prop 0.0.6b (F14) | FCC → ℝ³ in continuum limit (a → 0) | Symmetry enhancement O → SO(3) |

The lattice definition, coordination number, and root lattice identification are mutually consistent. The elimination of alternatives (B₃ has coordination 6; C₃ is not simply-laced) is correct.

---

### M4.13: Pressure Function ↔ Geometry Correspondence

**Result: PASS**

The pressure functions are defined on the stella geometry and checked for consistency with the weight structure:

| File | Correspondence | Consistency |
|------|---------------|-------------|
| Def 0.1.3 (F21) | P_c peaked at vertex x_c | Vertices identical to Def 0.1.1 |
| Def 0.1.4 (F23) | Domain D_c = Voronoi cell of x_c | Boundaries ⊥ root vectors |
| Prop 0.1.3a (F22) | Physics depends only on axioms P1–P7, not specific form | Form-independence proven |

The domain boundaries at 120° angles match the A₂ root system angular structure. The vertex-face duality (color sourced at vertex, suppressed at opposite face) is consistent with the weight ↔ anti-weight mapping.

---

### M4.14: Transformation Matrix A (Thm 1.1.1) Well-Definedness

**Result: PASS**

Thm 1.1.1 (F25 §4.3) defines the linear transformation from 3D stella projection to 2D weight space:

$$\mathbf{A} = \begin{pmatrix} \frac{3}{4\sqrt{2}} & -\frac{\sqrt{3}}{4\sqrt{2}} \\ \frac{1}{2\sqrt{2}} & \frac{\sqrt{6}}{4} \end{pmatrix}$$

This matrix:
- Has det(A) ≠ 0 (verified: det = 3√6/(16√2)·1 − (−√3·1)/(4√2·2√2) ≠ 0), so it is invertible
- Maps the projected equilateral triangle to the correct weight positions
- Is S₃-equivariant (commutes with the Weyl group action)

No other file cites or redefines this matrix, so there is no conflict. The matrix is used only in Thm 1.1.1's internal derivation.

---

### M4.15: Confinement Selection Rule Consistency

**Result: PASS**

The singlet condition (color confinement) is stated consistently:

| File | Statement | Form |
|------|-----------|------|
| Def 1.1.4 (F26) | Rule 5: Physical states satisfy Σw_v = 0 | Weight sum closure |
| Thm 0.0.13 (F18) | Singlet states: R-R̄, G-Ḡ, B-B̄ and ε^{ijk} | Representation theory |
| Def 0.1.1 (F19) | Phase cancellation: 1 + ω + ω² = 0 | Z₃ structure |

The closure rule Σw_v = 0 correctly identifies mesons (w + (−w) = 0) and baryons (w_R + w_G + w_B = 0, verified from the weight values in either convention). The phase cancellation 1 + ω + ω² = 0 is the Z₃ analog of the same condition. Both formulations agree.

---

## Summary

| Check ID | Result | Description |
|----------|--------|-------------|
| M4.1 | **PASS** | Vertex ↔ weight map (ι) structure: 6+2 decomposition consistent across 6 files |
| M4.2 | **NOTE** | Weight normalization: two conventions (T₃,Y) vs (T₃,T₈) in use; bridge documented but drift risk |
| M4.3 | **PASS** | Three SU(3) derivation paths (dimensional, topological, categorical) all converge on SU(3) |
| M4.4 | **PASS** | Categorical equivalence scope properly bounded to Cartan data; respected by downstream files |
| M4.5 | **PASS** | Tannaka reconstruction correctly self-classifies as consistency result; not circular |
| M4.6 | **PASS** | Weyl group ↔ geometric symmetry: S₃ with correct generators in all files |
| M4.7 | **PASS** | Antipodal/conjugation map: involution negating weights, consistently defined in 4 files |
| M4.8 | **PASS** | Root system ↔ edge mapping: 6 roots = 6 edges across all files |
| M4.9 | **PASS** | Apex ↔ adjoint decomposition: 6 roots + 2 Cartan = 8 gluons consistently |
| M4.10 | **NOTE** | D = N + 1 formula has distinct logical roles (derived/output/loop); compatible but subtle |
| M4.11 | **PASS** | Z₃ phase mapping: {1, ω, ω²} identical across all files; continuum preservation proven |
| M4.12 | **PASS** | FCC ↔ A₃ root lattice: definition, coordination, uniqueness all consistent |
| M4.13 | **PASS** | Pressure function ↔ geometry: domain boundaries match root vectors |
| M4.14 | **PASS** | Transformation matrix A: well-defined, invertible, S₃-equivariant |
| M4.15 | **PASS** | Confinement selection rule: Σw_v = 0 consistent with Z₃ phase cancellation |

---

## Supplementary Findings (2026-03-14 Re-Audit)

> **Re-auditor:** AutoVerifier-CG (Claude Opus 4.6), independent re-read of all key correspondence files
> **Date:** 2026-03-14
> **Motivation:** The original M4 audit (above) correctly verified mathematical consistency of all correspondences. This re-audit performed a closer read of cross-references between Thm 0.0.12 and 0.0.13, uncovering numbering errors not caught in the first pass.

### M4.16: Cross-Reference Errors — Thm 0.0.12 Cites Itself as "Tannaka Reconstruction"

**Result: ~~FAIL~~ → PASS (RESOLVED)**

> **Resolution (2026-03-14, autoinvestigator):** All three instances in Thm 0.0.12 have been corrected:
> - §8.2: Now reads "Future Work (Theorem 0.0.13)" ✅
> - §9.1: Now reads "requires Theorem 0.0.13 (Tannaka Reconstruction)" ✅
> - §10.1 header: Now reads "Theorem 0.0.13 (Tannaka Reconstruction)" ✅

~~Thm 0.0.12 (Categorical Equivalence) contains three instances where it references "Theorem 0.0.12" when it means Theorem 0.0.13 (Tannaka Reconstruction).~~

**Status: RESOLVED** — All three cross-reference errors fixed.

---

### M4.17: Cross-Reference Errors — Thm 0.0.13 Cites Itself as "Categorical Equivalence"

**Result: ~~FAIL~~ → NOTE (PARTIALLY RESOLVED)**

> **Resolution (2026-03-14, autoinvestigator):** 3 of 4 original instances fixed:
> - §3.1: Now correctly reads "Theorem 0.0.12 established" ✅
> - §6.1 table header: Now correctly shows "Theorem 0.0.12 | Theorem 0.0.13" ✅
> - §6.1 gap text: Now correctly reads "Theorem 0.0.12: Cartan data determines group up to isogeny" ✅
> - §10: Now correctly reads "hedging in Theorem 0.0.12" ✅
>
> **Remaining issue (1 instance):**
> - Corollary 0.0.13.1 (line 119): "The stella octangula encodes not just the discrete Cartan data (**Theorem 0.0.13**) but the full continuous..." — should reference **Theorem 0.0.12** since Cartan data equivalence is that theorem's result.

**Status: PARTIALLY RESOLVED** — 4 of 4 original instances fixed, but 1 new instance found in Corollary 0.0.13.1 (MINOR severity — does not affect mathematical content).

---

### M4.18: Rank Constraint Attribution in Thm 0.0.15

**Result: NOTE — MINOR (UNRESOLVED)**

Thm 0.0.15 (Topological Determination of SU(3)) claims "rank(G) ≤ D_space − 1 = 2" and attributes this to Lemma 0.0.2a. However:

- **Lemma 0.0.2a** establishes D_space ≥ N − 1 for SU(N), giving N ≤ D_space + 1 = 4, hence **rank ≤ 3** (not ≤ 2).
- **Proposition 0.0.40** establishes d_embed = rank + 1, giving rank = d_embed − 1 = D_space − 1 = **2** (exact).

The rank ≤ 2 bound is correct (via Prop 0.0.40) but mis-attributed to Lem 0.0.2a. Specifically, in the dependencies section:

> "Physical Hypothesis 0.0.0f...now derived in [Proposition 0.0.40]. **Enters via Lemma 0.0.2a**: the rank constraint rank(G) ≤ D_space − 1 = 2"

The phrase "Enters via Lemma 0.0.2a" is misleading — Lem 0.0.2a provides the weaker bound rank ≤ 3, while the stronger rank ≤ 2 comes from Prop 0.0.40.

**Note:** The proof in §3.4 uses four independent constraints (N ≥ 3, N ≤ 4, 3|N, Z₄ exclusion) whose intersection gives N = 3 regardless of whether the rank bound is 2 or 3. So the **mathematical conclusion is unaffected**.

---

### Supplementary Summary

| Check ID | Original Result | Current Result | Description | Severity |
|----------|----------------|----------------|-------------|----------|
| M4.16 | **FAIL** | **PASS** (resolved) | Thm 0.0.12 cross-references to Thm 0.0.13 — all 3 instances fixed | — |
| M4.17 | **FAIL** | **NOTE** (1 residual) | Thm 0.0.13 cross-references — 4/4 original fixed; 1 new instance in Corollary 0.0.13.1 | MINOR |
| M4.18 | **NOTE** | **NOTE** (unresolved) | Rank ≤ 2 constraint in Thm 0.0.15 attributed to Lem 0.0.2a (gives rank ≤ 3); actual source is Prop 0.0.40 | MINOR |

### Updated Overall Assessment

With all resolutions applied, the revised totals are:

| Metric | Original | Supplementary (initial) | After Resolution | Combined |
|--------|----------|-------------------------|------------------|----------|
| Checks | 15 | 3 | — | 18 |
| PASS | 13 | 0 → 1 | — | 14 |
| FAIL | 0 | 2 → 0 | — | **0** |
| NOTE | 2 | 1 → 2 | — | 4 |
| Overall | PASS | CONDITIONAL PASS → PASS | — | **PASS** |

**PASS rationale:** Both original FAILs (M4.16, M4.17) have been resolved. M4.16 is fully fixed; M4.17 has one residual minor instance (Corollary 0.0.13.1 referencing "Theorem 0.0.13" for Cartan data equivalence) which is a MINOR labeling issue with no mathematical impact. All key correspondence structures — vertex ↔ weight, root ↔ edge, Weyl ↔ symmetry, categorical equivalence scope, Tannaka circularity handling — are internally consistent across the 26 G1 proof files.

### Remaining Remediation

**Priority 1 (MINOR) — Fix Corollary 0.0.13.1 cross-reference (1 edit):**

In `foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md`:
- Corollary 0.0.13.1: "not just the discrete Cartan data (Theorem 0.0.13)" → "not just the discrete Cartan data (Theorem 0.0.12)"

**Priority 2 (MINOR) — Clarify rank constraint source in Thm 0.0.15:**

In `foundations/Theorem-0.0.15-Topological-Determination-SU3.md` dependencies section, change "Enters via Lemma 0.0.2a" to "Enters via Proposition 0.0.40 (Lem 0.0.2a provides only the weaker bound rank ≤ 3)."

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 1,
  "module": "M4",
  "checks_total": 18,
  "checks_passed": 14,
  "checks_failed": 0,
  "checks_noted": 4,
  "findings": [
    {
      "check_id": "M4.1",
      "result": "PASS",
      "description": "Vertex-weight map (ι) 6+2 decomposition consistent across all files",
      "evidence": "Def 0.0.0 Lemma 0.0.0a/c; Thm 0.0.3 §2.4; Thm 0.0.3b §4.2.3; Def 0.1.1 §2.2; Thm 1.1.1 §4; Def 1.1.4 §2.1"
    },
    {
      "check_id": "M4.2",
      "result": "NOTE",
      "description": "Two weight normalization conventions in use: (T₃,Y) and (T₃,T₈) with bridge T₈ = Y·√3/2",
      "evidence": "Def 0.1.1 uses (T₃,Y); Def 1.1.4 uses (T₃,T₈); bridge documented in Def 0.1.4 Step 7B and Thm 1.1.1 verification W-3"
    },
    {
      "check_id": "M4.3",
      "result": "PASS",
      "description": "Three independent SU(3) derivation paths converge on the same group",
      "evidence": "Dimensional: Thm 0.0.2+0.0.2b; Topological: Thm 0.0.15; Categorical: Thm 0.0.12+0.0.13"
    },
    {
      "check_id": "M4.4",
      "result": "PASS",
      "description": "Categorical equivalence explicitly scoped to Cartan data level; no downstream over-citing",
      "evidence": "Thm 0.0.12 scope table: ✅ discrete/combinatorial, ❌ continuous group. Prop 0.0.6b cites Thm 0.0.13 for full group."
    },
    {
      "check_id": "M4.5",
      "result": "PASS",
      "description": "Tannaka reconstruction self-classifies as consistency result; circularity explicitly addressed",
      "evidence": "Thm 0.0.13 §0: logical chain Steps 1-5; table of 'What It DOES' vs 'What It Does NOT'"
    },
    {
      "check_id": "M4.6",
      "result": "PASS",
      "description": "Weyl group ↔ geometric symmetry homomorphism: S₃ with generators σ₁↔s₁, σ₂↔s₂",
      "evidence": "Def 0.0.0 GR2; Thm 1.1.1 §7; Thm 0.0.12 S₃-equivariance"
    },
    {
      "check_id": "M4.7",
      "result": "PASS",
      "description": "Conjugation/antipodal map consistently defined as weight-negating involution in 4 files",
      "evidence": "Def 0.0.0 GR3 (τ); Def 0.1.1 (I); Thm 1.1.1 (point reflection); Def 1.1.4 Rule 4 (I)"
    },
    {
      "check_id": "M4.8",
      "result": "PASS",
      "description": "Root system ↔ edge mapping: 6 A₂ roots = 6 stella edges across all files",
      "evidence": "Thm 0.0.12; Thm 0.0.13; Thm 0.0.16; Def 1.1.4; Def 0.1.4 §8.2"
    },
    {
      "check_id": "M4.9",
      "result": "PASS",
      "description": "Apex vertex interpretation consistent: zero-weight/Cartan/adjoint-completion (6+2=8)",
      "evidence": "Thm 1.1.1 (φ(v₀)=0); Def 0.1.1 (apex↔T₃,T₈); Thm 0.0.13 (6+2=8); Thm 0.0.3b (zero not in 3⊕3̄)"
    },
    {
      "check_id": "M4.10",
      "result": "NOTE",
      "description": "D=N+1 formula has distinct logical roles across files (derived, output, loop element); compatible but subtle",
      "evidence": "Derived: Thm 0.0.2b, Prop 0.0.40; Output: Thm 0.0.15; Loop: Thm 0.0.9"
    },
    {
      "check_id": "M4.11",
      "result": "PASS",
      "description": "Z₃ phase mapping {1,ω,ω²} identical in all files; continuum preservation proven",
      "evidence": "Thm 0.0.15; Def 0.1.2; Prop 0.0.6b §(d); Def 1.1.4; Thm 0.1.0"
    },
    {
      "check_id": "M4.12",
      "result": "PASS",
      "description": "FCC lattice ↔ A₃ root lattice: definition, coordination (12), and uniqueness consistent",
      "evidence": "Thm 0.0.6 (construction); Prop 0.0.16a (uniqueness); Thm 0.0.16 (coordination); Prop 0.0.6b (continuum limit)"
    },
    {
      "check_id": "M4.13",
      "result": "PASS",
      "description": "Pressure domain boundaries perpendicular to root vectors, matching A₂ angular structure",
      "evidence": "Def 0.1.3; Def 0.1.4 §8.2; Prop 0.1.3a (form-independence)"
    },
    {
      "check_id": "M4.14",
      "result": "PASS",
      "description": "Transformation matrix A (3D→2D weight space) is invertible and S₃-equivariant",
      "evidence": "Thm 1.1.1 §4.3"
    },
    {
      "check_id": "M4.15",
      "result": "PASS",
      "description": "Confinement closure rule Σw_v=0 consistent with Z₃ cancellation 1+ω+ω²=0",
      "evidence": "Def 1.1.4 Rule 5; Thm 0.0.13; Def 0.1.1"
    },
    {
      "check_id": "M4.16",
      "result": "PASS",
      "description": "Thm 0.0.12 cross-references to Thm 0.0.13 — all 3 original errors FIXED",
      "evidence": "Thm 0.0.12 §8.2, §9.1, §10.1 now correctly reference Theorem 0.0.13"
    },
    {
      "check_id": "M4.17",
      "result": "NOTE",
      "description": "Thm 0.0.13 cross-references — 4/4 original errors fixed; 1 residual in Corollary 0.0.13.1 (line 119)",
      "evidence": "Corollary 0.0.13.1: 'not just the discrete Cartan data (Theorem 0.0.13)' should say Theorem 0.0.12",
      "severity": "MINOR"
    },
    {
      "check_id": "M4.18",
      "result": "NOTE",
      "description": "Rank ≤ 2 constraint in Thm 0.0.15 attributed to Lem 0.0.2a (gives rank ≤ 3); actual source is Prop 0.0.40",
      "evidence": "Thm 0.0.15 dependencies: 'Enters via Lemma 0.0.2a: rank(G) ≤ D_space − 1 = 2'; Lem 0.0.2a §1 gives D_space ≥ N−1 → rank ≤ 3",
      "severity": "MINOR"
    }
  ],
  "overall_result": "PASS"
}
```
