# Theorem 0.0.0a: Polyhedral Necessity for Emergent Spacetime

## Status: 🔶 NOVEL ✅ VERIFIED — FOUNDATIONAL NECESSITY THEOREM

**Role in Framework:** This theorem establishes that discrete encoding is **necessary** (given the non-circular emergence principle — see §4, Lemma 0.0.0a.3) for gauge structure to produce emergent spacetime, and that polyhedral complexes are a natural instantiation within the broader class of discrete structures (simplicial complexes, CW complexes) satisfying all four requirements. It addresses the question: "Why discrete structure, and why polyhedra specifically?" at the deepest conceptual level.

**Lean 4 Formalization:** ✅ **COMPLETE** — `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_0a.lean`
- All proofs compile without `sorry`
- 2 axioms (Cantor cardinality arguments, properly cited)
- Main theorem `polyhedral_necessity` proven by case analysis

**Dependencies:**
- ✅ **Theorem 0.0.6 (Spatial Extension from Honeycomb)** — FCC lattice provides pre-geometric coordinates
- ✅ **Theorem 0.0.3 §5.3.1** — Z₃ center symmetry is geometric (kinematic)
- ✅ **Definition 0.0.0 Lemma 0.0.0f** — Embedding dimension from confinement
- ✅ **Theorem 0.0.1 (D=4 from Observer Existence)** — Requires GR+QM, which Theorem 0.0.10 derives

**Paper Reference:** Paper 1, Section 2.5 "Why Polyhedral Encoding is Necessary"

---

## File Structure

This theorem uses the **3-file academic structure** for verification efficiency:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Theorem-0.0.0a-Polyhedral-Necessity.md** (this file) | Statement & motivation | §1-5 | Conceptual correctness |
| **[Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md)** | Complete proof | §6-9, Appendices | Mathematical rigor |
| **[Theorem-0.0.0a-Polyhedral-Necessity-Applications.md](./Theorem-0.0.0a-Polyhedral-Necessity-Applications.md)** | Verification & predictions | §10-14 | Numerical accuracy |

**Quick Links:**
- [→ See the complete derivation](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md)
- [→ See applications and verification](./Theorem-0.0.0a-Polyhedral-Necessity-Applications.md)

---

## Verification Status

**Last Verified:** 2026-01-20
**Verified By:** Multi-agent peer review (Mathematical, Physics, Literature agents)
**Verification Report:** [Theorem-0.0.0a-Verification-Report.md](../../verification/shared/Theorem-0.0.0a-Verification-Report.md)

### Lean 4 Formalization Status

| Component | Status | Location |
|-----------|--------|----------|
| Main theorem `polyhedral_necessity` | ✅ Proven | Line ~610 |
| Lemma 0.0.0a.1 (fiber bundle) | ✅ Proven | Line ~596 |
| Lemma 0.0.0a.2 (discrete charge) | ✅ Proven | Line ~298 |
| Lemma 0.0.0a.3 (pre-geometric coords) | ✅ Proven | Line ~421 |
| Lemma 0.0.0a.4 (connectionless coherence) | ✅ Proven | Line ~511 |
| No-go theorem (continuous substrates) | ✅ Proven | Line ~793 |
| Uniqueness theorem | ✅ Proven | Line ~920 |
| Construction hierarchy (ℕ→ℤ→ℚ→ℝ) | ✅ Proven | Lines 353-443 |
| Framework justification lemmas | ✅ Proven | Lines 445-544 |
| Edge derivation from faces | ✅ Proven | Lines 799-937 |

**Axioms Used (2 total):**
| Axiom | Justification |
|-------|---------------|
| `real_not_discretely_definable` | Cantor's diagonal argument (1874) |
| `retract_of_real_not_discrete` | Cardinality: Card(S) ≥ Card(ℝ) for retract |

**New in Latest Revision (2026-01-01):**
- Added `EmergenceRequirementsProp` (Prop-based version with proof witnesses)
- Added formal construction hierarchy ordering (ℕ < ℤ < ℚ < ℝ)
- Added explicit justification theorems for each framework assessment
- Strengthened uniqueness proof with proper edge derivation from faces
- Added scope documentation clarifying proven vs. asserted claims

### Verification Checklist
- [x] All symbols defined in symbol table
- [x] Dimensional consistency verified
- [x] Dependencies on other theorems valid
- [x] No circular references (bootstrap with 0.0.10/0.0.1 is intentional, not circular)
- [x] Cross-references accurate
- [x] Lemma 0.0.0a.3 correctly reframed (topology ≠ metric, emergence requires pre-continuum structure)
- [x] Lemma 0.0.0a.4 correctly distinguishes gravitational vs gauge parallel transport (2026-01-20)
- [x] Necessity claim qualified ("among known frameworks")
- [x] Causal set references added (including Sorkin 2003)
- [x] Spin foam references added (Perez 2013)
- [x] Lorentz violation bounds properly cited with E_P units
- [x] "Deterministic" claim clarified with quantum corrections note
- [x] **Lean 4 formalization complete** (2026-01-01)
- [x] Smooth manifold realizations addressed in §3.5, §5.2 item 6 (A1.5 adversarial finding, 2026-02-23)

## Direct Prerequisites (verify these first)

| Theorem | Section | What It Provides |
|---------|---------|------------------|
| Theorem 0.0.6 | §1, §2 | Pre-geometric coordinates via FCC lattice |
| Theorem 0.0.3 | §5.3.1 | Z₃ center symmetry is kinematic (not dynamical) |
| Definition 0.0.0 | Lemma 0.0.0f | Physical embedding dimension = N from confinement |
| Theorem 0.0.10 | §1 | GR+QM derived from framework (closes loop with 0.0.1) |

### Dependent Theorems (will need re-verification if this changes)

- **Theorem 0.0.0 (GR1-GR3 from First Principles):** Uses polyhedral necessity as motivation
- **Theorem 0.0.9 (Framework Derives GR+QM):** References this for conceptual completeness

---

## Critical Claims (for verification focus)

1. **Fiber Bundle Limitation:** Principal bundles P → M presuppose base manifold M
   - Check: Fiber bundle definition requires base space as input

2. **Discrete Charge from Confinement:** Z₃ center classifies by N-ality without continuous analog
   - Verify: N-ality is discrete (triality) for SU(3)

3. **Pre-Geometric Coordinate Existence:** FCC lattice provides coordinates without metric
   - Verify: Integer labels $(n_1, n_2, n_3)$ are purely combinatorial

4. **Phase Matching Without Connection:** Shared faces enforce phase coherence combinatorially
   - Verify: Theorem 0.0.6 §1(c) phase coherence mechanism

---

## 1. Statement

**Theorem 0.0.0a (Polyhedral Necessity for Emergent Spacetime)**

Among known mathematical frameworks and given the non-circular emergence principle (Lemma 0.0.0a.3, §4), discrete encoding is **necessary** for gauge structure to produce emergent spacetime—not merely one option among many. Polyhedral complexes are a natural class of discrete structures satisfying all four requirements below; see the Conclusion for the relationship to other discrete structures (simplicial complexes, CW complexes). Specifically:

**(a) Fiber Bundle Insufficiency:** Principal G-bundles P → M require the base manifold M as input; they cannot derive the spacetime they presuppose.

**(b) Discrete Charge Classification:** The Z₃ center of SU(3) classifies color states by N-ality (triality); this discrete classification has no continuous analog and requires discrete encoding.

**(c) Pre-Geometric Coordinates:** Topological manifolds presuppose $\mathbb{R}^n$ (via local charts). A substrate whose definition requires $\mathbb{R}^n$ cannot non-circularly produce $\mathbb{R}^n$ as emergent output. Discrete structures (finite combinatorial complexes, integer lattices) can be defined without reference to $\mathbb{R}^n$, making them suitable non-circular substrates for continuum emergence (see Derivation §6.3.1 for three independent operational arguments).

**(d) Phase Coherence Without Connection:** Parallel transport on continuous manifolds requires a connection; face-sharing polyhedra enforce phase matching purely combinatorially through shared boundary identification, without presupposing differential structure.

**Conclusion:** These four requirements—(a) avoiding presupposition, (b) discrete charge classification, (c) pre-continuum coordinates, (d) connection-free phase coherence—select **discrete** encoding as necessary among known mathematical frameworks for emergent spacetime from gauge structure, conditional on the non-circular emergence principle (§4, Lemma 0.0.0a.3). Any discrete structure with vertices (from gauge charge), faces (from phase coherence), and combinatorial coordinates satisfies all four requirements; this includes polyhedral complexes, abstract simplicial complexes, and CW complexes with appropriate cell structure. The stella octangula is itself a simplicial complex, so the polyhedral and simplicial descriptions are compatible. Causal sets and spin foams satisfy subsets of the four requirements but not all four in combination (see §3.3, §5.2 item 3). The framework selects polyhedral complexes as the specific instantiation via the geometric realization conditions GR1–GR3 (Definition 0.0.0), which is a separate step from the discrete necessity established here.

### 1.1 Symbol Table

| Symbol | Definition | Dimension/Type |
|--------|------------|----------------|
| $G$ | Gauge group (typically SU(3)) | Compact Lie group |
| $P \xrightarrow{\pi} M$ | Principal G-bundle over manifold M | Fiber bundle |
| $M$ | Base manifold (spacetime) | Smooth manifold |
| $Z_N$ | Center of SU(N); $Z_3 = \{1, \omega, \omega^2\}$ for SU(3) | Finite cyclic group |
| $\omega$ | $e^{2\pi i/3}$ (primitive cube root of unity) | Complex number |
| $\Lambda_{\text{FCC}}$ | Face-centered cubic lattice | Discrete point set |
| $(n_1, n_2, n_3)$ | FCC lattice coordinates | Integer triple |
| $\mathcal{P}$ | Polyhedral complex (stella octangula units) | Abstract simplicial complex |
| $\partial F$ | Shared face between adjacent polyhedra | 2-simplex (triangle) |
| $(\phi_R, \phi_G, \phi_B)$ | Color field phases $(0, 2\pi/3, 4\pi/3)$ | Angles in $[0, 2\pi)$ |
| $\Gamma_{ab}^c$ | Connection coefficients (Christoffel symbols) | Dimensionless |
| $g_{\mu\nu}$ | Emergent metric tensor | [length]² |

---

## 2. Motivation: The Bootstrap Problem

### 2.1 The Standard Approach

In conventional gauge theory, one begins with:
1. A smooth spacetime manifold $M$ (typically $\mathbb{R}^{3,1}$ or a curved Lorentzian manifold)
2. A principal fiber bundle $P \xrightarrow{G} M$ with structure group $G$
3. A connection $\omega$ on $P$ encoding the gauge field
4. Matter fields as sections of associated vector bundles

This approach is phenomenologically successful but conceptually incomplete for emergence:

**The manifold $M$ is postulated, not derived.**

If we seek to understand why spacetime has 4 dimensions, why it has Lorentzian signature, or how it emerged from a pre-geometric state, the fiber bundle formalism cannot help—it takes $M$ as given input.

### 2.2 The Emergence Requirement

The Chiral Geometrogenesis framework aims to **derive** spacetime from a pre-geometric substrate. This requires:

1. **No a priori spacetime:** The starting point must not presuppose a manifold
2. **Emergent coordinates:** Spatial labels must arise from the structure itself
3. **Emergent metric:** Distances must be derived from field dynamics
4. **Gauge structure preserved:** The SU(3) gauge symmetry must be encoded in the pre-geometric structure

### 2.3 The Central Question

> **Question:** What mathematical structure can encode gauge symmetry without presupposing the spacetime manifold?

This theorem proves that **discrete structures** (including polyhedral complexes, simplicial complexes, and similar combinatorial objects) are necessary among known mathematical structures, given the non-circular emergence principle.

---

## 3. Comparison with Alternative Approaches

### 3.1 Fiber Bundles (Why They Cannot Work for Emergence)

| Requirement | Fiber Bundle Status | Why It Fails |
|-------------|---------------------|--------------|
| No presupposed manifold | ❌ Requires base $M$ | Definition of bundle includes projection $\pi: P \to M$ |
| Pre-geometric coordinates | ❌ Uses $M$ coordinates | Local trivializations assume coordinate charts |
| Emergent metric | ❌ Connection needs metric | Gauge covariant derivative $D_\mu = \partial_\mu + A_\mu$ uses $\partial_\mu$ |
| Discrete charge | ✅ Can encode | Center $Z_N$ acts on fibers |

**Key insight:** Fiber bundles are the correct description **after** spacetime emerges, but cannot be the pre-geometric substrate **from which** spacetime emerges.

### 3.2 Lattice Gauge Theory (Partial Solution)

| Requirement | Lattice QCD Status | Assessment |
|-------------|-------------------|------------|
| No presupposed manifold | ⚠️ Uses lattice $\mathbb{Z}^4$ | Better than continuum, but still assumes structure |
| Pre-geometric coordinates | ✅ Discrete labels | Integer lattice sites |
| Emergent metric | ⚠️ Lattice spacing $a$ | Parameter, not emergent |
| Discrete charge | ✅ Group elements on links | Well-suited for SU(3) |

**Assessment:** Lattice gauge theory uses discrete structure and succeeds computationally. In standard lattice QCD, the lattice is treated as a computational regulator to be removed in the continuum limit — but this is a **choice of interpretation**, not a mathematical necessity. Nothing prevents reinterpreting the lattice as physically fundamental. The key difference from polyhedral encoding is that lattice QCD presupposes an ambient $\mathbb{Z}^4$ with a fixed lattice spacing $a$ as a parameter, whereas the polyhedral framework derives spatial structure from gauge-theoretic data (Theorem 0.0.6). This is a difference of degree rather than kind: both use discrete structures, with polyhedral encoding additionally deriving the lattice from the gauge group.

### 3.3 Loop Quantum Gravity (Different Goal)

| Requirement | LQG Status | Assessment |
|-------------|-----------|------------|
| No presupposed manifold | ✅ Spin networks | Combinatorial graphs |
| Pre-geometric coordinates | ✅ Graph labels | Node and edge labels |
| Emergent metric | ✅ From spin foam | Area and volume operators |
| Discrete charge | ⚠️ Different group | Uses $SU(2) \subset SO(3,1)$, not $SU(3)_{\text{color}}$ |

**Assessment:** LQG successfully avoids presupposing a manifold for gravitational structure, but addresses spacetime geometry (Lorentz group), not internal gauge symmetry (SU(3) color). The approaches are potentially complementary.

### 3.4 Polyhedral Encoding (This Framework)

| Requirement | Polyhedral Status | How It Succeeds |
|-------------|-------------------|-----------------|
| No presupposed manifold | ✅ Combinatorial | Vertices, edges, faces as abstract sets |
| Pre-geometric coordinates | ✅ FCC lattice | Integer labels $(n_1, n_2, n_3)$ |
| Emergent metric | ✅ From correlators | Theorem 5.2.1 derives $g_{\mu\nu}$ |
| Discrete charge | ✅ Vertex labels | Weight correspondence (GR1) |

### 3.5 Smooth Manifold Realizations (Why They Don't Undermine Polyhedral Necessity)

> **Adversarial finding A1.5 (DENTED):** The G1 adversarial stress-test constructed explicit smooth manifold realizations of SU(3), demonstrating that SU(3) gauge theory can be formulated on smooth manifolds. This is not in dispute — it is standard QCD.

The following smooth manifolds carry natural SU(3) actions:

| Manifold | Real Dim | SU(3) Action | Emergence Status |
|----------|:--------:|--------------|------------------|
| SU(3)/T² (flag manifold) | 4 | Transitive (left multiplication) | ❌ Presupposes smooth structure |
| ℂP² | 4 | Non-transitive | ❌ Presupposes smooth structure |
| Gr(3,3) | 18 | Transitive | ❌ Far too large; presupposes smooth structure |

**Reformulated GR1–GR3 on smooth manifolds:** One can replace "vertex → weight" with "fixed point → weight" using the Borel fixed-point theorem. The flag manifold SU(3)/T² has 6 T²-fixed points corresponding to the 6 non-zero SU(3) weights. However:
- No apex analog exists (no zero-weight fixed point)
- This is standard algebraic geometry, not a polyhedral construction
- The smooth manifold itself presupposes the continuum

**Why this does not undermine Theorem 0.0.0a:**

The polyhedral necessity claim is **not** that SU(3) gauge theory cannot be formulated on smooth manifolds — it obviously can, and this is how standard QCD works. The claim is that smooth manifolds cannot serve as the **pre-geometric substrate from which spacetime emerges**, because:

1. **Circularity:** Smooth manifolds presuppose the continuum structure ($\mathbb{R}^n$ local charts) that the framework aims to derive (Lemma 0.0.0a.1, 0.0.0a.3)
2. **No pre-geometric coordinates:** SU(3)/T² has no integer lattice structure; its coordinates are smooth functions, not combinatorial data
3. **Connection-dependent phase coherence:** Gauge transport on SU(3)/T² requires a connection 1-form, which presupposes differential structure (Lemma 0.0.0a.4)

**Scope clarification:** Polyhedral necessity is a statement about **what is required for emergence** — deriving spacetime from pre-geometric structure — not about what is mathematically possible for gauge theories in general.

[→ Detailed argument in Derivation file §9.7](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#97-objection-smooth-manifolds-realize-su3-without-polyhedra)

### 3.6 Formal Framework Justifications (Lean 4)

Each framework assessment in the Lean formalization is backed by explicit justification theorems with literature citations:

| Framework | Justification Theorem | Key Reference |
|-----------|----------------------|---------------|
| Fiber Bundle | `fiberBundle_assessment_justified` | Nakahara (2003) Ch. 9, Def 9.1 |
| Lattice Gauge | `latticeGauge_assessment_justified` | Wilson (1974), Creutz (1983) |
| Polyhedral Complex | `polyhedralComplex_assessment_justified` | This framework |
| Spin Foam | `spinFoam_assessment_justified` | Rovelli (2004), Perez (2013) |
| Causal Set | `causalSet_assessment_justified` | Bombelli et al. (1987), Sorkin (2003) |

These theorems verify that `assessFramework` returns the correct `EmergenceRequirements` for each framework, based on the mathematical/physical properties documented in the literature.

---

## 4. The Four Lemmas (Summary)

The proof of Theorem 0.0.0a proceeds through four lemmas, each addressing one requirement:

### Lemma 0.0.0a.1 (Fiber Bundles Presuppose Spacetime)

**Statement:** A principal G-bundle $P \xrightarrow{\pi} M$ requires the base manifold $M$ as structural input; it cannot derive the spacetime it presupposes.

**Key argument:** The bundle projection $\pi: P \to M$ is part of the defining data. Without $M$, the concept of "bundle over" is undefined.

[→ Full proof in Derivation file §6.1](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#61-lemma-00a1-fiber-bundles-presuppose-spacetime)

### Lemma 0.0.0a.2 (Discrete Charge from Confinement)

**Statement:** The Z₃ center of SU(3) classifies hadron states by N-ality (triality): $\{0, 1, 2\} \mod 3$. This discrete classification has no continuous analog and requires discrete geometric encoding.

**Key argument:** N-ality is conserved exactly (not approximately) and takes only 3 values. A continuous encoding would introduce spurious states.

[→ Full proof in Derivation file §6.2](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#62-lemma-00a2-discrete-charge-from-confinement)

### Lemma 0.0.0a.3 (Pre-Geometric Coordinates Require Discreteness)

**Statement:** Topological manifolds presuppose $\mathbb{R}^n$ for their definition (via local charts). A substrate whose definition requires $\mathbb{R}^n$ cannot non-circularly produce $\mathbb{R}^n$ as emergent output. Only discrete structures can serve as non-circular substrates for continuum emergence.

**Key argument:** The core case rests on three independent operational arguments (see Derivation §6.3.1), not on interpreting the $\mathbb{N} \to \mathbb{R}$ construction hierarchy as ontological precedence:

1. **Specification problem (operational):** A substrate whose definition requires $\mathbb{R}^n$ cannot produce $\mathbb{R}^n$ as emergent output without circularity. Polyhedral complexes are specified by finite combinatorial data; manifolds require $\mathbb{R}^n$ in their definition.
2. **Finite information content:** A discrete substrate with finitely many sites has finite total information; the continuum emerges as an effective description in the thermodynamic limit.
3. **Definability without ambient space:** Polyhedral complexes can be defined as abstract combinatorial objects with no reference to $\mathbb{R}^n$; manifolds cannot.

**Methodological note:** The "non-circular emergence" criterion is a **methodological principle** adopted by this framework, not a universally accepted mathematical requirement. Some physical theories successfully derive structures from substrates that formally contain those same structures (e.g., statistical mechanics derives thermodynamics from Hamiltonian mechanics on phase space). The non-circularity requirement is strongest when the goal is ontological emergence (deriving $\mathbb{R}^n$ as a new entity) rather than epistemic emergence (deriving effective descriptions). This framework adopts the stronger ontological reading as a design choice.

**Lean formalization:** `lemma_0_0_0a_3_pregeometric_discrete` proves:
1. FCC lattice coordinates exist without presupposing $\mathbb{R}^n$
2. $\mathbb{Z}$ does not require $\mathbb{R}$ for its definition (definitional independence)

[→ Full proof in Derivation file §6.3](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#63-lemma-00a3-pre-geometric-coordinates-require-discreteness) | [→ Strengthened arguments §6.3.1](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#631-strengthened-argument-the-specification-problem)

### Lemma 0.0.0a.4 (Phase Coherence Without Metric)

**Statement:** Parallel transport on smooth manifolds requires either a metric (for gravitational transport via Christoffel symbols) or manifold structure (for gauge transport via connection 1-forms). Face-sharing polyhedral tilings enforce phase matching purely combinatorially: fields on a shared face $F$ must agree by definition of "shared," without presupposing any differential structure.

**Key argument:** Gravitational parallel transport uses the Levi-Civita connection (requires metric). Gauge parallel transport uses connection 1-forms (requires manifold structure with smooth paths). Both presuppose spacetime. Shared faces provide direct identification without transport equations or manifold structure.

[→ Full proof in Derivation file §6.4](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#64-lemma-00a4-phase-coherence-without-metric)

### Critical Clarification: Why Polyhedral Structure Requires the Combination of Lemmas

Finiteness of geometric elements (from Lemma 0.0.0a.2) does not by itself require polyhedral structure — finitely many points could exist in a continuous space without that space being polyhedral. Conversely, face-sharing (from Lemma 0.0.0a.4) does not by itself require discreteness — continuous CW-complexes also have face-sharing cells.

**Polyhedral necessity emerges from the conjunction:** finite vertices (from discrete charge classification) organized into cells with shared 2-dimensional faces (from connection-free phase coherence), using pre-continuum coordinates (from emergence requirements), independently of any base manifold (from fiber bundle insufficiency). No single lemma forces polyhedral structure; all four acting together do. [→ See Derivation §7.2 for detailed analysis](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md#72-conclusion)

---

## 5. What This Theorem Does and Does Not Claim

### 5.1 What We Claim

1. **Necessity among known frameworks:** Among known mathematical frameworks for encoding gauge structure, discrete encoding is **necessary** for emergent spacetime (given the non-circular emergence principle). Polyhedral complexes are a specific class of discrete structures satisfying all four requirements; other discrete structures with vertices and faces (simplicial complexes, CW complexes) also satisfy them. We do not claim absolute necessity (which would require proving no other framework could ever work), but necessity given current mathematical knowledge and the non-circularity methodological principle.

2. **Conceptual, not dynamical:** We prove that the **conceptual structure** of emergent spacetime requires discreteness; we do not derive dynamical confinement.

3. **Complementarity, not replacement:** Fiber bundles remain correct for describing physics **after** spacetime emerges; polyhedral encoding describes the pre-geometric substrate.

4. **SU(3) specific:** The argument uses SU(3) properties (Z₃ center, rank 2); extension to other groups is addressed but not the main focus.

### 5.2 What We Do NOT Claim

1. ~~Fiber bundles are "wrong" for QCD~~ ✗ — They are correct for continuum dynamics

2. ~~This theorem derives confinement~~ ✗ — Confinement is dynamical; we use it as input (via Lemma 0.0.0f)

3. ~~Other discrete approaches are excluded~~ ✗ — Lattice QCD, spin foams, causal sets, etc. are compatible; we claim necessity of **some** discrete structure

4. ~~The polyhedral approach is complete~~ ✗ — It provides the pre-geometric stage; full physics requires the dynamical framework of Phases 1-5

5. ~~No future mathematical framework could work~~ ✗ — Our claim is relative to known frameworks; future mathematics might reveal alternatives

6. ~~SU(3) gauge theory requires polyhedral structure~~ ✗ — Standard QCD on smooth spacetime is well-formulated and correct; smooth manifolds like SU(3)/T² carry natural SU(3) actions. Polyhedral necessity applies specifically to the pre-geometric emergence context, not to gauge theory in general (see §3.5)

### 5.3 Relation to Theorem 0.0.0

Theorem 0.0.0 establishes **what** conditions (GR1-GR3) a geometric realization must satisfy. Theorem 0.0.0a establishes **why** any realization must be discrete (and why polyhedral complexes are a natural class of discrete structures meeting all four requirements).

The logical relationship:
```
Theorem 0.0.0a (Why polyhedral?)
         ↓
Theorem 0.0.0 (GR1-GR3 from first principles)
         ↓
Definition 0.0.0 (Formal definition of geometric realization)
         ↓
Theorem 0.0.3 (Stella octangula is the unique realization)
```

### 5.4 Uniqueness and Edge Structure (Lean 4)

The Lean formalization includes strengthened uniqueness theorems:

1. **`discrete_gauge_phase_implies_polyhedral`**: Given discrete coordinates, gauge encoding, and phase coherence, a polyhedral complex exists with:
   - Vertices from gauge structure
   - Faces from phase coherent structure
   - **Edges derived from faces** (not empty)

2. **`polyhedral_has_edges_from_faces`**: If faces exist with ≥3 vertices, edges are non-empty.

3. **`polyhedral_is_unique_satisfying_structure`**: Any structure satisfying all three requirements IS a polyhedral complex (has faces with ≥3 vertices).

4. **Alternative structures ruled out**:
   - `graphs_insufficient_for_phase_coherence`: Graphs (edges only) cannot support phase coherence
   - `point_clouds_insufficient`: Point clouds (no boundaries) cannot define adjacency

---

## 6. References

### Primary

1. **Georgi, H.** (1982). *Lie Algebras in Particle Physics*. Benjamin/Cummings. — Standard reference for SU(3) representation theory and weight diagrams.

2. **Nakahara, M.** (2003). *Geometry, Topology and Physics*, 2nd ed. IOP Publishing. — Fiber bundle formalism and gauge theories.

3. **Conway, J.H., Jiao, Y., & Torquato, S.** (2011). "New family of tilings of three-dimensional Euclidean space by tetrahedra and octahedra." *Proc. Natl. Acad. Sci. USA* 108, 11009. — Constraints on polyhedral tilings.

4. **Rovelli, C.** (2004). *Quantum Gravity*. Cambridge University Press. — Loop quantum gravity approach to pre-geometric structure.

5. **Greensite, J.** (2011). "An Introduction to the Confinement Problem." *Lecture Notes in Physics* 821. Springer. 2nd ed. (2020) available. — Confinement physics and N-ality.

6. **'t Hooft, G.** (1978). "On the Phase Transition Towards Permanent Quark Confinement." *Nucl. Phys. B* 138, 1-25. — Center symmetry in gauge theories.

### Discrete Spacetime Approaches

7. **Bombelli, L., Lee, J., Meyer, D., & Sorkin, R.D.** (1987). "Space-time as a causal set." *Phys. Rev. Lett.* 59, 521-524. — Foundational causal set paper.

8. **Sorkin, R.D.** (1991). "Spacetime and causal sets." In *Relativity and Gravitation: Classical and Quantum* (Proc. SILARG VII). — Causal set program overview.

9. **Sorkin, R.D.** (2003). "Causal Sets: Discrete Gravity." *arXiv:gr-qc/0309009*. — Comprehensive causal set review with philosophical motivation.

10. **Dowker, F.** (2006). "Causal sets as discrete spacetime." *Contemporary Physics* 47, 1-9. — Modern review of causal sets.

11. **Smolin, L.** (2003). "How far are we from the quantum theory of gravity?" *arXiv:hep-th/0303185*. — Discrete approaches to quantum gravity.

12. **Perez, A.** (2013). "The Spin Foam Approach to Quantum Gravity." *Living Rev. Relativity* 16, 3. — Comprehensive review of spin foam models.

### Framework Documents

13. **Definition 0.0.0** (Minimal Geometric Realization) — Formal criteria GR1-GR3

14. **Theorem 0.0.3** (Stella Uniqueness) — Proves stella octangula is the unique realization

15. **Theorem 0.0.6** (Spatial Extension from Honeycomb) — FCC lattice provides pre-geometric coordinates

16. **Theorem 0.0.10** (Framework Derives GR+QM) — Closes the logical loop with Theorem 0.0.1

### Notation Conventions

See [notation-glossary.md](../reference/notation-glossary.md) for complete notation conventions used throughout this proof.

---

## Navigation

**Continue to:**
- [→ Complete Derivation (§6-9)](./Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md)
- [→ Applications and Verification (§10-14)](./Theorem-0.0.0a-Polyhedral-Necessity-Applications.md)

**Return to:**
- [← Mathematical Proof Plan](../../Mathematical-Proof-Plan.md)
- [← Definition 0.0.0](./Definition-0.0.0-Minimal-Geometric-Realization.md)
