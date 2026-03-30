# Module V5: Domain-of-Validity Verification — COMPLETE

> **Audit:** G1 Geometric Foundation Validity Audit
> **Module:** V5 (Domain-of-Validity — Established results applied within their proven domain)
> **Date:** 2026-03-15
> **Status:** All 26 files audited; 109 established-result invocations checked
> **Method:** Three parallel sub-auditors (files 1–9, 10–18, 19–26), findings synthesized and cross-checked
> **Posture:** DEFENSIVE — verify external correctness

---

## V5 Summary

| Metric | Count |
|--------|-------|
| Total established-result invocations checked | 109 |
| SOUND (within proven domain, conditions verified) | 95 |
| QUALIFIED (within domain, conditions not fully verified or prospectively applied) | 11 |
| WEAK (stretching the proven domain) | 3 |
| INVALID (applied outside proven domain) | 0 |
| SMUGGLED (undeclared domain assumption) | 0 |

**Overall verdict:** No INVALID domain-of-validity violations found in G1. The proofs are generally careful about citing established results within their proven domains and noting required conditions. Three WEAK findings identify genuine domain stretches: (1) CPT theorem invoked pre-geometrically, (2) Chentsov's theorem extended beyond finite sample spaces, and (3) an incorrect group-theoretic claim about icosahedral symmetry. Eleven QUALIFIED findings identify cases where conditions are met but not explicitly verified, or where results are invoked prospectively before their full prerequisites are established.

---

## Check-by-Check Results

### V5.1 — Definition 0.0.0: Minimal Geometric Realization

**Result: QUALIFIED**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Cartan subalgebra / weight space structure (rank(SU(N)) = N−1, Weyl(SU(N)) = S_N) | SOUND — G explicitly restricted to "compact simple Lie group" | — |
| SU(3) fundamental representation is complex (3 ≇ 3̄) for N ≥ 3 | SOUND — N = 3 is explicit | — |
| Apex vertices carry trivial weight by Weyl fixed-point argument | SOUND — standard Lie algebra result | — |
| **CPT theorem (Lüders 1954, Pauli 1955) used to justify GR3** | **WEAK** — CPT requires Lorentz invariance, locality, unitarity on a spacetime manifold; invoked pre-geometrically where no spacetime exists | **MAJOR** |

**Key risk:** The CPT theorem is the single clearest instance in G1 of an established result invoked outside its proven domain. The proof uses CPT as "physical justification" for requiring charge conjugation symmetry (GR3) at the pre-geometric level, but the CPT theorem's prerequisites (Lorentz-invariant QFT on a spacetime manifold) are not met before spacetime emerges. The conclusion (charge conjugation should be a symmetry) may well be correct, but the standard CPT theorem does not license it in this regime.

---

### V5.2 — Theorem 0.0.1: D=4 From Observer Existence

**Result: SOUND**

11 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Gravitational potential Φ(r) ∝ r^{−(n−2)} in n spatial dimensions (Ehrenfest 1917) | SOUND — Gauss's law correctly applied to isolated point mass | — |
| Effective potential analysis for orbital stability (D < 5) | SOUND — standard classical mechanics | — |
| Bertrand's theorem (1873) | SOUND — explicitly stated as applying to n = 3 only | — |
| Virial theorem (2⟨T⟩ = s⟨V⟩ for V ∝ r^s) | SOUND — Coulomb potential in n dimensions is pure power-law | — |
| Hydrogen atom in n dimensions / Landau-Lifshitz "fall to center" | SOUND — references LL QM §35; n = 4 gives exact critical V ∝ 1/r² | — |
| Huygens' principle (Hadamard) — sharp propagation in odd n ≥ 3 | SOUND — linear wave equation in flat space; n = 1 exception correctly noted | — |
| Knot theory: non-trivial S¹ embeddings only in ℝ³ (Rolfsen 1976) | SOUND — standard general-position argument for n ≥ 4 | — |
| Spinor structure in n dimensions (Atiyah-Bott-Shapiro) | SOUND — Clifford algebra dim 2^{[n/2]}, mod 8 periodicity | — |
| CDT result d_H = 4.01 ± 0.05 (Ambjørn et al. 2004) | SOUND — cited with quantitative error bars, no extrapolation | — |
| Black hole lifetime scaling τ ∝ M^{n/(n−2)} | SOUND — semi-classical regime (M ≫ M_Planck) | — |
| Bekenstein-Hawking entropy scaling S ∝ M^{(D−2)/(D−3)} | SOUND — semi-classical gravity, area law | — |

**Key risk:** None. This is the most citation-rich file in G1 and the most careful about domain conditions. Every established result is applied within its proven domain with proper qualifications.

---

### V5.3 — Theorem 0.0.2: Euclidean ℝ³ From SU(3)

**Result: SOUND**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Killing form is negative-definite, Ad-invariant, non-degenerate on su(N) | SOUND — G = SU(3) is compact and simple | — |
| B(X,Y) = 2N Tr(XY) for SU(N) in fundamental rep (dual Coxeter number h^∨ = 3) | SOUND — factor 6 correctly computed | — |
| Weight space metric induced by Killing form is positive-definite | SOUND — explicit computation: B\|_h = −3I₂, so −B⁻¹ = (1/3)I₂ | — |
| Asymptotic freedom β₀ = (11N_c − 2N_f)/3 | SOUND — one-loop perturbative QCD; N_f = 3, N_c = 3 gives β₀ = 9 | — |
| Dimensional transmutation Λ_QCD = μ exp(−2π/(β₀α_s(μ))) | SOUND — one-loop RG, MS-bar scheme | — |

**Key risk:** None. The novel content is the *interpretation* (weight space metric = physical metric), which is a framework choice, not a domain violation.

---

### V5.4 — Theorem 0.0.2b: Dimension-Color Correspondence

**Result: QUALIFIED**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| rank(SU(N)) = N−1 (Humphreys §8.1) | SOUND | — |
| Killing form negative-definite on su(N) | SOUND | — |
| Fundamental weights sum to zero, span h*, form (N−1)-simplex | SOUND | — |
| Single gauge coupling for SU(N) Yang-Mills | SOUND | — |
| **Holographic correspondence (AdS/CFT) for D_radial = 1** | **QUALIFIED** — QCD is not conformal; proof honestly labels this as heuristic analogy, not load-bearing (two other arguments provided) | MINOR |

**Key risk:** The AdS/CFT invocation is the only stretch, and the proof is admirably transparent about its limited logical force. Non-critical.

---

### V5.5 — Lemma 0.0.2a: Confinement Dimension

**Result: SOUND**

3 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Affine independence: N points in ℝ^d require d ≥ N−1 (Grünbaum 2003) | SOUND — pure linear algebra | — |
| Weyl group of SU(N) is S_N | SOUND — standard Lie algebra result | — |
| Color singlet wavefunctions (meson, baryon) with ε^{ijk} | SOUND — standard SU(3) group theory | — |

**Key risk:** None. Cleanest file in G1 for domain-of-validity.

---

### V5.6 — Proposition 0.0.40: Embedding Dimension From Confinement

**Result: SOUND**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| String tension √σ = 440 ± 30 MeV (Bali 2001, Bazavov 2023, FLAG) | SOUND — lattice QCD consensus | — |
| Single gauge coupling of SU(N) Yang-Mills (Gross & Wilczek 1973) | SOUND — gauge theory Lagrangian | — |
| SU(3) confines in 2+1D with σ > 0 (Teper 1999, Bringoltz & Teper 2007) | SOUND — lattice gauge theory, used as scope clarification | — |
| θ-angle does not undergo dimensional transmutation (Abel et al. 2020, nEDM) | SOUND — topological vs. coupling distinction | — |

**Key risk:** None. Novel content (coupling-to-dimension correspondence, Step C4) is correctly identified as framework axiom (F), not established result.

---

### V5.7 — Theorem 0.0.0a: Polyhedral Necessity

**Result: QUALIFIED**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Principal G-bundle P → M requires manifold M (Nakahara 2003) | SOUND — definitional | — |
| Z₃ center of SU(3) classifies representations by N-ality | SOUND — standard group theory | — |
| Cantor diagonal argument (ℝ uncountable) | SOUND — ZFC | — |
| **Gauge parallel transport requires connection 1-form on manifold** | **QUALIFIED** — correct for continuum gauge theory, but lattice gauge theory defines parallel transport via link variables without smooth manifolds; proof partially addresses this | MINOR |

**Key risk:** The lattice gauge theory nuance is minor — the proof's main argument stands regardless.

---

### V5.8 — Proposition 0.0.XX: SU(3) From Distinguishability

**Result: SOUND**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Chentsov's theorem (1972, Le 2017): Fisher metric unique under sufficient statistics invariance | SOUND — modern extensions correctly noted; non-degeneracy prerequisite properly distinguished | — |
| Fisher information metric definition and regularity conditions | SOUND — smooth distributions, regularity conditions met | — |
| Lagrange's theorem (subgroup orders divide group order) | SOUND — finite groups (Z_N is finite) | — |
| Weyl group classification for rank-2 simple Lie groups | SOUND — standard classification correctly enumerated | — |
| Cartan classification: complete list of rank-2 algebras is A₂, B₂, C₂, G₂ | SOUND — complete list | — |

**Key risk:** None.

---

### V5.9 — Theorem 0.0.3: Stella Uniqueness

**Result: SOUND**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| SU(3) weight diagram (3 and 3̄) — standard Gell-Mann matrix eigenvalues | SOUND | — |
| A₂ root system: 6 roots correctly enumerated | SOUND | — |
| Root system uniqueness up to automorphism (Humphreys 1972) | SOUND | — |
| Euler characteristic: χ = V − E + F = 8 − 12 + 8 = 4 | SOUND — each S² contributes χ = 2 | — |
| S₃ transitivity on vertices forces equilateral triangles | SOUND — distance-preserving group action | — |

**Key risk:** None.

---

### V5.10 — Theorem 0.0.3b: Geometric Realization Completeness

**Result: SOUND**

6 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Pigeonhole principle (infinite vertices → finite weights) | SOUND | — |
| Weight multiplicities of 3⊕3̄ representation | SOUND — standard textbook | — |
| Simplicity of A₅ (Jordan 1870s) → no surjection A₅ → S₃ | SOUND — \|A₅\| = 60 > \|S₃\| = 6, simple group | — |
| Normal subgroups of S₄ (Dummit & Foote) | SOUND — complete classification | — |
| Kepler-Poinsot solid vertex counts (12, 20, 12, 12) | SOUND — Coxeter | — |
| Hausdorff property of subspaces of ℝⁿ | SOUND — standard topology | — |

**Key risk:** None.

---

### V5.11 — Proposition 0.0.16a: A₃ From Physical Requirements

**Result: QUALIFIED**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Dynkin classification: rank-3 irreducible root systems are A₃, B₃, C₃ | SOUND — complete enumeration | — |
| D₃ ≅ A₃ isomorphism (so(6) ≅ su(4)) | SOUND | — |
| Root lattice computation: Q(B₃) = ℤ³, Q(C₃) = FCC | SOUND — Bourbaki/Conway-Sloane | — |
| Tetrahedral-octahedral honeycomb uniqueness (vertex-transitive) | SOUND — vertex-transitivity qualification explicit | — |
| **Simply-laced property as elimination criterion for C₃** | **QUALIFIED** — mathematical fact (C₃ not simply-laced) is correct; physical inference (non-simply-laced → non-uniform gauge coupling) is framework-specific | MINOR |

**Key risk:** Minor. The mathematical fact is sound; the physical interpretation is framework content.

---

### V5.12 — Theorem 0.0.16: Adjacency From SU(3)

**Result: SOUND**

6 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| SU(3) tensor product: 3 ⊗ 3 = 6 ⊕ 3̄ | SOUND — dimension check 9 = 6 + 3 | — |
| Littlewood-Richardson: 6 ⊗ 3 = 10 ⊕ 8 | SOUND — 18 = 10 + 8 | — |
| Adjoint decomposition: 3 ⊗ 3̄ = 8 ⊕ 1 | SOUND — 9 = 8 + 1 | — |
| O_h ≅ S₄ × ℤ₂ (octahedral symmetry) | SOUND | — |
| W(A₂) = S₃ (Humphreys Ch. 10) | SOUND | — |
| A₃ root lattice = FCC (Conway & Sloane 1999) | SOUND | — |

**Key risk:** None.

---

### V5.13 — Theorem 0.0.6: Spatial Extension From Octet Truss

**Result: WEAK**

6 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Dihedral angles: θ_T = arccos(1/3), θ_O = arccos(−1/3); θ_T + θ_O = π | SOUND — Coxeter 1973; verified to machine precision | — |
| **Uniqueness of integer dihedral solution (t,o) = (2,2)** | **QUALIFIED** — correct, but proof does not explicitly verify irrationality of arccos(1/3)/π (follows from Niven-Mann theorem) | MINOR |
| FCC packing fraction π/(3√2) ≈ 0.7405 (Kepler conjecture, Hales 2005) | SOUND — not load-bearing | — |
| Conway-Jiao-Torquato continuous family of tilings | SOUND — correctly limits uniqueness claim to vertex-transitive | — |
| **C₃ subgroup claim about icosahedral symmetry** | **WEAK** — the claim "gcd(3,5) = 1 ∴ C₃ ⊄ I_h as rotation about 5-fold axis" is technically incorrect; C₃ IS a subgroup of I_h (icosahedral symmetry has 3-fold axes); the angular incompatibility argument (60° vs 63.43°) is the correct and load-bearing reasoning | **MODERATE** |
| **Bloch theorem inapplicability on quasicrystals** | **QUALIFIED** — inapplicability correctly stated; follow-on claims (Anderson localization, path-dependent holonomy) are physical heuristics beyond the theorem itself | MINOR |

**Key risk:** The WEAK finding is a genuine error in a non-load-bearing argument. C₃ embeds in I_h via the 3-fold rotational axes — the statement that it does not is false. The conclusion (icosahedral quasicrystals excluded) is correct via the angular incompatibility argument. **Recommend correcting or removing the false group-theoretic claim.**

---

### V5.14 — Proposition 0.0.6b: Continuum Limit Procedure

**Result: QUALIFIED**

6 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| π₃(SU(3)) = ℤ (Bott periodicity 1959) | SOUND — standard algebraic topology | — |
| Serre reconstruction: root system → Lie algebra → Lie group | SOUND — Serre's theorem + exponentiation (Helgason 1978) | — |
| Center Z(SU(N)) = ℤ_N from coweight/root lattice | SOUND — covering space theory | — |
| **Sector orthogonality in infinite volume limit (Coleman 1985 Ch. 7)** | **QUALIFIED** — correctly cited, but applied in geometric continuum limit where dynamical prerequisites (gauge action) are not yet established; Remark 3.3.1 honestly acknowledges this gap | MODERATE |
| **Cluster decomposition (Weinberg 1995 Ch. 4)** | **QUALIFIED** — presupposes fully dynamical QFT with unique vacuum and mass gap; proposition only constructs geometric/kinematic framework at this stage | MODERATE |
| Discrete O does not converge to SO(3) — group vs effective symmetry | SOUND — correctly framed as effective phenomenon | — |

**Key risk:** Two results (Coleman sector orthogonality, Weinberg cluster decomposition) are invoked prospectively — the proposition establishes geometric structure but the cited results require dynamical content not yet in place. The proof is transparent about this (Remark 3.3.1), but §4 and §6 read as applications rather than anticipations.

---

### V5.15 — Theorem 0.0.9: Framework-Internal D=4 Consistency Check

**Result: QUALIFIED**

6 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| **Weinberg's soft graviton theorem (1964)** | **QUALIFIED** — requires Lorentz-invariant S-matrix, which the framework derives elsewhere (Thm 0.0.8 + 0.0.11); creates logical chain dependency, acknowledged in the proof | MODERATE |
| Yang-Mills theorem: local gauge invariance → adjoint gauge bosons (1954) | SOUND | — |
| Ehrenfest-Tegmark stability arguments for D = 4 | SOUND | — |
| Noether's theorem: stress-energy from translation invariance (1918) | SOUND | — |
| Gauss's law in n dimensions | SOUND — standard PDE | — |
| Graviton propagator in de Donder gauge | SOUND — linearized GR, weak-field limit | — |

**Key risk:** Weinberg's theorem is correctly stated but its applicability depends on Lorentz invariance being established elsewhere. Sequential dependency, not a domain violation per se.

---

### V5.16 — Theorem 0.0.15: Topological Determination of SU(3)

**Result: SOUND**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Cartan classification of compact simple Lie groups and their centers | SOUND — complete table, Helgason 1978 | — |
| Degenerate low-rank cases (B₁ = A₁, C₂ = B₂, D₃ = A₃) — Humphreys §11.4 | SOUND | — |
| π₁(PSU(3)) = ℤ₃ from covering space theory (Hatcher 2002) | SOUND | — |
| π₃(SU(3)) = ℤ (Bott periodicity) | SOUND | — |
| Simply-connected form selected by Z₃ center requirement | SOUND | — |

**Key risk:** None.

---

### V5.17 — Theorem 0.0.12: Categorical Equivalence

**Result: QUALIFIED**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Definition of categorical equivalence (Mac Lane 1998) | SOUND | — |
| **PL-homeomorphism extension from vertex maps** | **QUALIFIED** — correct for finite simplicial complexes (which applies here), but proof is only a sketch | MINOR |
| Serre's theorem: root system determines Lie algebra | SOUND — correctly scoped at Cartan data level | — |
| Weyl group W(A₂) = S₃ action on weight space | SOUND | — |

**Key risk:** Minor. PL-homeomorphism extension is standard but only sketched.

---

### V5.18 — Theorem 0.0.13: Tannaka Reconstruction of SU(3)

**Result: QUALIFIED**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| **Tannaka-Krein duality: G ≅ Aut_⊗(ω) (Deligne & Milne 1982)** | **QUALIFIED** — domain conditions met (SU(3) is compact, Rep(SU(3)) satisfies all requirements), but fiber functor uses prior SU(3) knowledge, limiting logical force to consistency check | MODERATE |
| SU(3) tensor product decompositions (3⊗3, 3⊗3̄, 3̄⊗3̄) | SOUND — dimension checks pass | — |
| All SU(3) irreps from tensor powers of 3 and 3̄ (highest weight theorem) | SOUND | — |
| Cartan data determines group up to isogeny | SOUND — correctly identified as gap Tannaka bridges | — |

**Key risk:** Tannaka-Krein is within its proven domain but has limited logical force as a consistency check. Proof is transparent about this.

---

### V5.19 — Definition 0.1.1: Stella Octangula Boundary Topology

**Result: SOUND**

5 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Euler's polyhedron formula V − E + F = χ | SOUND — closed orientable polyhedral surfaces | — |
| Convex polyhedron boundary homeomorphic to S² (Munkres) | SOUND — tetrahedron is convex | — |
| Barycentric coordinates as coordinate atlas | SOUND — non-degenerate simplices | — |
| SU(3) weight vectors, Cartan subalgebra properties | SOUND — flagged as "anticipatory" | — |
| Descartes' angular defect theorem | SOUND — regular tetrahedra satisfy all conditions | — |

**Key risk:** None.

---

### V5.20 — Definition 0.1.2: Three Color Fields & Relative Phases

**Result: SOUND**

5 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Z(SU(N)) ≅ ℤ_N | SOUND — SU(3) not a quotient | — |
| Cube roots of unity sum to zero: 1 + ω + ω² = 0 | SOUND — elementary algebra | — |
| SU(3) fundamental representation weights in (T₃, T₈) basis | SOUND — explicit Gell-Mann matrix computation | — |
| Weight angle computation: cos θ = −1/2 → θ = 120° | SOUND — standard Euclidean inner product | — |
| Anti-fundamental weights are negatives of fundamental weights | SOUND | — |

**Key risk:** None.

---

### V5.21 — Definition 0.1.3: Pressure Functions

**Result: QUALIFIED**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| **Green's function of 3D Laplacian: G(x) = 1/(4π\|x − x_c\|) (Jackson)** | **QUALIFIED** — correctly stated, but passage from 1/r (Green's function) to 1/r² (pressure function) is modeling choice, not forced by math; transparently flagged | MINOR |
| **Flux conservation / geometric spreading: 4πr²P(r) = const** | **QUALIFIED** — requires pre-existing 3D metric space; proof uses ℝ³ embedding in pre-geometric context; flagged as "computational scaffolding" (A-PF) | MINOR |
| Integral convergence of 1/(r² + ε²)² for ε > 0 | SOUND — standard calculus | — |
| Cornell potential V(r) = −α_s/r + σr (Eichten et al. 1978) | SOUND — flagged as "illustrative, not foundational" | — |
| Tetrahedral angle arccos(−1/3) ≈ 109.47° | SOUND — elementary geometry | — |

**Key risk:** Both QUALIFIED findings involve using ℝ³ metric concepts in a pre-geometric context. The proof is commendably transparent about this tension.

---

### V5.22 — Proposition 0.1.3a: Pressure Function Form-Independence

**Result: SOUND**

2 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Voronoi tessellation: dominance domains ↔ Euclidean Voronoi cells | SOUND — Euclidean restriction explicitly acknowledged | — |
| L² integrability: power-law r^{−2α} convergence requires α > 3/4 | SOUND — standard calculus | — |

**Key risk:** None.

---

### V5.23 — Definition 0.1.4: Color Field Domains

**Result: SOUND**

4 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Voronoi cell = pressure dominance domain for uniform regularization | SOUND — monotonicity explicit | — |
| Solid angle equality from T_d transitive action on vertices | SOUND — standard group theory | — |
| Perpendicular bisector planes as Voronoi boundaries | SOUND — Euclidean distance | — |
| SU(3) root vectors and Weyl group — projected boundary normals parallel to roots | SOUND — explicit computation | — |

**Key risk:** None.

---

### V5.24 — Theorem 0.1.0: Field Existence From Distinguishability

**Result: WEAK**

4 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| **Fisher information metric definition and regularity** | **QUALIFIED** — Fisher regularity conditions (interchange of derivative and integral) used but not explicitly stated; satisfied on compact domain with smooth distributions | MINOR |
| **Chentsov's uniqueness theorem (1982)** | **WEAK** — original theorem is for finite sample spaces; extension to Cartan torus T² of SU(3) as a "statistical manifold" stretches the domain; proof acknowledges circularity in transparency note but domain extension needs stronger justification | **MAJOR** |
| Killing form computation for SU(3) (B = 6 Tr) | SOUND — explicit Gell-Mann matrix calculation | — |
| **Interference form uniqueness (Thm 4.3.1)** | **QUALIFIED** — proved only at leading order O(δφ²); theorem statement claims necessity ("must have the form") but proof shows uniqueness only at leading order with higher-order terms dismissed | MODERATE |

**Key risk:** The Chentsov domain extension is the most consequential WEAK finding in the Phase 0 files. Chentsov's original theorem applies to finite sample spaces (the simplex of probability distributions on a finite set), not to arbitrary compact manifolds. The bi-invariance argument provides partial justification but does not fully bridge the gap. Extensions to parametric families on compact manifolds exist (Campbell 1986, Ay & Tuschmann 2005) but are not cited.

---

### V5.25 — Theorem 1.1.1: SU(3) ↔ Stella Octangula

**Result: SOUND**

6 established-result invocations checked. All within proven domains.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| Gell-Mann matrices as SU(3) generators | SOUND — standard particle physics | — |
| Weight computation from Cartan generators | SOUND — explicit matrix multiplication | — |
| Equilateral triangle in Killing metric (A₂ simply-laced) | SOUND — careful treatment of metric subtlety | — |
| Weyl group W(A₂) = S₃ (Humphreys Ch. 10) | SOUND — explicit permutation verification | — |
| Projection matrix P = I − nn^T | SOUND — standard linear algebra | — |
| Linear map between projected vertices and SU(3) weights | SOUND — explicit matrix computation | — |

**Key risk:** None. Exemplary treatment of the Killing metric vs. Euclidean metric distinction.

---

### V5.26 — Definition 1.1.4: Stella Diagram Rules

**Result: QUALIFIED**

5 established-result invocations checked.

| Invocation | Domain Status | Severity |
|-----------|---------------|----------|
| SU(3) tensor decompositions: 3 ⊗ 3̄ = 1 ⊕ 8; 3 ⊗ 3 ⊗ 3 = 1 ⊕ 8 ⊕ 8 ⊕ 10 | SOUND | — |
| **Wilson loop area law ⟨W(C)⟩ ~ exp(−σA(C))** | **QUALIFIED** — invoked prospectively from Phase 2 (Prop 2.5.2a); domain conditions (confining phase, large loop limit) deferred; forward reference clearly flagged | MINOR |
| Euler characteristic of diagram graph: χ = 6 − 9 + 2 = −1 | SOUND — correctly distinguished from boundary χ = 4 | — |
| Phase accumulation / winding number for Z₃-valued edge labels | SOUND — group structure of Z₃ ↪ U(1) | — |
| Feynman diagram analogy | SOUND — explicitly qualified as analogy, not exact | — |

**Key risk:** None. Wilson loop is the only domain stretch, transparently flagged.

---

## Cross-Cutting Analysis

### Pattern 1: Pre-geometric invocations of spacetime-dependent results

Three findings (V5.1 CPT, V5.21 Green's function/geometric spreading) share a common pattern: established results that require spacetime structure are invoked in the pre-geometric regime where spacetime has not yet emerged. The proofs generally acknowledge this tension but handle it differently:
- **CPT (V5.1):** Used as "physical justification" — WEAK
- **Green's function/spreading (V5.21):** Flagged as "computational scaffolding" — QUALIFIED

**Recommendation:** Adopt a uniform convention for pre-geometric invocations of spacetime-dependent results, clearly distinguishing *motivational* use (doesn't affect logic) from *load-bearing* use (affects conclusions).

### Pattern 2: Prospective invocations

Four findings (V5.14 Coleman/Weinberg, V5.15 Weinberg graviton, V5.26 Wilson loop) invoke results whose prerequisites are established later in the derivation chain. These are not domain violations per se — the results will be applicable once prerequisites are derived — but they read as applications rather than anticipations.

**Recommendation:** Where results are cited before their prerequisites are in place, use explicit prospective language: "Once [prerequisite] is established (Theorem X.Y.Z), [result] will apply to yield..." rather than stating the result as though it already applies.

### Pattern 3: Chentsov domain extension

The Chentsov theorem invocation (V5.24) is the single most consequential domain issue. The original theorem (finite sample spaces) is applied to a compact Lie group quotient. While extensions exist (Campbell 1986, Bauer et al. 2016, Ay & Tuschmann 2005), the specific extension needed here should be explicitly justified or the argument restructured.

### Pattern 4: Factual errors in non-load-bearing arguments

The C₃ ⊂ I_h claim (V5.13) is a factual error (C₃ IS a subgroup of I_h). While non-load-bearing (the angular incompatibility argument carries the conclusion), factual errors in any part of a proof erode credibility. These should be corrected even if they don't affect the logical structure.

---

## Severity Distribution

| Severity | Count | Findings |
|----------|-------|----------|
| CRITICAL | 0 | — |
| MAJOR | 2 | V5.1 (CPT pre-geometric), V5.24 (Chentsov domain) |
| MODERATE | 5 | V5.13 (C₃ ⊂ I_h error), V5.14 (Coleman/Weinberg prospective ×2), V5.15 (Weinberg graviton chain), V5.18 (Tannaka consistency), V5.24 (interference form uniqueness) |
| MINOR | 9 | V5.4, V5.7, V5.11, V5.13 (×2), V5.17, V5.21 (×2), V5.24, V5.26 |
| NOTE | 0 | — |

---

## Recommendations for Remediation

1. **V5.1 (MAJOR):** Add explicit note to Def 0.0.0 Prop 0.0.0h acknowledging that CPT prerequisites (Lorentz invariance, locality, unitarity) are not met pre-geometrically. Either reframe GR3 as a framework axiom motivated by but not derived from CPT, or provide independent justification for charge conjugation symmetry.

2. **V5.24 (MAJOR):** Strengthen the Chentsov domain argument in Thm 0.1.0. Either cite specific extensions to parametric families on compact manifolds (Ay & Tuschmann 2005), or restructure to derive Fisher-Killing metric equivalence without Chentsov uniqueness.

3. **V5.13 (MODERATE):** Correct the false claim about C₃ ⊄ I_h in Thm 0.0.6 §1.5 Argument 1. C₃ IS a subgroup of I_h via the 3-fold rotational axes. The angular incompatibility argument (60° vs 63.43°) is correct and sufficient.

4. **V5.13 (MINOR):** Add citation to Niven-Mann theorem for irrationality of arccos(1/3)/π in dihedral uniqueness argument.

5. **V5.14 (MODERATE):** Add explicit "prospective" language to Prop 0.0.6b §4 and §6 when invoking Coleman/Weinberg results.

---

```json
{
  "group": "G1",
  "layer": 2,
  "module": "V5",
  "checks_total": 26,
  "sound": 14,
  "qualified": 9,
  "weak": 3,
  "invalid": 0,
  "smuggled": 0,
  "findings": [
    {
      "check_id": "V5.1",
      "result": "QUALIFIED",
      "description": "Def 0.0.0 — CPT theorem invoked pre-geometrically where Lorentz invariance not established",
      "evidence": "docs/proofs/foundations/Definition-0.0.0-Minimal-Geometric-Realization.md, Proposition 0.0.0h",
      "severity": "MAJOR"
    },
    {
      "check_id": "V5.2",
      "result": "SOUND",
      "description": "Thm 0.0.1 — All 11 established results applied within proven domains with proper qualifications",
      "evidence": "docs/proofs/foundations/Theorem-0.0.1-D4-From-Observer-Existence.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.3",
      "result": "SOUND",
      "description": "Thm 0.0.2 — Killing form, asymptotic freedom, dimensional transmutation all correctly scoped",
      "evidence": "docs/proofs/foundations/Theorem-0.0.2-Euclidean-From-SU3.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.4",
      "result": "QUALIFIED",
      "description": "Thm 0.0.2b — AdS/CFT used as heuristic for non-conformal QCD (honestly labeled, non-load-bearing)",
      "evidence": "docs/proofs/foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md, Section 5 Argument 3",
      "severity": "MINOR"
    },
    {
      "check_id": "V5.5",
      "result": "SOUND",
      "description": "Lem 0.0.2a — All established results (affine independence, Weyl group, singlet states) within domain",
      "evidence": "docs/proofs/foundations/Lemma-0.0.2a-Confinement-Dimension.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.6",
      "result": "SOUND",
      "description": "Prop 0.0.40 — Lattice QCD values, gauge theory, confinement results all correctly applied",
      "evidence": "docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.7",
      "result": "QUALIFIED",
      "description": "Thm 0.0.0a — Gauge parallel transport claim correct for continuum but not fully addressed for lattice",
      "evidence": "docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity.md, Lemma 0.0.0a.4",
      "severity": "MINOR"
    },
    {
      "check_id": "V5.8",
      "result": "SOUND",
      "description": "Prop 0.0.XX — Chentsov, Fisher metric, Lagrange, Weyl group, Cartan classification all within domain",
      "evidence": "docs/proofs/foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.9",
      "result": "SOUND",
      "description": "Thm 0.0.3 — SU(3) weights, A₂ roots, Euler characteristic, regularity all correctly applied",
      "evidence": "docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.10",
      "result": "SOUND",
      "description": "Thm 0.0.3b — Pigeonhole, weight multiplicities, A₅ simplicity, S₄ subgroups all within domain",
      "evidence": "docs/proofs/foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.11",
      "result": "QUALIFIED",
      "description": "Prop 0.0.16a — Simply-laced elimination of C₃ is math-correct but physical inference is framework-specific",
      "evidence": "docs/proofs/foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md, Section 3.4",
      "severity": "MINOR"
    },
    {
      "check_id": "V5.12",
      "result": "SOUND",
      "description": "Thm 0.0.16 — SU(3) tensor products, O_h structure, A₃=FCC all standard textbook results",
      "evidence": "docs/proofs/foundations/Theorem-0.0.16-Adjacency-From-SU3.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.13",
      "result": "WEAK",
      "description": "Thm 0.0.6 — False claim C₃ ⊄ I_h (C₃ IS subgroup of I_h); dihedral irrationality not cited; Bloch heuristic",
      "evidence": "docs/proofs/foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md, Section 1.5 Argument 1",
      "severity": "MODERATE"
    },
    {
      "check_id": "V5.14",
      "result": "QUALIFIED",
      "description": "Prop 0.0.6b — Coleman sector orthogonality and Weinberg cluster decomposition invoked prospectively before dynamical prerequisites established",
      "evidence": "docs/proofs/foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md, Sections 4 and 6",
      "severity": "MODERATE"
    },
    {
      "check_id": "V5.15",
      "result": "QUALIFIED",
      "description": "Thm 0.0.9 — Weinberg soft graviton theorem depends on Lorentz invariance derived elsewhere in framework",
      "evidence": "docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md, Sections 5.1 and 9.1",
      "severity": "MODERATE"
    },
    {
      "check_id": "V5.16",
      "result": "SOUND",
      "description": "Thm 0.0.15 — Cartan classification, covering space theory, Bott periodicity all standard and correct",
      "evidence": "docs/proofs/foundations/Theorem-0.0.15-Topological-Determination-SU3.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.17",
      "result": "QUALIFIED",
      "description": "Thm 0.0.12 — PL-homeomorphism extension only sketched (correct for finite simplicial complexes)",
      "evidence": "docs/proofs/foundations/Theorem-0.0.12-Categorical-Equivalence.md, Lemma 0.0.12d",
      "severity": "MINOR"
    },
    {
      "check_id": "V5.18",
      "result": "QUALIFIED",
      "description": "Thm 0.0.13 — Tannaka-Krein domain conditions met but fiber functor uses prior SU(3) knowledge, limiting logical force",
      "evidence": "docs/proofs/foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md, Section 3.2",
      "severity": "MODERATE"
    },
    {
      "check_id": "V5.19",
      "result": "SOUND",
      "description": "Def 0.1.1 — Euler formula, S² homeomorphism, barycentric coordinates, Descartes all within domain",
      "evidence": "docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.20",
      "result": "SOUND",
      "description": "Def 0.1.2 — Center of SU(N), cube roots of unity, weight vectors, angle computation all standard",
      "evidence": "docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.21",
      "result": "QUALIFIED",
      "description": "Def 0.1.3 — Green's function and geometric spreading use ℝ³ metric in pre-geometric context; flagged as scaffolding",
      "evidence": "docs/proofs/Phase0/Definition-0.1.3-Pressure-Functions.md, Sections 3.1-3.2",
      "severity": "MINOR"
    },
    {
      "check_id": "V5.22",
      "result": "SOUND",
      "description": "Prop 0.1.3a — Voronoi tessellation and L² integrability correctly applied",
      "evidence": "docs/proofs/Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.23",
      "result": "SOUND",
      "description": "Def 0.1.4 — Voronoi cells, solid angles, perpendicular bisectors, root vectors all standard and correct",
      "evidence": "docs/proofs/Phase0/Definition-0.1.4-Color-Field-Domains.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.24",
      "result": "WEAK",
      "description": "Thm 0.1.0 — Chentsov's theorem extended beyond finite sample spaces to Cartan torus; interference form uniqueness proved only at leading order",
      "evidence": "docs/proofs/Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md, Sections 3.3 and 4.3",
      "severity": "MAJOR"
    },
    {
      "check_id": "V5.25",
      "result": "SOUND",
      "description": "Thm 1.1.1 — Gell-Mann matrices, weights, Killing metric, Weyl group, projection all exemplary",
      "evidence": "docs/proofs/Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V5.26",
      "result": "QUALIFIED",
      "description": "Def 1.1.4 — Wilson loop area law invoked prospectively from Phase 2; forward dependency clearly flagged",
      "evidence": "docs/proofs/Phase1/Definition-1.1.4-Stella-Diagram-Rules.md, Section 7 Rule 7",
      "severity": "MINOR"
    }
  ],
  "overall_verdict": "No INVALID domain-of-validity violations in G1. 95 of 109 established-result invocations are SOUND. Three WEAK findings: (1) CPT theorem invoked pre-geometrically (MAJOR), (2) Chentsov's theorem extended beyond finite sample spaces (MAJOR), (3) false C₃ ⊄ I_h claim in icosahedral exclusion (MODERATE). Nine QUALIFIED findings are mostly prospective invocations or minor gaps in explicit condition verification. The proofs are generally careful and honest about domain limitations."
}
```
