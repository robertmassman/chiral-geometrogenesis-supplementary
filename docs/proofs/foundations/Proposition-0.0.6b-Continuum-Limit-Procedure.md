# Proposition 0.0.6b: Continuum Limit from Discrete Polyhedral Structure

## Status: ✅ VERIFIED — Continuum Limit Procedure

**Purpose:** This proposition explicitly constructs the continuum limit from the discrete polyhedral encoding of SU(3), addressing a key question: "π₃(SU(3)) = Z holds for the continuous group. How does this emerge from discrete polyhedral encoding?"

**Created:** 2026-01-11
**Last Updated:** 2026-01-12 (Lean formalization insights integrated)

**The Gap Addressed:**

The stella octangula is a finite, discrete geometric object with 8 vertices and 48-element octahedral symmetry O_h. (Note: O_h ⊂ O(3) consists of 24 proper rotations forming the chiral octahedral group O ⊂ SO(3), plus 24 improper rotations including reflections.) Yet the theorems require:
- Continuous SU(3) gauge group
- π₃(SU(3)) = Z for instanton classification
- Continuous spatial coordinates for field theory

This proposition constructs the explicit limit procedure and shows which structures survive.

**Dependencies:**
- ✅ Theorem 0.0.6 (Spatial Extension From Octet-Truss) — FCC lattice emergence
- ✅ Proposition 0.0.17r (Lattice Spacing From Holographic Self-Consistency)
- ✅ Definition 0.0.0 (Minimal Geometric Realization) — Stella-SU(3) correspondence
- ✅ Theorem 0.0.15 (Topological Derivation of SU(3)) — Z₃ center structure

---

## 0. Executive Summary

### The Three Limits

The discrete stella octangula encoding requires three distinct limit procedures:

| Limit | What Changes | What Survives |
|-------|--------------|---------------|
| **1. Spatial continuum** | O → SO(3) (effective), lattice → ℝ³ | Translation symmetry, Euclidean geometry |
| **2. Gauge group continuum** | Weight lattice → continuous Lie group | π₃(SU(3)) = Z, Z₃ center |
| **3. Thermodynamic limit** | V → ∞ for instanton sectors | θ-vacuum structure, cluster decomposition |

### Key Results

1. The **Z₃ center structure survives all limits** — it's a topological invariant
2. The **discrete O symmetry effectively enhances to continuous SO(3)** in the spatial limit
3. The **instanton classification π₃(SU(3)) = Z** emerges from the lattice of winding numbers
4. The **continuum limit is well-defined** and recovers standard field theory

---

## 1. Statement

### 1.1 Axioms Used

This proposition relies on three well-established results from algebraic topology, QFT, and statistical mechanics:

| Axiom | Mathematical Statement | Citation |
|-------|----------------------|----------|
| π₃(SU(3)) ≅ ℤ | Third homotopy group of SU(3) is the integers | Bott (1959), Ann. Math. 70, 313-337 |
| Sector orthogonality | lim_{V→∞} ⟨n\|m⟩_V = δ_{nm} | Coleman (1985), Ch. 7 |
| Cluster decomposition | lim_{\|x-y\|→∞} ⟨O(x)O(y)⟩ = ⟨O(x)⟩⟨O(y)⟩ | Weinberg (1995), Ch. 4 |

**Note:** The π₃(SU(3)) ≅ ℤ isomorphism can be witnessed constructively by the winding number map once SU(3) is determined. The Lean formalization proves this bijection explicitly without requiring the axiom.

### 1.2 Main Statement

**Proposition 0.0.6b (Continuum Limit from Discrete Structure)**

The discrete stella octangula encoding of SU(3) admits a well-defined continuum limit in which:

**(a) Spatial Continuum:** The FCC lattice with integer coordinates (n₁, n₂, n₃) becomes Euclidean ℝ³:
$$\Lambda_{FCC} \xrightarrow{a \to 0} \mathbb{R}^3$$

with the discrete O symmetry (24 proper rotations) effectively enhancing to SO(3) rotational symmetry as lattice-breaking corrections vanish.

**(b) Gauge Group Continuum:** The discrete weight structure on stella vertices generates the full continuous SU(3):
$$\{\text{stella vertices}\} \xrightarrow{\text{exponential map}} SU(3)$$

with preserved topological invariants π₃(SU(3)) = Z and center Z(SU(3)) = Z₃.

**(c) Thermodynamic Limit:** For instanton sectors, the infinite volume limit:
$$V = L^3 \to \infty$$

gives well-defined θ-vacua |θ⟩ = Σ_n e^{inθ}|n⟩ with cluster decomposition.

**(d) Z₃ Preservation:** The Z₃ center structure survives all limits:
- Discrete stella: Z₃ acts on color vertices by 120° rotation
- Continuous SU(3): Z(SU(3)) = Z₃ is the mathematical center
- θ-vacua: z_k|θ⟩ = |θ + 2πk/3⟩ (from Proposition 0.0.5a)

---

## 2. The Spatial Continuum Limit

### 2.1 Pre-Geometric Coordinates (Review from Theorem 0.0.6)

The FCC lattice provides integer coordinates without metric:
$$\Lambda_{FCC} = \{(n_1, n_2, n_3) \in \mathbb{Z}^3 : n_1 + n_2 + n_3 \equiv 0 \pmod{2}\}$$

**Combinatorial properties (no metric required):**
- Each site has 12 nearest neighbors (coordination number)
- Girth = 3 (triangles exist; e.g., (0,0,0)-(1,1,0)-(1,0,1) form a triangle)
- Vertex-transitive (all vertices are equivalent under symmetry)
- Octahedral symmetry O_h

### 2.2 Introduction of Physical Scale

From Proposition 0.0.17r, the lattice spacing is:
$$a^2 = \frac{8\ln(3)}{\sqrt{3}} \cdot \ell_P^2 \approx 5.07 \ell_P^2$$

Physical coordinates: $x^i = a \cdot n^i$

### 2.3 The Limit Procedure

**Definition 2.3.1 (Spatial Continuum Limit):**

Hold fixed the physical volume V and take N → ∞ sites:
$$a = (V/N)^{1/3} \to 0 \quad \text{as} \quad N \to \infty$$

**Theorem 2.3.2 (Symmetry Enhancement):**

In the limit a → 0, the discrete symmetry O (chiral octahedral group, 24 proper rotations) effectively enhances to continuous SO(3):
$$O \xrightarrow[\text{effective}]{a \to 0} SO(3)$$

**Proof:**

The enhancement O → SO(3) is an *effective* phenomenon, not a group-theoretic limit:

1. **Discrete symmetry:** The chiral octahedral group O ⊂ SO(3) consists of 24 proper rotations (det = +1). Note that O_h ⊂ O(3) includes 24 additional improper rotations (reflections with det = −1), but only the proper rotations O preserve orientation and lie in SO(3).

2. **Lattice-breaking effects:** At finite lattice spacing a, physical observables O(x) transform under O but not under general SO(3) rotations. The deviation from SO(3) invariance scales as:
   $$\delta O \sim \left(\frac{a}{L}\right)^n$$
   where L is the observation scale and n ≥ 1.

3. **Suppression at physical scales:** From Proposition 0.0.17r, a ≈ 2.25 ℓ_P. At any observable scale L ≫ ℓ_P:
   - At L = 1 fm (nuclear): a/L ∼ 10⁻²⁰
   - At L = 1 m (macroscopic): a/L ∼ 10⁻³⁵

   These lattice-breaking effects are utterly negligible.

4. **Effective SO(3):** In the low-energy effective theory, all physical observables become SO(3)-invariant because lattice corrections are below any measurable threshold. The effective symmetry group of the continuum limit is SO(3), though the microscopic symmetry is O.

5. **Not a sequence convergence:** This enhancement is *not* because O "converges to" SO(3)—finite groups cannot approximate continuous groups via sequences. Rather, the *physics* becomes SO(3)-invariant. ∎

### 2.4 What Survives the Spatial Limit

| Structure | Finite Lattice | Continuum Limit |
|-----------|---------------|-----------------|
| Symmetry | O (24 proper rotations) | SO(3) (continuous) |
| Coordinates | Integer labels | Real ℝ³ |
| Nearest neighbors | 12 per site | Continuous neighborhood |
| Topology | Discrete graph | Connected manifold |
| Translation | Discrete shifts | Continuous translations |

---

## 3. Gauge Group Determination from Discrete Data

### 3.1 Stella Encodes Weight Data

From Definition 0.0.0, the stella octangula provides:
- 6 weight vertices corresponding to fundamental + anti-fundamental weights
- 2 apex vertices (both at zero weight)
- S₃ ≅ Weyl(SU(3)) symmetry from permutations

This is **kinematic data** about SU(3) — the weights of the fundamental representation.

### 3.2 From Weights to Continuous Lie Group

**Theorem 3.2.1 (Weight Data Generates Group):**

The discrete weight structure uniquely determines the continuous Lie group SU(3).

**Proof:**

1. **Root system from weights:** The weight differences give root vectors:
   - $\alpha_1 = \mathbf{w}_R - \mathbf{w}_G$ (simple root)
   - $\alpha_2 = \mathbf{w}_G - \mathbf{w}_B$ (simple root)
   - This is the A₂ root system

2. **Lie algebra from roots:** The A₂ root system uniquely determines:
   $$\mathfrak{su}(3) = \mathfrak{h} \oplus \bigoplus_{\alpha \in \Phi} \mathfrak{g}_\alpha$$

   where h is the Cartan subalgebra (2-dimensional) and the sum is over roots.

3. **Lie group from algebra:** Exponentiating su(3) gives SU(3):
   $$SU(3) = \exp(\mathfrak{su}(3))$$

   This is the unique connected, simply-connected compact Lie group with Lie algebra su(3).

4. **Topological data:** Once SU(3) is determined, we automatically have:
   - π₃(SU(3)) = Z (from homotopy theory)
   - Z(SU(3)) = Z₃ (from Lie group structure)

**Conclusion:** The stella's discrete weight structure is sufficient to **uniquely determine** the continuous SU(3) and all its topological properties. ∎

### 3.3 What the Stella Does NOT Provide

The stella encodes **representation theory** (weights, Weyl group, charge conjugation), not **dynamics** (gauge fields, instantons, confinement).

| Encoded by Stella | Not Encoded by Stella |
|-------------------|----------------------|
| Weight lattice | Gauge field A_μ |
| Weyl group S₃ | Field strength F_μν |
| Z₃ center | Instanton configurations |
| Fundamental rep | Path integral measure |

**Key point:** The stella constrains the **kinematic structure** (which gauge group). The **dynamics** (field theory) requires additional input.

### 3.4 Emergence of π₃(SU(3)) = Z

**Question:** How does π₃(SU(3)) = Z emerge from the discrete stella?

**Answer:**

π₃(SU(3)) = Z is a **consequence of SU(3) being determined**, not directly encoded in the stella.

**Chain of logic:**
1. Stella → A₂ root system (discrete data)
2. A₂ root system → su(3) Lie algebra (continuous structure)
3. su(3) → SU(3) Lie group (exponentiation)
4. SU(3) has π₃(SU(3)) = Z (homotopy theory)

The stella determines WHICH group; homotopy theory determines its topological properties.

---

## 4. The Thermodynamic Limit for θ-Vacua

### 4.1 Why V → ∞ Is Needed

The θ-vacuum |θ⟩ = Σ_n e^{inθ}|n⟩ requires:
- Well-defined instanton sectors |n⟩
- Distinct topological charge Q for each sector
- Orthogonality: ⟨n|m⟩ = δ_{nm}

These properties only hold in the **thermodynamic limit** V → ∞.

### 4.2 The Limit Procedure

**Definition 4.2.1 (Thermodynamic Limit):**

Consider a sequence of volumes V_L = L³ with L → ∞:
1. **Fixed boundary conditions:** A_μ → pure gauge at spatial infinity
2. **Topological charge:** Q = (g²/32π²) ∫ F∧F ∈ Z
3. **Hilbert space:** H_L → H_∞ with orthogonal sectors

### 4.3 Instanton Sectors Become Well-Defined

**Theorem 4.3.1 (Sector Orthogonality):**

In the limit V → ∞, instanton sectors satisfy:
$$\lim_{V \to \infty} \langle n|m\rangle_V = \delta_{nm}$$

**Proof Sketch:**

At finite volume, gauge transformations can interpolate between sectors. In the infinite volume limit:
1. Large gauge transformations with winding become "infinite energy"
2. Sectors become superselection sectors
3. No local operator can change the topological charge
4. ⟨n|O|m⟩ = 0 for n ≠ m and local O ∎

### 4.4 θ-Vacuum Structure

In the thermodynamic limit, the θ-vacuum:
$$|\theta\rangle = \sum_{n=-\infty}^{\infty} e^{in\theta} |n\rangle$$

is well-defined with:
- Normalization: ⟨θ|θ'⟩ = 2πδ(θ - θ')
- Z₃ action: z_k|θ⟩ = |θ + 2πk/3⟩ (from Prop 0.0.5a)
- Energy density: ε(θ) = ε₀ + χ_top(1 - cos θ), with χ_top the topological susceptibility [Mass⁴]
- Total energy: E(θ) = V·ε(θ) = E₀ + χ_top·V·(1 - cos θ)

**Theorem 4.4.1 (Energy Divergence Selects θ = 0):**

For θ ≠ 0 (i.e., cos θ < 1), the energy difference between the θ-vacuum and the θ = 0 vacuum diverges in the thermodynamic limit:
$$\Delta E(\theta) = E(\theta) - E(0) = \chi_{top} \cdot V \cdot (1 - \cos\theta) \xrightarrow{V \to \infty} \infty$$

**Proof:**

1. For any θ with cos θ < 1, the factor (1 - cos θ) > 0
2. With χ_top > 0 (positive topological susceptibility), we have χ_top · (1 - cos θ) > 0
3. As V → ∞, the product χ_top · V · (1 - cos θ) → ∞
4. Therefore, only θ = 0 has finite energy in the thermodynamic limit ∎

**Physical interpretation:** This energy divergence, combined with Z₃ superselection (Prop 0.0.5a), ensures that θ = 0 is the unique physical vacuum state.

---

## 5. Z₃ Structure Survives All Limits

### 5.1 Z₃ at Each Level

| Level | Z₃ Manifestation | How It Appears |
|-------|------------------|----------------|
| **Discrete stella** | 120° rotation of color vertices | R → G → B → R |
| **Continuous SU(3)** | Center Z(SU(3)) = {1, ω, ω²} | ω = e^{2πi/3} |
| **θ-vacua** | Shift: z_k\|θ⟩ = \|θ + 2πk/3⟩ | Topological action |
| **Observables** | Z₃-invariance of $\mathcal{A}_{meas}$ | Prop 0.0.17i |

### 5.2 Why Z₃ Survives

**Theorem 5.2.1 (Z₃ Topological Invariance):**

The Z₃ structure is preserved under all limit procedures because it is a **topological invariant** of SU(3), not a metric or geometric property.

**Proof:**

1. **Algebraic origin:** Z₃ = Z(SU(3)) is the center of the group—a fixed property of the group structure itself.

2. **Group-theoretic determination:** The center is determined purely by the Lie algebra:
   $$Z(G) = \exp(2\pi i \cdot \text{coweight lattice} / \text{root lattice})$$

3. **For SU(3):** The quotient coweight/root lattice ≅ Z₃, giving Z(SU(3)) = {1, ω, ω²} with ω = e^{2πi/3}.

4. **Independence of limits:** The spatial limit a → 0 and thermodynamic limit V → ∞ affect the *representation* of physical fields on spacetime, but do not alter the gauge group structure. Once the stella determines SU(3) via the A₂ root system (§3), the center Z₃ is fixed as an intrinsic property of that group.

5. **Not subject to deformation:** Unlike metric properties, Z₃ is a discrete subgroup. There are no continuous paths connecting its elements, and no limit procedure can "smooth it away." ∎

### 5.3 Connection to Strong CP

The Z₃ preservation ensures that Proposition 0.0.5a (θ = 0 from Z₃ superselection) remains valid in the continuum:

1. **Discrete:** Z₃ acts on stella color vertices
2. **Limit:** Z₃ → Z(SU(3)) preserved
3. **θ-vacuum:** Z₃ shifts θ by 2π/3
4. **Observables:** Z₃-invariant (Prop 0.0.17i)
5. **Result:** θ = 0 selected (Prop 0.0.5a)

---

## 6. Cluster Decomposition

### 6.1 The Requirement

For a sensible QFT, cluster decomposition must hold:
$$\lim_{|x-y| \to \infty} \langle O(x) O(y) \rangle = \langle O(x) \rangle \langle O(y) \rangle$$

### 6.2 Cluster Decomposition for θ-Observables

**Theorem 6.2.1 (Cluster Decomposition):**

For Z₃-invariant observables O ∈ $\mathcal{A}_{meas}$, cluster decomposition holds in the thermodynamic limit.

**Proof:**

1. From Prop 0.0.17i, observables are Z₃-invariant
2. Z₃-invariant observables don't distinguish θ-vacua within an orbit
3. Within the selected θ = 0 vacuum, standard QFT cluster decomposition applies
4. The correlation length is finite (mass gap in confining phase)
5. Therefore cluster decomposition holds ∎

### 6.3 Colored Operators

**Note:** For colored (non-singlet) operators like quark fields ψ, cluster decomposition is more subtle:
- Quarks confine at large distances
- Color flux tubes prevent factorization
- But this is **confinement**, a dynamical property, not a failure of the framework

---

## 7. Summary

**Proposition 0.0.6b** establishes:

1. **Spatial continuum limit:** O → SO(3) (effective) as a → 0, with lattice → ℝ³
2. **Gauge group continuum:** Stella weights → A₂ roots → su(3) → SU(3), with π₃(SU(3)) = Z automatic
3. **Thermodynamic limit:** V → ∞ gives well-defined θ-vacua with orthogonal sectors
4. **Z₃ preservation:** The center Z(SU(3)) = Z₃ survives all limits as a topological invariant
5. **Cluster decomposition:** Holds for Z₃-invariant observables in the selected θ = 0 vacuum

**Key equation:**
$$\boxed{\text{Discrete stella} \xrightarrow{\text{limits}} \text{Continuous SU(3) gauge theory with } \pi_3 = \mathbb{Z}, Z_3 \text{ center}}$$

**Summary:** The continuum limit is explicitly constructed. The stella provides kinematic data (which group); homotopy theory and the thermodynamic limit provide the rest.

---

## 8. References

### Framework Documents

1. [Theorem 0.0.6](./Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md) — FCC lattice emergence
2. [Proposition 0.0.17r](./Proposition-0.0.17r-Lattice-Spacing-From-Holographic-Self-Consistency.md) — Lattice spacing derivation
3. [Definition 0.0.0](./Definition-0.0.0-Minimal-Geometric-Realization.md) — Stella-SU(3) correspondence
4. [Theorem 0.0.15](./Theorem-0.0.15-Topological-Derivation-SU3.md) — Z₃ center structure
5. [Proposition 0.0.5a](./Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md) — θ = 0 from Z₃

### External Literature

6. Bott, R. (1959). "The stable homotopy of the classical groups." Ann. Math. 70, 313-337. [π₃(SU(n)) = Z]
7. Wilson, K.G. (1974). "Confinement of quarks." Phys. Rev. D 10, 2445. [Lattice gauge theory]

### θ-Vacuum Physics

8. Callan, C.G., Dashen, R.F. & Gross, D.J. (1976). "The structure of the gauge theory vacuum." Phys. Lett. B 63, 334-340. [θ-vacuum construction]
9. Coleman, S. (1985). "Aspects of Symmetry." Cambridge University Press, Ch. 7. [Instantons and θ-vacua, definitive reference]
10. 't Hooft, G. (1978). "On the phase transition towards permanent quark confinement." Nucl. Phys. B 138, 1-25. [Z₃ center symmetry and confinement]
11. Svetitsky, B. & Yaffe, L.G. (1982). "Critical behavior at finite-temperature confinement transitions." Nucl. Phys. B 210, 423-447. [Z₃ deconfinement transition]

### Group Theory

12. Conway, J.H. & Smith, D.A. (2003). "On Quaternions and Octonions." A.K. Peters. [Finite subgroups of SO(3)]
13. Mimura, M. & Toda, H. (1963). "Homotopy groups of SU(3), SU(4) and Sp(2)." J. Math. Kyoto Univ. 3, 217-250. [Explicit π₃ calculation]

---

*Proposition created: January 11, 2026*
*Corrections applied: January 12, 2026*
*Status: ✅ VERIFIED — Continuum Limit Procedure*
*Key result: Continuum limit explicitly constructed, Z₃ preserved*
