# Theorem 0.0.41: Dimensional Incompleteness

## Status: 🔶 NOVEL ✅ VERIFIED (multi-agent) — METATHEOREM ON SCALE DETERMINATION IN PHYSICAL THEORIES

**Date:** 2026-03-29

**Abstract:** We prove that any axiom system whose equations are homogeneous under mass-dimension rescaling — including any system built from topological, combinatorial, or algebraic inputs — requires at least one empirical dimensionful input to determine all physical quantities. The solution set of such a system is a principal $\mathbb{R}_+$-bundle over the space of dimensionless solutions, and no finite addition of scale-homogeneous equations can reduce the fiber. This is a rigorous consequence of the Buckingham Pi theorem, upgraded from a dimensional-analysis tool to a metatheorem about the relationship between mathematical structure and physical measurement. One dimensionful input is both necessary and sufficient.

**Dependencies:**
- ✅ ESTABLISHED: Buckingham Pi theorem (Buckingham 1914, Phys. Rev. 4, 345)
- ✅ ESTABLISHED: Theory of principal bundles and group actions on smooth manifolds
- ✅ ESTABLISHED: Dimensional analysis in field theory (Bridgman 1931)
- ✅ VERIFIED: Prop 5.2.5e (Holographic Self-Encoding Scale Invariance — explicit no-go for CG)

**Relationship to existing results:**
- **Prop 0.0.35** (Dimensional Uniqueness of R_stella): Establishes that R_stella is the unique dimensional source *within CG*. The present theorem proves this is the *theoretical minimum for any scale-homogeneous theory*.
- **Prop 0.0.36** (Anthropic Bounds on R_stella): Constrains R_stella to a finite range but does not determine a unique value. Consistent with the present theorem's conclusion that one measurement is irreducible.

---

## §0. Motivation

The Chiral Geometrogenesis framework derives all dimensionless physical quantities — coupling constants, mass ratios, hierarchies spanning 19 orders of magnitude — from three topological integers $(N_c, N_f, \chi) = (3, 3, 4)$ of the stella octangula. Yet one dimensionful input ($R_\text{stella} = 0.44847$ fm) remains required to anchor the framework to physical units.

A natural question: is this a deficiency of CG, or a structural feature of any theory with CG's mathematical character? This theorem proves the latter. The irreducibility of one dimensionful input is a theorem about scale-homogeneous axiom systems — a class that necessarily includes any theory built from topology, algebra, and standard field equations.

---

## §1. Definitions

### Definition 1.1 (Scale-Homogeneous Axiom System)

A *scale-homogeneous axiom system* is a triple $(\mathcal{Q}, \mathcal{D}, \mathcal{E})$ where:

1. $\mathcal{Q} = \{Q_1, \ldots, Q_m\}$ is a finite set of physical quantities.
2. $\mathcal{D}: \mathcal{Q} \to \mathbb{Z}$ assigns each quantity its mass dimension $d_i = \mathcal{D}(Q_i)$ in natural units ($\hbar = c = 1$). At least one $d_i \neq 0$ (the system has non-trivial dimensionful content).
3. $\mathcal{E} = \{e_1, \ldots, e_n\}$ is a finite set of equations (the "axioms") constraining the $Q_i$, such that each $e_j$ is *homogeneous under the scaling group*: if $(Q_1, \ldots, Q_m)$ satisfies $e_j$, then so does $(\lambda^{d_1} Q_1, \ldots, \lambda^{d_m} Q_m)$ for all $\lambda > 0$.

### Definition 1.2 (Scaling Group Action)

The multiplicative group $\mathbb{R}_+ = (0, \infty)$ acts on the space of positive configurations $\mathbb{R}^m_{>0}$ via:

$$\mathcal{R}_\lambda: (Q_1, \ldots, Q_m) \mapsto (\lambda^{d_1} Q_1, \ldots, \lambda^{d_m} Q_m)$$

The homogeneity condition on $\mathcal{E}$ is precisely the statement that the solution set $\mathcal{S} \subset \mathbb{R}^m_{>0}$ is $\mathcal{R}$-invariant: $\mathcal{R}_\lambda(\mathcal{S}) = \mathcal{S}$ for all $\lambda > 0$.

### Definition 1.3 (Dimensionless Quotient)

The *dimensionless quotient* is the orbit space:

$$\bar{\mathcal{S}} = \mathcal{S} / \mathbb{R}_+$$

Each point of $\bar{\mathcal{S}}$ represents a class of physically equivalent solutions differing only in overall scale. The natural projection $\pi: \mathcal{S} \to \bar{\mathcal{S}}$ sends each solution to its orbit.

### Definition 1.4 (Dimensionful Empirical Input)

A *dimensionful empirical input* is an equation of the form $Q_i = q_i$ where $d_i \neq 0$ and $q_i \in \mathbb{R}_{>0}$ is an empirically determined value.

---

## §2. Theorem Statement

**Theorem 0.0.41 (Dimensional Incompleteness).** Let $(\mathcal{Q}, \mathcal{D}, \mathcal{E})$ be a scale-homogeneous axiom system with at least one quantity of non-zero mass dimension. Suppose the solution set $\mathcal{S} \subset \mathbb{R}^m_{>0}$ is non-empty. Then:

**(a) Bundle Structure.** The projection $\pi: \mathcal{S} \to \bar{\mathcal{S}}$ is a principal $\mathbb{R}_+$-bundle. Each fiber is a copy of $\mathbb{R}_+$ — a one-parameter family of solutions.

**(b) Irreducibility.** No equation $e_{n+1}$ that is itself scale-homogeneous can reduce the fiber to a point. That is, adding finitely many scale-homogeneous equations cannot break the $\mathbb{R}_+$-symmetry.

**(c) Necessity.** Selecting a unique physical solution $s_0 \in \mathcal{S}$ from the orbit $\pi^{-1}(\bar{s})$ requires exactly one dimensionful empirical input.

**(d) Sufficiency.** One such input suffices: given any $Q_i$ with $d_i \neq 0$ and an empirical value $q_i > 0$, the equation $Q_i = q_i$ uniquely selects a point on each fiber.

---

## §3. Proof

### §3.1 Proof of (a): Bundle Structure

**Lemma (Freeness).** The $\mathbb{R}_+$-action on $\mathcal{S}$ is free — that is, $\mathcal{R}_\lambda(s) = s$ implies $\lambda = 1$ for all $s \in \mathcal{S}$.

*Proof.* Suppose $\mathcal{R}_\lambda(s) = s$ for some $s = (Q_1, \ldots, Q_m) \in \mathcal{S}$. Then $\lambda^{d_i} Q_i = Q_i$ for all $i$. Since $Q_i > 0$ (as $\mathcal{S} \subset \mathbb{R}^m_{>0}$), this gives $\lambda^{d_i} = 1$ for all $i$. For any $i$ with $d_i \neq 0$, this forces $\lambda = 1$ (since $\lambda > 0$ and $d_i \in \mathbb{Z} \setminus \{0\}$). By hypothesis, at least one such $i$ exists. Therefore the action is free universally on $\mathcal{S}$ — not merely generically. $\square$

**Properness.** The action $\mathcal{R}: \mathbb{R}_+ \times \mathcal{S} \to \mathcal{S} \times \mathcal{S}$ given by $(\lambda, s) \mapsto (\mathcal{R}_\lambda(s), s)$ is proper. To see this: the map $\mathbb{R}_+ \times \mathbb{R}^m_{>0} \to \mathbb{R}^m_{>0} \times \mathbb{R}^m_{>0}$ given by $(\lambda, Q) \mapsto (\mathcal{R}_\lambda(Q), Q)$ is proper because for any compact $K \subset \mathbb{R}^m_{>0} \times \mathbb{R}^m_{>0}$, the preimage is bounded in $\lambda$ (since $\lambda^{d_i} = Q'_i/Q_i$ for some $i$ with $d_i \neq 0$, and $Q_i, Q'_i$ range over a compact set of positive reals). The restriction to $\mathcal{S}$ inherits properness.

**Bundle structure.** A free and proper action of $\mathbb{R}_+$ on a Hausdorff topological space yields a principal $\mathbb{R}_+$-bundle (see e.g. Palais 1961):

$$\pi: \mathcal{S} \to \bar{\mathcal{S}} = \mathcal{S}/\mathbb{R}_+$$

The quotient $\bar{\mathcal{S}}$ is Hausdorff because the action is proper. Since $\mathbb{R}_+$ is contractible (homeomorphic to $\mathbb{R}$ via $\lambda \mapsto \ln\lambda$), all principal $\mathbb{R}_+$-bundles are trivial:

$$\mathcal{S} \cong \bar{\mathcal{S}} \times \mathbb{R}_+$$

Each fiber $\pi^{-1}(\bar{s})$ is homeomorphic to $\mathbb{R}_+$, representing the one-parameter family of solutions obtained by rescaling a given solution by all possible $\lambda > 0$. $\square$

### §3.2 Proof of (b): Irreducibility

Let $e_{n+1}$ be a scale-homogeneous equation. Its solution set $\mathcal{S}_{n+1} \subset \mathbb{R}^m_{>0}$ is $\mathcal{R}$-invariant by definition.

The augmented solution set is:

$$\mathcal{S}' = \mathcal{S} \cap \mathcal{S}_{n+1}$$

Since both $\mathcal{S}$ and $\mathcal{S}_{n+1}$ are $\mathcal{R}$-invariant, their intersection $\mathcal{S}'$ is also $\mathcal{R}$-invariant. If $\mathcal{S}'$ is non-empty and the $\mathbb{R}_+$-action remains free on $\mathcal{S}'$, then by part (a), $\mathcal{S}'$ is again a principal $\mathbb{R}_+$-bundle over $\mathcal{S}'/\mathbb{R}_+$.

In particular, each non-empty fiber of $\mathcal{S}'$ is a copy of $\mathbb{R}_+$ — it cannot be a single point.

**By induction:** Adding any finite number of scale-homogeneous equations preserves the $\mathcal{R}$-invariance and hence the bundle structure. The fiber dimension remains 1 (or the solution set becomes empty). No finite collection of scale-homogeneous equations can reduce the fiber to a point without eliminating all solutions. $\square$

### §3.3 Proof of (c) and (d): Necessity and Sufficiency

**Sufficiency.** Consider the equation $Q_i = q_i$ with $d_i \neq 0$ and $q_i > 0$. Under $\mathcal{R}_\lambda$, this becomes:

$$\lambda^{d_i} Q_i = q_i$$

For a given $s \in \mathcal{S}$ with $Q_i(s) = Q_i^0$, this is satisfied uniquely by:

$$\lambda = \left(\frac{q_i}{Q_i^0}\right)^{1/d_i}$$

This uniquely determines $\lambda$, selecting a single point on the fiber $\pi^{-1}(\pi(s))$. $\square$

**Necessity.** Without any dimensionful empirical input, every equation constraining the $Q_i$ is scale-homogeneous (by the hypothesis that the axiom system consists only of scale-homogeneous equations). By part (b), the $\mathbb{R}_+$-orbit remains unbroken — the fiber is not reduced. Therefore no unique solution is selected.

Could *two or more* dimensionful inputs be needed? No. Once one dimensionful input fixes $\lambda$ (as shown above), all other dimensionful quantities are determined by the remaining (scale-homogeneous) equations, which fix all dimensionless ratios. A second empirical input would either be redundant (consistent with the first) or contradictory (inconsistent with the equations). Therefore exactly one dimensionful input is both necessary and sufficient. $\square$

---

## §4. Why Topological Axiom Systems Are Scale-Homogeneous

The theorem's hypothesis is *scale-homogeneity*, not "topological origin." This section establishes that topological/combinatorial axiom systems necessarily satisfy the hypothesis.

### §4.1 Classification of Ingredients

The building blocks of a topological axiom system fall into four categories:

| Category | Examples | Dimension |
|----------|----------|-----------|
| (i) Topological integers | Euler characteristics, Betti numbers, representation dimensions, winding numbers | Dimensionless |
| (ii) Algebraic rationals | Group theory coefficients, anomaly factors, Casimir invariants | Dimensionless |
| (iii) Geometric transcendentals | $\pi$, $\ln 2$, $\ln 3$, $e$ | Dimensionless |
| (iv) Field equations | Conservation laws, equations of motion, thermodynamic identities | Dimension-homogeneous |

### §4.2 Proof of Scale-Homogeneity

**Claim.** Any axiom system constructed from ingredients (i)–(iv) is scale-homogeneous.

**Proof.** Categories (i)–(iii) produce only dimensionless constants. Category (iv) produces equations that are homogeneous in mass dimension — this is a standard property of physical field equations, following from the requirement that all terms in an equation carry the same dimensions.

Any equation of the form:

$$f(\{Q_i\}, \{c_\alpha\}) = 0$$

where $\{c_\alpha\}$ are dimensionless constants and $f$ is polynomial (or analytic) in the $Q_i$, must have every monomial at the same mass dimension (dimensional consistency). Under $\mathcal{R}_\lambda$, each monomial scales by $\lambda^D$ where $D$ is the common dimension, so:

$$f(\{\lambda^{d_i} Q_i\}, \{c_\alpha\}) = \lambda^D f(\{Q_i\}, \{c_\alpha\}) = 0$$

The equation is satisfied if and only if the original is. Therefore $f = 0$ is scale-homogeneous.

**Remark (Quantum anomalous dimensions).** In quantum field theory, operators acquire anomalous dimensions $\gamma(\mu)$ under renormalization, so that the scaling dimension becomes $d_i + \gamma_i(\alpha_s(\mu))$. This does not violate scale homogeneity because the renormalization group equations themselves — $\mu \, d\alpha_s/d\mu = \beta(\alpha_s)$ — are degree-0 (dimensionless = function of dimensionless). The running coupling $\alpha_s(\mu)$ depends on the *ratio* $\mu/\Lambda_\text{QCD}$, not on any absolute scale. Thus quantum corrections modify the exponents but preserve the $\mathbb{R}_+$-invariance of the solution set. $\square$

### §4.3 Application to CG

The CG framework is constructed from:
- $(N_c, N_f, \chi) = (3, 3, 4)$ — topological integers from the stella octangula (category i)
- $b_0 = (11N_c - 2N_f)/(12\pi) = 9/(4\pi)$ — one-loop $\beta$-function coefficient combining group theory integers with the loop factor (categories ii + iii)
- $\pi$, $\ln 3$ — geometric constants in lattice spacing and information formulas (category iii)
- QCD field equations, thermodynamic identities, Einstein equations — standard field theory (category iv)

By §4.2, all CG equations are scale-homogeneous. The projective ambiguity (Prop 5.2.5e) is therefore not a contingent feature but an inevitable consequence of the framework's topological foundation.

---

## §5. The Buckingham Pi Metatheorem

### §5.1 Classical Buckingham Pi Theorem

The Buckingham Pi theorem (1914) states: if a physical relation involves $m$ quantities with $k$ independent base dimensions, it can be expressed as a relation among $m - k$ dimensionless products (the "Pi groups").

### §5.2 Upgrade to Metatheorem

The Dimensional Incompleteness Theorem is the Buckingham Pi theorem applied *reflexively* — to the axiom system itself rather than to a specific physical problem:

**Buckingham Pi (classical):** A physical problem with $m$ quantities and $k$ base dimensions has $m - k$ independent dimensionless constraints.

**Dimensional Incompleteness (metatheorem):** A topological axiom system determines *all* dimensionless constraints (the best case: $m - k$ equations for $m - k$ unknowns, fully fixing the dimensionless quotient $\bar{\mathcal{S}}$ to a point). The remaining $k$ parameters — at minimum 1, since physical theories in natural units ($\hbar = c = 1$) have $k = 1$ independent dimension (mass/energy/length/inverse-time are all equivalent) — require empirical input.

### §5.3 Why This Was Not Previously Recognized

The Buckingham Pi theorem has been a standard tool since 1914, but its metatheoretic content — as a lower bound on empirical inputs for any scale-homogeneous theory — was not previously articulated because:

1. **No theory before CG saturated the bound.** The Standard Model has $\sim$20 undetermined parameters. The bound $N_\text{dim} \geq 1$ was far from relevant.
2. **The distinction between dimensionless and dimensionful inputs was not emphasized.** CG's sharp separation — 0 dimensionless, 1 dimensionful — makes the bound visible for the first time.
3. **The theorem was considered "obvious."** Physicists informally know "you need at least one unit." The formal statement — that this is a *theorem* about axiom systems, not merely a convention — had not been made precise.

---

## §6. Scope and Limitations

### §6.1 What the Theorem Does NOT Say

1. **It does not claim all theories need exactly one input.** Most theories (SM, string theory) need many more. The theorem establishes only the *lower bound*.
2. **It does not address dimensionless parameters.** A theory may have many undetermined dimensionless couplings (the SM has ~19 in the minimal formulation, ~25–26 including neutrino masses and mixing). The theorem constrains only the dimensionful sector.
3. **It does not rule out a "theory of everything."** A ToE is possible — it must either accept one dimensionful input or derive a dimensionful constant from non-topological mathematics (no known candidate).

### §6.2 Potential Evasions

The theorem can be evaded only by an axiom that is *inhomogeneous* under mass-dimension rescaling:

| Evasion route | Mechanism | Assessment |
|---------------|-----------|------------|
| Mathematical dimensionful constant | A pure number with units | No such object exists in mathematics |
| Discrete quantization of scale | Topological invariant constraining a continuous scale | Topological invariants are dimensionless integers |
| Compactification of $\mathbb{R}_+$ to $S^1$ | Discrete scale symmetry | Would require a physical mechanism; compactification radius is itself dimensionful |
| Non-standard dimensional analysis | Abandon dimension-consistency requirement | Would invalidate mathematical physics |

### §6.3 The Conformal Class Interpretation

The theorem admits a geometric restatement: *a topological axiom system determines a conformal class, not a metric. Promoting a conformal class to a metric requires exactly one measurement.*

- **Pre-geometric phase:** The stella octangula is a purely topological object defining a conformal class — all geometric relationships up to overall scale.
- **Geometric phase:** Spacetime emerges with a physical metric in the conformal class determined by topology, but the overall scale is not fixed.
- **The one input:** Selecting a metric from a conformal class requires one real number — the conformal factor. This is $R_\text{stella}$.

---

## §7. Relationship to Gödel's Incompleteness Theorem

### §7.1 Structural Analogy

| Feature | Gödel's Incompleteness | Dimensional Incompleteness |
|---------|----------------------|---------------------------|
| System | Formal arithmetic (Peano axioms) | Scale-homogeneous axiom system |
| Self-referential structure | Gödel sentence: "This statement is unprovable" | Projective orbit: "All scales satisfy these equations" |
| What is underdetermined | Truth of certain arithmetic statements | Absolute scale of physical quantities |
| What is determined | All provable truths from the axioms | All dimensionless ratios from topology |
| Resolution | Accept incompleteness or add axioms | Accept one empirical input or add inhomogeneous axiom |

### §7.2 Where the Analogy Breaks Down

Despite the structural parallel, the two theorems are fundamentally different:

1. **Gödel concerns self-reference; Dimensional Incompleteness concerns symmetry.** Gödel constructs a self-referential sentence within the formal system. Dimensional Incompleteness identifies a symmetry ($\mathbb{R}_+$-rescaling) that the axiom system respects.

2. **Gödel's limitation is absolute; Dimensional Incompleteness is conditional.** Gödel's incompleteness cannot be circumvented by adding axioms (any consistent extension is itself incomplete). Dimensional Incompleteness *can* be circumvented by an inhomogeneous equation — one that explicitly breaks the scaling symmetry. The theorem says only that such an equation cannot come from topological/combinatorial axioms.

3. **Different underdetermination types.** Gödel: true arithmetic statements that no proof can reach. Dimensional Incompleteness: all solutions on the projective orbit are *equally valid* mathematically. The physical world selects a scale, but this selection is empirical, not mathematical.

### §7.3 A Better Analogy: Gauge Fixing

A more precise analogy is gauge fixing in electrodynamics:

- Maxwell's equations are gauge-invariant: $A_\mu \to A_\mu + \partial_\mu \chi$ preserves all physics.
- To compute, one must choose a gauge — an additional condition not contained in Maxwell's equations.
- The gauge choice carries no physical information; it is a convention.

Similarly:
- CG's equations are scale-invariant: $Q \to \lambda^d Q$ preserves all dimensionless physics.
- To connect to observation, one must choose a scale anchor — an additional datum not contained in the equations.
- The choice of *which* quantity to anchor is conventional ($R_\text{stella}$ vs $\ell_P$ vs $G$); the *value* is empirical.

The Dimensional Incompleteness Theorem states that this "gauge freedom" in the scale direction is irreducible for any scale-homogeneous system.

---

## §8. Information-Theoretic Formulation

### §8.1 The Information Content of Scale

The theorem can be recast information-theoretically. The question becomes: *how much information must be transmitted from the physical world to the mathematical framework to fully determine all physical quantities?*

**The mathematical framework provides:** All dimensionless ratios and structural information — encoded in the topological data.

**The physical world must provide:** One real number — the value of any single dimensionful quantity.

**Information content:** A real number carries $\log_2(\text{range}/\text{precision})$ bits. For $R_\text{stella}$: the range of physically sensible values spans ~40 orders of magnitude ($\sim$133 bits); current precision ($\delta R/R \sim 7\%$) contributes $\sim$4 bits. Total: $\sim$137 bits.

### §8.2 The Minimum Channel Capacity

**Definition (Dimensional Channel).** The *dimensional channel* is the minimum-capacity information channel between a mathematical axiom system and physical reality, required to select a unique physical solution.

For a scale-homogeneous system, the undetermined degree of freedom lives on a single $\mathbb{R}_+$-fiber. Via $\lambda \mapsto \ln\lambda$, this fiber is isomorphic to $\mathbb{R}$. Specifying a point on $\mathbb{R}$ to precision $\delta$ within a range of width $\Delta$ requires:

$$C_\text{dim}(\delta, \Delta) = \log_2(\Delta / \delta) \text{ bits}$$

The *topological* content — that exactly one real parameter must be supplied, corresponding to the single $\mathbb{R}_+$-fiber — is independent of precision. The *metrical* content (how many bits) depends on the prior range and measurement precision, as illustrated in §8.1.

### §8.3 Holographic Interpretation

In the CG framework, the stella boundary $\partial\mathcal{S}$ encodes all *structural* information via its topology. The one missing datum — $R_\text{stella}$ — is the *size* of $\partial\mathcal{S}$ in physical units. The holographic principle determines the information density (bits per Planck area) but not the Planck area itself (Prop 5.2.5e).

**Restatement:** The holographic principle determines how information is *organized* but not the *size* of the organizational unit.

---

## §9. Physical Interpretation

### §9.1 The Tripartite Structure of Physical Law

The Dimensional Incompleteness Theorem, combined with CG's structural completeness, reveals a tripartite architecture:

```
┌──────────────────────────────────┐
│  TOPOLOGY  (stella octangula)    │  ← Fully determined, discrete
│  All dimensionless quantities    │     N_c = 3, χ = 4, b₀ = 9/(4π)
│  All ratios, hierarchies         │     Zero free parameters
├──────────────────────────────────┤
│  ANOMALY  (conformal breaking)   │  ← Magnitude set by one input
│  β-function running, Λ_QCD,     │     R_stella = 0.44847 fm
│  dimensional transmutation       │     One free parameter
├──────────────────────────────────┤
│  OBSERVATION  (measurement)      │  ← The bridge to meter sticks
│  ℏ, c, k_B (unit conversions)   │     Convention, not physics
│  Coordinate system choice        │     Zero physical content
└──────────────────────────────────┘
```

The first layer is mathematics. The third layer is convention. The second — the anomaly magnitude — is the irreducible empirical content.

### §9.2 The Sharpened "Why These Constants?" Question

Classical physics asks: "Why do the fundamental constants have the values they do?" CG eliminates all instances of this question except one:

> *Why does the conformal anomaly of the SU(3) gauge theory on $\partial\mathcal{S}$ have magnitude $\sqrt{\sigma} = 440$ MeV rather than some other value?*

The Dimensional Incompleteness Theorem proves this question is unanswerable from within any scale-homogeneous axiom system. It is not a gap in CG but a feature of the mathematics-to-measurement interface.

---

## §10. Consistency Checks

### §10.1 Dimensional Analysis

The theorem itself is "dimensionless" — it is a statement about the structure of solution sets, involving no specific physical quantities. ✓

### §10.2 Recovery of Known Results

- **Standard Model:** $N_\text{dim} = 1$ (e.g., $M_Z$) plus $\sim$19 dimensionless parameters in the minimal formulation ($\sim$25–26 with neutrino masses and mixing, since neutrino oscillations are experimentally established). The theorem's bound $N_\text{dim} \geq 1$ is satisfied but far from saturated in the dimensionless sector. ✓
- **String theory:** $N_\text{dim} = 1$ (string length) plus O(100–500) moduli. Bound satisfied, far from saturated. ✓
- **CG:** $N_\text{dim} = 1$ ($R_\text{stella}$), 0 dimensionless free parameters. Bound saturated. ✓

### §10.3 Self-Consistency

The theorem does not apply to itself (it is a mathematical theorem about physical axiom systems, not a physical axiom system). No circularity. ✓

### §10.4 Explicit Verification in CG

The bootstrap equations (Prop 0.0.17y) form a DAG of 7 equations. Each is verified to be scale-homogeneous:

| Equation | Content | Homogeneity check |
|----------|---------|-------------------|
| ε₁ | $\alpha_s(M_P) = 1/64$ | Dimensionless = dimensionless. Degree 0. ✓ |
| ε₂ | $b_0 = 9/(4\pi)$ | Dimensionless = dimensionless. Degree 0. ✓ |
| ε₃ | $R_\text{stella}/\ell_P = \exp(128\pi/9)$ | Length/length = dimensionless. Degree 0. ✓ |
| ε₄ | $\sqrt{\sigma} = \hbar c / R_\text{stella}$ | Energy = energy·length / length. Degree 1. ✓ |
| ε₅ | $a^2 = (8\ln 3/\sqrt{3})\,\ell_P^2$ | Length² = dimensionless × length². Degree 2. ✓ |
| ε₆ | $M_P = \hbar c / \ell_P$ | Energy = energy × length / length. Degree 1. ✓ |
| ε₇ | $a/\ell_P = \sqrt{8\ln 3/\sqrt{3}}$ | Length/length = dimensionless. Degree 0. ✓ |

All equations are homogeneous. The theorem applies.

**Note on independence:** ε₇ is algebraically equivalent to ε₅ (dividing ε₅ by $\ell_P^2$ and taking the square root yields ε₇). Similarly, ε₆ is the definition $M_P = \hbar c/\ell_P$, which is a unit conversion rather than an independent constraint. The effective number of independent scale-homogeneous constraints is therefore 5, not 7. This does not affect the theorem — any number of scale-homogeneous equations leaves the $\mathbb{R}_+$-fiber intact. $\square$

---

## §11. Open Questions

1. **Does any mathematical structure provide a dimensionful constant?** No candidate is known. All mathematical constants ($\pi$, $e$, $\gamma$) are dimensionless. A positive answer would evade the theorem but would require a radical departure from known mathematics.

2. **Discrete scale symmetry as partial evasion?** If a physical mechanism compactified $\mathbb{R}_+$ to $S^1$ (as in the Efimov effect in atomic physics), the scale would be constrained to a discrete lattice rather than a continuum. However, the compactification radius would itself be a dimensionful parameter, merely reformulating rather than eliminating the input.

3. **Connection to the measurement problem.** The irreducible role of one empirical input resonates with (but is distinct from) the quantum measurement problem. Whether this analogy has deeper content remains open.

---

## §12. References

| Reference | Key result | Relevance |
|-----------|-----------|-----------|
| Buckingham (1914), Phys. Rev. 4, 345 | Pi theorem: $m$ quantities, $k$ dimensions → $m-k$ dimensionless groups | Foundation for the metatheorem |
| Bridgman (1931), *Dimensional Analysis* | Systematic treatment of dimensional reasoning | Framework for scale homogeneity |
| Barenblatt (1996), *Scaling, Self-Similarity* | Modern treatment of dimensional analysis | Self-similar solutions as projective orbits |
| Gödel (1931), Monatshefte Math. 38 | Incompleteness of consistent formal systems | Structural analogy (§7) |
| Wigner (1960), Comm. Pure Appl. Math. 13 | "Unreasonable effectiveness of mathematics" | Context (§9) |
| 't Hooft & Veltman (1972), Nucl. Phys. B 44, 189 | Dimensional regularization introduces arbitrary mass scale $\mu$ | Scale ambiguity in quantum field theory (§4.2) |
| 't Hooft (1980), in *Recent Developments in Gauge Theories*, NATO ASI B59, 135 | Technical naturalness: small parameters require symmetry protection | Naturalness of scale inputs (§6) |
| Deser, Duff & Isham (1976), Nucl. Phys. B 111, 45 | Nonlocal conformal anomalies in curved spacetime | Conformal class interpretation (§6.3) |
| Palais (1961), Ann. Math. 73, 295 | Proper actions yield principal bundles | Bundle structure (§3.1) |
| Prop 0.0.35 | R_stella is unique dimensional source in CG | CG-specific instance of this theorem |
| Prop 5.2.5e | $I_\text{stella} = I_\text{gravity}$ is degree 0 | Explicit no-go verifying the theorem for CG's holographic condition |
| Prop 0.0.17y | 7-equation bootstrap DAG, unique projective fixed point | Explicit scale-homogeneous system (§10.4) |
| Research-Absolute-Scale-Determination-Paths.md | Directions A–E investigation | Exhaustive analysis motivating and supporting this theorem |

---

## §13. Verification Records

- **Multi-Agent Peer Review (2026-03-29):** [Theorem-0.0.41-Dimensional-Incompleteness-Multi-Agent-Verification-2026-03-29.md](../verification-records/Theorem-0.0.41-Dimensional-Incompleteness-Multi-Agent-Verification-2026-03-29.md) — 3-agent adversarial review (mathematical, physics, literature). All agents verify with high confidence.
- **Adversarial Physics Verification:** [theorem_0_0_41_adversarial_verification.py](../../../verification/foundations/theorem_0_0_41_adversarial_verification.py) — 34 numerical tests covering freeness, scale homogeneity, bundle structure, irreducibility, sufficiency, necessity, and adversarial attempts to break scale invariance. All tests pass. Plots: [theorem_0_0_41_dimensional_incompleteness.png](../../../verification/plots/theorem_0_0_41_dimensional_incompleteness.png)
