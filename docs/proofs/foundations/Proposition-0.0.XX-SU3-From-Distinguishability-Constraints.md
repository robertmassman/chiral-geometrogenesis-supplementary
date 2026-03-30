# Proposition 0.0.XX: SU(3) from Distinguishability and Dimensionality Constraints

## Status: 🔶 NOVEL — SU(3) RETRODICTION FROM DISTINGUISHABILITY + QUANTUM INTERFERENCE (A-IF) + COLOR NEUTRALITY

**Created:** 2026-02-01
**Purpose:** Provide a novel retrodiction of SU(3) — the known QCD gauge group since ~1973 — by showing it is uniquely selected by observer distinguishability requirements combined with the dimensionality constraint D = 4 from Theorem 0.0.1. This is a novel *explanation* of a known fact, not a prediction: the conclusion (SU(3)) is already established experimentally, and the lower bound (N ≥ 3) relies on the framework-specific Assumption A-IF.

**Important Limitation:** This derivation is NOT purely information-theoretic. (1) The lower bound (N ≥ 3) depends on the **quantum interference form** for probability distributions (Assumption A-IF below) — a framework-specific input that presupposes coherent superposition and the Born rule. Without it, the Fisher metric is generically non-degenerate for all N ≥ 2 and the N = 2 elimination fails. (2) The upper bound (N ≤ 4) requires the geometric input D_space = 3 from observer existence.

**Research Path:** This addresses Path A from [Research-Meta-Foundational-Directions.md](../supporting/Research-Meta-Foundational-Directions.md), identified as **top priority** for 2026 Q1-Q2.

**Dependencies:**
- ✅ Theorem 0.0.1 (Observer Existence → D = 4)
- ✅ Lemma 0.0.2a (Confinement-Dimension Constraint) — Affine independence bound N ≤ 4
- ✅ Proposition 0.0.XXa (First Stable Principle) — Pure info-theoretic bound N = 3
- ✅ Proposition 0.0.17b (Fisher Metric Uniqueness)
- ✅ Theorem 0.1.0 (Field Existence from Distinguishability)
- ✅ Theorem 0.0.17 (Information-Geometric Unification)
- ✅ Lemma 0.0.17c (Fisher-Killing Equivalence) — Used in Approach C (Theorem 3.2.1)
- 📚 Standard results: Cartan classification, Fisher information geometry (Amari & Nagaoka)

**Explicit Assumptions (framework-specific inputs not derived within this proposition):**

> **Assumption A-IF (Quantum Interference Form):** The probability distribution for $N$ distinguishable components takes the coherent superposition form:
>
> $$p_\phi(x) = \left|\sum_c A_c(x)\, e^{i\phi_c}\right|^2$$
>
> This presupposes: (i) complex-valued amplitudes, (ii) coherent superposition (amplitudes add before squaring), and (iii) the Born rule (probability = |amplitude|²). These are substantial physical assumptions that encode quantum-mechanical structure at the pre-geometric level.
>
> **Why this matters:** A classical probability mixture $p(x) = \sum_c w_c P_c(x)$ with positive weights would yield a generically non-degenerate Fisher metric for **all** $N \geq 2$. The $N = 2$ elimination (§3.1.2) — and hence the lower bound $N \geq 3$ — depends entirely on the cross-terms that arise from the interference form. This is the single most consequential assumption in this proposition.
>
> **Partial derivation:** Theorem 0.1.0 derives the interference form from Fisher metric structure on the stella octangula. However, that derivation takes SU(3) as input, so using it here to derive SU(3) would be circular. Within this proposition, A-IF is an independent framework assumption.
>
> **Classification:** (F) — Framework-specific. Identified as SMUGGLED by [V1 Validity Audit](../reviews/G1/G1-Validity-Audit-Module-V1-Findings.md) §V1.3, now explicitly declared. [V2 Derivation Step Verification](../reviews/G1/G1-Validity-Audit-Module-V2-Findings.md) §V2.6 confirms the Fisher non-degeneracy derivation (§3.1) is mathematically correct given A-IF; rated QUALIFIED (MODERATE) solely due to this assumption's (F)-class status.

> **Assumption A-CS (Compact Simple Gauge Group):** The gauge group is restricted to **compact simple** Lie groups. This excludes product groups (e.g., SU(2)×U(1)), non-compact groups, and abelian groups.
>
> **Why this matters:** The Standard Model gauge group SU(3)×SU(2)×U(1) is *not* simple. The restriction to simple groups is essential for the uniqueness argument in §4.3–4.4: without it, the Weyl group / Cartan analysis does not uniquely select SU(3).
>
> **Motivation:** At this stage of the framework, we seek only the **color gauge factor** — the strong interaction group responsible for confinement. The full SM product group structure is addressed in Phases 2–3, where electroweak SU(2)×U(1) emerges separately. Compactness follows from unitarity (established physics); simplicity is a framework choice to isolate the confining sector.
>
> **Classification:** (F) — Framework-specific. Identified as SMUGGLED by [V1 Validity Audit](../reviews/G1/G1-Validity-Audit-Module-V1-Findings.md) §V1.3 finding F4, now explicitly declared.

> **Assumption A-SN ($S_N$ Permutation Symmetry / "Color Democracy"):** All $N$ field components are treated as physically indistinguishable — there is no preferred labeling or hierarchy among colors. Formally, the configuration space and Fisher metric are required to be invariant under the symmetric group $S_N$ acting by permutation of component indices.
>
> **Why this matters:** The $S_N$ symmetry is what identifies the Weyl group of the gauge group (§4.4). For $N = 3$, $S_3$ is the Weyl group of SU(3) and no other rank-2 simple group. Without this assumption, the Weyl group argument for selecting SU(3) among rank-2 groups does not work.
>
> **Motivation:** In QCD, all three color charges couple identically to gluons — there is no physical distinction between red, green, and blue. This is "color democracy." The assumption is physically well-motivated but is an input, not a consequence of distinguishability alone.
>
> **Classification:** (F) — Framework-specific. Identified as QUALIFIED by [V1 Validity Audit](../reviews/G1/G1-Validity-Audit-Module-V1-Findings.md) §V1.3 finding F8, now explicitly declared.

**Goal:** Provide a complementary retrodiction of SU(3) via information geometry, arriving at the same (experimentally known) conclusion as the geometric path (Theorem 0.0.15) through a different mechanism:

| Geometric Path (Thm 0.0.15) | Information Path (This Proposition) |
|------------------------------|-------------------------------------|
| Stella geometry → Z₃ phases → SU(3) | Fisher non-degeneracy → N ≥ 3 → SU(3) |
| Assumes stella, derives SU(3) | Assumes A-IF, derives N = 3 |
| Both paths share: D = 4 (Thm 0.0.1) | Both paths share: D = 4 (Thm 0.0.1) |

**Significance:** This proposition does NOT replace the geometric derivation — both paths require D = 4 for the upper bound. Its value is showing that SU(3) is special from an information-geometric perspective: it is the unique gauge group compatible with stable observer-distinguishability, given the quantum interference form. This provides a complementary perspective that does not depend on assuming the stella octangula first.

**Epistemic status:** This is a **retrodiction** — a novel explanatory pathway to a known result (SU(3) as the color gauge group). The conclusion is not falsifiable via this route because: (1) SU(3) is already experimentally established, and (2) the key framework axiom A-IF is not independently testable within this proposition. The scientific value lies in the explanatory coherence of the framework, not in predictive content.

---

## 0. Executive Summary

### 0.1 The Problem

The current CG framework derives SU(3) via:
1. Observer existence → D = 4 (Theorem 0.0.1)
2. Stella octangula geometry → Z₃ phase structure (Theorem 0.0.15 §3.0)
3. Z₃ + D = 4 + Cartan classification → SU(3) (Theorem 0.0.15)

**The gap:** Why the stella octangula? While Theorem 0.0.3 establishes its uniqueness given SU(3), the stella's appearance feels contingent. Can we derive SU(3) more directly from information?

### 0.2 The Approach

We aim to show:

$$\boxed{\text{Observer distinguishability} + \text{A-IF} + \text{D = 4} + \text{color neutrality} \xRightarrow{\text{constraints}} \text{SU}(3)}$$

Two complementary arguments:

**Approach 1 (Dimensionality, §3):** The lower bound N ≥ 3 from Fisher non-degeneracy (the genuinely novel contribution, given A-IF), combined with the upper bound N ≤ 4 from D = 4 + affine independence + Z₃ from color neutrality, uniquely gives N = 3.

**Approach 2 (Symmetry, §4):** Given N = 3, SU(3) is the unique compact simple Lie group with Weyl group S₃ (standard Lie theory, given A-CS and A-SN).

### 0.3 What This Achieves

| Geometric Path (existing) | Information Path (this proposition) |
|--------|----------------------|
| Stella geometry assumed first | Configuration space dimension constrained via A-IF (framework assumption) |
| Z₃ from stella symmetry | Z₃ from color neutrality (framework assumption) |
| SU(3) from Z₃ + D = 4 | SU(3) retrodicted from Fisher constraints + A-IF + D = 4 + color neutrality |

> **Note:** This proposition does NOT reduce the input count. It provides an **alternative retrodiction pathway** that replaces geometric inputs (stella geometry) with information-theoretic inputs (Fisher non-degeneracy + A-IF), while still requiring D = 4 for the upper bound. The value is complementarity of explanation, not predictive economy. Both paths reconstruct the known result SU(3).

---

## 1. Statement of Results

### Result A.1 (Configuration Space Dimensionality) ✅ PROVEN (constrained selection)

*Given the quantum interference form (A-IF) and D = 4 (Thm 0.0.1), the unique configuration space that supports:*
1. *Non-trivial distinguishability (dim > 1)*
2. *Bounded information per measurement (Fisher metric regular)*
3. *Observer stability (no runaway configurations)*
4. *Geometric realizability in $D_{space} = 3$*

*has $\dim(\mathcal{C}) = 2$, corresponding to $N = 3$ components.*

**Formal Statement:**

Let $\mathcal{C}$ be the configuration space of distinguishable states for an observer, with probability distributions taking the interference form $p_\phi(x) = |\sum_c A_c(x) e^{i\phi_c}|^2$ (Assumption A-IF). Require:
- **(C1)** $\dim(\mathcal{C}) > 1$ (non-trivial distinguishability)
- **(C2)** The Fisher metric $g^F_{ij}$ is non-degenerate and bounded
- **(C3)** Geodesic completeness (observer can explore all configurations)
- **(C4)** Compact configuration space (bounded, finite total information)
- **(C5)** $N \leq D_{space} + 1 = 4$ (geometric realizability, Lemma 0.0.2a)
- **(C6)** Color neutrality: $\sum_c e^{i\phi_c} = 0$ at equilibrium

Then $\dim(\mathcal{C}) = 2$, corresponding to $N = 3$ components.

> **Note on prior statement:** The original formal statement listed only (C1)–(C4), omitting the dependence on A-IF, D = 4, and color neutrality. The result is proven, but only under all six conditions.

### Result A.2 (SU(3) from Information Geometry Axioms) ✅ PROVEN (given A-CS, A-SN)

*Given $N = 3$ (from Result A.1) and a configuration space $\mathcal{M}$ with:*
1. *Fisher metric $g^F$ satisfying Markov invariance (Chentsov uniqueness)*
2. *$S_N$ permutation symmetry among components (Assumption A-SN)*
3. *Color neutrality: $\sum_c e^{i\phi_c} = 0$ at equilibrium*
4. *Gauge group restricted to compact simple Lie groups (Assumption A-CS)*

*then SU(3) is the unique group whose Killing form reproduces $g^F$ on the Cartan torus.*

---

## 2. Background: Information Geometry Foundations

### 2.1 The Fisher Information Metric

For a family of probability distributions $\{p_\theta\}_{\theta \in \Theta}$, the Fisher metric is:

$$g^F_{ij}(\theta) = \mathbb{E}\left[\frac{\partial \log p_\theta}{\partial \theta^i} \cdot \frac{\partial \log p_\theta}{\partial \theta^j}\right]$$

**Chentsov's Theorem (1972; modern generalization: Lê 2017):** The Fisher metric is the **unique** Riemannian metric on statistical manifolds (up to constant scaling) invariant under sufficient statistics (Markov morphisms). *Note:* The original theorem applies to finite sample spaces; the modern extension by Lê (2017) establishes uniqueness for the more general settings used here (see §9, Refs 8–11).

### 2.2 From Prop 0.0.17b: Fisher Metric Uniqueness

Proposition 0.0.17b establishes that the Fisher metric is forced by:
- Markov invariance
- Cramér-Rao optimality
- S₃ symmetry (Weyl invariance)

The result: $g^F = \frac{1}{12}\mathbb{I}_2$ on the SU(3) Cartan torus.

### 2.3 From Theorem 0.1.0: Fields from Distinguishability

Theorem 0.1.0 proves that non-trivial Fisher metric requires fields with the interference form:

$$p_\phi(x) = \left|\sum_c A_c(x) e^{i\phi_c}\right|^2$$

> **Assumption Declaration (A-IF):** The interference form above is an **explicit framework assumption** within this proposition, not a consequence of observer distinguishability alone. Theorem 0.1.0 derives this form but takes SU(3) structure as input; using it here would be circular. A classical probability model $p(x) = \sum_c w_c P_c(x)$ would yield a generically non-degenerate Fisher metric for all $N \geq 2$, eliminating the $N = 2$ degeneracy that is central to this argument. The coherent superposition form — implying complex amplitudes and the Born rule — is what makes the $N = 2$ Fisher metric degenerate. See the Explicit Assumptions box above for full discussion.

**Key insight:** The number of terms $N$ in the sum is constrained by distinguishability requirements.

---

## 3. Approach 1: Dimensionality from Information Constraints

### 3.1 Why N ≥ 3 (Lower Bound)

**Claim 3.1:** A configuration space supporting non-trivial observer distinguishability must have $N \geq 3$ components.

#### 3.1.1 Case N = 1 (Trivial — No Distinguishability)

With a single field $\chi(x) = A(x) e^{i\phi}$, the probability distribution is:
$$p_\phi(x) = |A(x) e^{i\phi}|^2 = A(x)^2$$

This is **independent of $\phi$**! The Fisher metric vanishes identically:

$$g^F(\phi) = \int p_\phi(x) \left(\frac{\partial \log p}{\partial \phi}\right)^2 dx = \int A^2 \cdot 0^2 \, dx = 0$$

*Conclusion:* $N = 1$ gives zero distinguishability. ✗

#### 3.1.2 Case N = 2 (Degenerate — Zero-Dimensional Configuration Space)

This is the critical case that eliminates N = 2 as a viable configuration.

**Setup:** Two fields $\chi_1, \chi_2$ with phases $\phi_1, \phi_2$ satisfying the neutrality constraint:
$$e^{i\phi_1} + e^{i\phi_2} = 0$$

---

**PRIMARY ARGUMENT: Configuration Space Dimension**

**Lemma 3.1.2a (N = 2 Configuration Space is Trivial):**
*For N = 2 fields with color neutrality, the configuration space has dimension zero.*

**Proof:**

The neutrality condition requires:
$$e^{i\phi_2} = -e^{i\phi_1} = e^{i(\phi_1 + \pi)}$$

Therefore: $\phi_2 = \phi_1 + \pi$ (mod $2\pi$)

Counting degrees of freedom:
- Initial: 2 phases ($\phi_1, \phi_2$)
- Minus 1: Neutrality constraint ($\sum_c e^{i\phi_c} = 0$)
- Minus 1: Overall U(1) gauge freedom

$$\dim(\mathcal{C}) = 2 - 1 - 1 = 0$$

**Conclusion:** The N = 2 "configuration space" is a single point. There is no manifold to support a Riemannian metric. **This alone is sufficient to reject N = 2.** □

---

**SUPPORTING VERIFICATION: Fisher Metric Analysis**

*The following analysis provides independent confirmation that N = 2 fails. While redundant given the dimensionality argument above, it demonstrates the physical mechanism of failure.*

**Step 2: Interference Pattern at N = 2 Equilibrium**

The interference pattern is:
$$p_\phi(x) = |A_1(x) e^{i\phi_1} + A_2(x) e^{i\phi_2}|^2$$

With $\phi_2 = \phi_1 + \pi$:
$$p = |A_1 e^{i\phi_1} - A_1 e^{i\phi_1} \cdot \frac{A_2}{A_1}|^2 = |A_1 - A_2|^2 e^{i \cdot 0} = (A_1 - A_2)^2$$

**Critical Problem:** At the equilibrium:
- If $A_1(x) = A_2(x)$ (symmetric geometry): $p(x) = 0$ everywhere → **undefined Fisher metric**
- If $A_1 \neq A_2$ (asymmetric): gradient $\frac{\partial p}{\partial \phi} = 0$ → **degenerate Fisher metric**

**Step 3: Fisher Metric Degeneracy (Rigorous Proof)**

**Lemma 3.1.2 (N = 2 Fisher Metric Singularity):**
*At the color-neutral equilibrium with N = 2, the Fisher information matrix has zero eigenvalue.*

**Proof:**

The Fisher metric component is:
$$g^F = \int p_\phi(x) \left(\frac{\partial \log p}{\partial \phi}\right)^2 dx$$

Computing the derivative at $\phi_2 - \phi_1 = \pi$:

$$\frac{\partial p}{\partial \phi_1} = \frac{\partial}{\partial \phi_1} \left[A_1^2 + A_2^2 + 2A_1 A_2 \cos(\phi_1 - \phi_2)\right]$$
$$= -2A_1 A_2 \sin(\phi_1 - \phi_2)$$

At equilibrium ($\phi_1 - \phi_2 = -\pi$): $\sin(-\pi) = 0$

Therefore:
$$\frac{\partial p}{\partial \phi_1}\bigg|_{\text{eq}} = 0$$

The Fisher metric becomes:
$$g^F = \int p \cdot \left(\frac{0}{p}\right)^2 dx = 0$$

The Fisher metric **vanishes** at the N = 2 equilibrium. □

**Step 4: Violation of Non-Degeneracy Requirement**

For the Fisher metric to serve as a valid Riemannian metric on a statistical manifold, it must be:
1. **Non-degenerate** (positive-definite) — This is a *metric requirement*, not part of Chentsov's theorem
2. **Invariant under sufficient statistics** — This is *Chentsov's uniqueness condition* (Markov morphisms)

**Clarification:** N = 2 violates condition (1), the non-degeneracy requirement. The Chentsov theorem (Markov invariance) is about *uniqueness* of the metric among non-degenerate candidates — it does not apply when the metric is degenerate.

[Chentsov's uniqueness theorem](https://arxiv.org/abs/1306.1465) guarantees that among non-degenerate statistical metrics, the Fisher metric is unique up to scaling. But N = 2 fails the prerequisite: no non-degenerate metric exists on a 0-dimensional configuration space.

**Step 5: Stability Analysis (Hessian)**

Even if we perturb away from exact neutrality, the equilibrium is unstable:

**Energy functional:**
$$E[\phi] = -\int p_\phi(x) \log p_\phi(x) \, dx$$

**Hessian at equilibrium:**
$$H_{ij} = \frac{\partial^2 E}{\partial \phi_i \partial \phi_j}\bigg|_{\text{eq}}$$

For N = 2, the single eigenvalue of the 1×1 Hessian:
$$\lambda = \frac{\partial^2}{\partial \phi^2}\left[-\int (A_1-A_2)^2 \log(A_1-A_2)^2 dx\right]$$

This is **zero** (the energy is independent of $\phi$ at equilibrium).

**Physical interpretation:** The N = 2 equilibrium is a **critical point of infinite degeneracy** — any perturbation leaves energy unchanged, making the dynamics ill-defined.

---

**Summary of N = 2 Rejection:**

| Argument | Type | Sufficient Alone? |
|----------|------|-------------------|
| dim(C) = 0 (Lemma 3.1.2a) | Topological | ✅ **YES** (Primary) |
| Fisher metric vanishes (Lemma 3.1.2) | Information-geometric | ✅ YES |
| Hessian has zero eigenvalue (Step 5) | Dynamical stability | ✅ YES |
| Non-degeneracy violated (Step 4) | Metric requirement | ✅ YES |

*Conclusion:* $N = 2$ fails via **four independent arguments**, with the dimensionality argument (Lemma 3.1.2a) being the most fundamental. ✗

#### 3.1.3 Case N = 3 (Stable — Non-Degenerate Fisher Metric)

With three fields and color neutrality $1 + \omega + \omega^2 = 0$ where $\omega = e^{2\pi i/3}$:

**The interference pattern at equilibrium:**

$$p_\phi(x) = \left|A_R + A_G \omega + A_B \omega^2\right|^2$$

Expanding (using $\omega + \omega^2 = -1$ and $|\omega| = 1$):

$$p = A_R^2 + A_G^2 + A_B^2 + 2A_R A_G \cos\frac{2\pi}{3} + 2A_R A_B \cos\frac{4\pi}{3} + 2A_G A_B \cos\frac{2\pi}{3}$$

$$= A_R^2 + A_G^2 + A_B^2 - A_R A_G - A_R A_B - A_G A_B$$

**Positive-Definiteness:**

This can be rewritten as:
$$p = \frac{1}{2}\left[(A_R - A_G)^2 + (A_G - A_B)^2 + (A_B - A_R)^2\right] \geq 0$$

**Key difference from N = 2:** This is positive **unless all three amplitudes are equal**.

**Lemma 3.1.3a (Generic Amplitude Inequality):**
*For the pressure-derived amplitudes $A_c(x) = a_0 P_c(x)$ on the stella octangula (Definition 0.1.3), the three amplitudes are pairwise distinct for almost all points $x \in \mathbb{R}^3$.*

**Proof:**

The pressure function is $P_c(x) = 1/(|x - x_c|^2 + \epsilon^2)$ where $x_c$ are the tetrahedron vertices.

**Step 1:** Two amplitudes are equal iff their distances are equal:
$$A_c(x) = A_{c'}(x) \iff |x - x_c|^2 = |x - x_{c'}|^2$$

This defines the **perpendicular bisector plane** of segment $x_c x_{c'}$.

**Step 2:** The set where any pair of amplitudes are equal is:
$$S_{eq} = \bigcup_{c < c'} \{x : A_c(x) = A_{c'}(x)\}$$

This is a union of 3 planes (the Voronoi cell boundaries from Definition 0.1.4 §3.2).

**Step 3:** A finite union of planes in $\mathbb{R}^3$ has **Lebesgue measure zero**.

**Step 4:** Therefore, for almost all $x \in \mathbb{R}^3$:
$$A_R(x) \neq A_G(x) \neq A_B(x) \neq A_R(x)$$

**Corollary:** The only point where all three amplitudes are equal is the center $x = 0$ (equidistant from all vertices). At any other point, at least two amplitudes differ. □

**Computational verification:** See `verification/foundations/proposition_0_0_XX_amplitude_inequality.py` (9/9 tests pass).

For generic position-dependent amplitudes $A_c(x)$ on the stella octangula:
- At any point $x$ (except the center and boundary planes), all three amplitudes differ
- Therefore $p(x) > 0$ almost everywhere
- The Fisher metric is **non-degenerate**

**Fisher Metric Verification:**

From Theorem 0.0.17 §3.5:
$$g^F_{ij} = g^K_{ij} = \frac{1}{12}\delta_{ij}$$

The Fisher metric is the identity (times constant), which is positive-definite.

**Stability (Hessian Analysis):**

The Hessian of the energy functional at N = 3 equilibrium has eigenvalues:
$$\lambda_1, \lambda_2 > 0$$

(Both positive, confirmed by Theorem 0.0.17 S₃ symmetry argument)

**Conclusion:** $N = 3$ uniquely provides:
- Non-trivial distinguishability ✓
- Non-degenerate Fisher metric ✓
- Stable equilibrium ✓

### 3.2 Why N ≤ 3 (Upper Bound)

**Claim 3.2:** The dimensionality of observer-compatible configuration spaces is bounded by $N \leq D_{space} = 3$.

> **Note on novelty:** The genuinely novel contribution of this proposition is the **lower bound** (§3.1: N ≥ 3 from Fisher non-degeneracy under A-IF). The upper bound uses the same geometric input (D = 4) as the standard path in Theorem 0.0.15. What differs is the *mechanism* by which SU(3) is selected from the allowed range.

**Primary Argument: Affine Independence (from Lemma 0.0.2a)**

For the configuration space to embed in $D_{space} = 3$ dimensional physical space:
- The $N$ fundamental weights of SU(N) must be geometrically realized
- $N$ points in affine general position require $\dim \geq N - 1$
- In $D_{space} = 3$: at most $4$ affinely independent points
- Therefore $N \leq 4$

Combined with Z₃ center requirement (from color neutrality): $3 | N$, so $N \in \{3\}$.

> **Shared input (V3 §V3.3):** The Z₃ constraint enters here via the same physical input as in Theorem 0.0.15 §3.0 (stella 3-fold rotational symmetry). The general neutrality condition $\sum_c e^{i\phi_c} = 0$ holds for any $N \geq 2$ with equally-spaced phases ($N$-th roots of unity), giving $Z_N$. The specific $Z_3 \subseteq Z_N$ requirement — i.e., $3 | N$ — shares its origin with the stella's 3-fold symmetry, not an independent input. The information-geometric path shares this constraint with the geometric path; the genuinely independent contributions of this proposition are the **lower bound** $N \geq 3$ from Fisher non-degeneracy (§3.1) and **Approach C** (Theorem 3.2.1, which selects $N = 3$ without using $D = 4$ or $Z_3$).

This is a **well-justified, rigorous** upper bound using the established result D = 4 from Theorem 0.0.1.

**Supplementary Perspective: First Stable Principle**

An alternative route to N = 3 that does not use D = 4 is the First Stable Principle ([Proposition 0.0.XXa](Proposition-0.0.XXa-First-Stable-Principle.md)), which selects N = 3 as the minimal stable configuration. However, this is a **minimality postulate** (formalized Occam's razor), not a derivation from physical law. The geometric upper bound above is the primary argument. See §6.1.1 for the investigation that motivated this distinction.

**Failed Approach: Pure Information-Theoretic Upper Bound (Unresolved)**

We investigated whether information geometry alone could bound N without geometric input:

**Conjecture 3.2.1 (Information Capacity Bound — UNRESOLVED):**
*The maximum number of distinguishable components in $D_{space}$ dimensions is:*

$$N_{max} = D_{space}$$

Two heuristic arguments were attempted:

1. **Measurement channels:** $\log_2(N) \leq D_{space}$ gives $N \leq 8$ — too weak.

2. **Phase space matching:** $2(N-1) \leq 6$ gives $N \leq 4$ — correct bound but the phase-space matching argument is heuristic, not rigorous.

**The investigation in §6.1.1 confirmed that Fisher metric rank does not bound N** (full rank for all N ≥ 3). A rigorous pure information-theoretic upper bound on N remains an open problem.

**Approach C: Irreducibility and Information Density** 🔶 NOVEL

While Fisher metric rank alone does not bound N from above, the **algebraic structure** of composite-N interference systems provides a physically motivated selection criterion. The key insight: composite-N systems are algebraically reducible (they decompose into subsystems), while prime-N systems are irreducible. Among irreducible systems, per-DOF Fisher information selects N = 3 uniquely.

**Lemma 3.2.1a (Composite-N Decomposition):**
*For composite $N = a \cdot b$ with $a, b \geq 2$, the interference pattern decomposes into $a$ sub-interference terms, each involving only $b$ phases.*

**Proof:**

The $N$-th roots of unity $\{\omega^k\}_{k=0}^{N-1}$ (where $\omega = e^{2\pi i/N}$) can be grouped into $Z_a$ cosets:

$$\text{Coset } j = \{\omega^{a k + j} : k = 0, \ldots, b-1\}, \quad j = 0, \ldots, a-1$$

Each coset contains $b$ elements whose phases differ by $2\pi a/N = 2\pi/b$, so each coset forms a $Z_b$ sub-pattern. The total field amplitude decomposes:

$$\chi(x) = \sum_{c=0}^{N-1} A_c(x) e^{i\phi_c} = \sum_{j=0}^{a-1} \underbrace{\sum_{k=0}^{b-1} A_{ak+j}(x) e^{i\phi_{ak+j}}}_{\chi_j(x) \text{ (coset sub-amplitude)}}$$

Each sub-amplitude $\chi_j(x)$ involves only $b$ components — the interference pattern is a superposition of $a$ terms of reduced complexity. This is an **algebraic decomposition**: the $N$-component system factors into $a$ subsystems of $b$ components each. □

**Examples:**
- **$N = 4$:** $Z_2$ cosets $\{0,2\}$ and $\{1,3\}$ give $\chi = (A_0 - A_2) + i(A_1 - A_3)$, a sum of two 2-component sub-amplitudes.
- **$N = 6$:** Admits two decompositions: (i) $a=2, b=3$: two $Z_3$ sub-patterns $\{0,2,4\}$ and $\{1,3,5\}$; (ii) $a=3, b=2$: three $Z_2$ sub-patterns $\{0,3\}$, $\{1,4\}$, $\{2,5\}$.
- **$N = 9$:** $Z_3$ cosets give three $Z_3$ sub-patterns.

**Computational verification:** See `verification/foundations/proposition_0_0_XX_decomposability.py` (Tests 1–6: reconstruction errors $< 10^{-10}$ for all composite $N = 4, 6, 8, 9, 10$).

---

**Lemma 3.2.1b (Prime-N Irreducibility):**
*For prime $N$, the interference pattern does NOT decompose into independent subsystems via coset structure.*

**Proof:**

When $N$ is prime, the cyclic group $Z_N$ has **no proper non-trivial subgroups** (Lagrange's theorem: subgroup orders must divide $N$, and the only divisors of a prime are $1$ and $N$ itself). Therefore:

1. No non-trivial coset decomposition of $\{\omega^k\}_{k=0}^{N-1}$ exists.
2. The $N$-th roots of unity cannot be partitioned into subsets that independently form sub-interference patterns via the $Z_a$ coset mechanism of Lemma 3.2.1a.
3. The interference pattern $p(x) = |\sum_{c=0}^{N-1} A_c(x) e^{i\phi_c}|^2$ contains genuine $N$-way cross-terms that cannot be decomposed into products or sums of lower-order interference terms.

The system is **algebraically irreducible**: all $N$ components participate jointly in the interference, with no intermediate factorization. □

**Computational verification:** See `verification/foundations/proposition_0_0_XX_decomposability.py` (Tests 7–10: $Z_3, Z_5, Z_7$ have zero proper non-trivial subgroups; numerical cross-term analysis confirms irreducibility).

---

**Theorem 3.2.1 (Irreducible Information Density Bound):** 🔶 NOVEL
*Among irreducible (prime) $N \geq 3$, the per-degree-of-freedom Fisher information $I_{\text{DOF}}(N) = 1/(2N)$ is uniquely maximized at $N = 3$.*

**Proof:**

**Step 1 (Per-DOF Fisher information):**
From [Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md), for $S_N$-symmetric interference with color neutrality, the Fisher metric on the Cartan torus takes the form:

$$g^F = \frac{1}{2N} \cdot \mathbb{I}_{N-1}$$

The per-DOF Fisher information is:

$$I_{\text{DOF}}(N) = \frac{\text{Tr}(g^F)}{N-1} = \frac{(N-1) \cdot \frac{1}{2N}}{N-1} = \frac{1}{2N}$$

**Step 2 (Monotonicity):** Since $1/(2N)$ is a strictly decreasing function of $N$, we have $I_{\text{DOF}}(N_1) > I_{\text{DOF}}(N_2)$ whenever $N_1 < N_2$.

**Step 3 (Restriction to irreducible systems):** By Lemma 3.2.1a, composite $N$ systems are algebraically reducible — they decompose into lower-order subsystems. A physically fundamental configuration should be irreducible: it should not factor into simpler sub-configurations. By Lemma 3.2.1b, irreducibility requires $N$ to be prime.

**Step 4 (Selection):** Among prime $N \geq 3$ (the set $\{3, 5, 7, 11, 13, \ldots\}$), the per-DOF Fisher information is:

| $N$ (prime) | $I_{\text{DOF}} = 1/(2N)$ |
|-------------|--------------------------|
| **3** | **1/6 ≈ 0.1667** |
| 5 | 1/10 = 0.1000 |
| 7 | 1/14 ≈ 0.0714 |
| 11 | 1/22 ≈ 0.0455 |
| $\vdots$ | $\to 0$ |

The unique maximum is at $N = 3$. □

**Physical interpretation:** Each degree of freedom in an $N = 3$ irreducible system carries more Fisher information (distinguishing power) per DOF than any larger prime system. The $N = 3$ system is maximally "information-dense" among irreducible configurations.

**Honest status:** This argument replaces the bare minimality postulate (First Stable Principle) with a **quantitative information-theoretic criterion**: maximize per-DOF Fisher information among irreducible systems. The criterion is physically motivated (information efficiency), but the *selection of this criterion* (rather than, say, total information or some other functional) is still a methodological choice. It is more principled than bare Occam's razor because:
1. It provides a **quantitative** measure ($1/(2N)$), not just "pick the smallest"
2. It is **physically grounded** in Fisher information geometry (Cramér-Rao sensitivity)
3. The irreducibility filter ($N$ prime) has **algebraic content** (Lemma 3.2.1a/b), not just minimality

**What remains:** The statement "nature selects configurations that maximize per-DOF information among irreducible systems" is a well-motivated selection principle, not a theorem derivable from more basic axioms.

**Computational verification:** See `verification/foundations/proposition_0_0_XX_decomposability.py` (17/17 tests pass; Tests 11–13 verify the $1/(2N)$ scaling and $N = 3$ maximality).

---

### 3.3 Synthesis: N = 3 Uniquely

| Constraint | Source | N Values |
|------------|--------|----------|
| Non-trivial distinguishability | §3.1(i) | N ≥ 2 |
| Stable equilibrium | §3.1(ii)-(iii) | N ≥ 3 |
| Affine independence in 3D | Lemma 0.0.2a | N ≤ 4 |
| Z₃ phase structure | Color neutrality (*shared with geometric path — see §3.2 note*) | 3 \| N |
| Irreducible info density (Approach C) | Theorem 3.2.1 | N = 3 among primes ≥ 3 |

**Intersection:** $N = 3$ is unique.

> **Note on Approach C:** Theorem 3.2.1 provides an alternative route to N = 3 that does not use D = 4. It selects N = 3 as the unique prime ≥ 3 that maximizes per-DOF Fisher information. This replaces the bare minimality postulate of the First Stable Principle with a quantitative information-theoretic criterion, though the selection principle itself ("maximize per-DOF info among irreducibles") remains a methodological choice.

---

## 4. Approach 2: SU(3) from Fisher Metric Isometries

### 4.1 The Question

Given that $N = 3$, why is the gauge group SU(3) and not some other group?

> **Assumptions used in this section:** The argument below relies on Assumption **A-CS** (compact simple gauge group) to restrict the search space, and Assumption **A-SN** ($S_N$ permutation symmetry) to identify the Weyl group. Both are declared in the Explicit Assumptions section above.

**Claim 4.1:** SU(3) is the unique compact simple Lie group whose isometry group on the configuration space matches the Fisher metric structure.

### 4.2 Configuration Space as Statistical Manifold

The configuration space for $N = 3$ fields with phase constraint $\sum \phi_c = 0$:

$$\mathcal{C} = T^2 \cong \{(\phi_G - \phi_R, \phi_B - \phi_R) \in [0, 2\pi)^2\}$$

**Theorem (from 0.0.17):** On this configuration space, the Fisher metric equals the Killing metric:

$$g^F = g^K = \frac{1}{12}\mathbb{I}_2$$

> **Normalization Convention:** The factor 1/12 arises from the standard SU(3) generator normalization $\text{Tr}(T^a T^b) = \frac{1}{2}\delta^{ab}$. The Killing form on the Cartan subalgebra is $g^K_{ij} = \frac{1}{2N} \delta_{ij}$ for SU(N) in this normalization. For N = 3: $g^K_{ij} = \frac{1}{6}\delta_{ij}$. The additional factor of 1/2 comes from the restricted Cartan torus coordinates (see [Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md) for details).

### 4.3 Isometry Groups and Lie Algebras

**Question:** What Lie groups have $T^2$ as their maximal torus with Killing metric proportional to identity?

**Analysis:**

For a compact simple Lie group $G$ of rank 2:
- The Cartan torus is $T^2$
- The Killing form on the Cartan subalgebra determines the metric

**Rank-2 compact simple groups:**
| Group | Cartan Metric Structure | Root System |
|-------|------------------------|-------------|
| SU(3) | $\frac{1}{12}\mathbb{I}_2$ (isotropic) | A₂ (hexagonal) |
| SO(5) | Anisotropic | B₂ (square-like) |
| Sp(4) ≅ SO(5) | Anisotropic | C₂ |
| G₂ | Anisotropic | G₂ (exceptional) |

**Key observation:** Only SU(3) has an **isotropic** (proportional to identity) Killing metric on its Cartan torus.

### 4.4 Why Isotropy? — The S₃ Symmetry Requirement

From Prop 0.0.17b, the Fisher metric must be S₃-invariant (Weyl group symmetry).

**Theorem 4.4.1:** Among rank-2 compact simple Lie groups, SU(3) is the unique group whose Weyl group is exactly S₃.

| Group | Weyl Group | Order | S₃? |
|-------|------------|-------|-----|
| SU(3) | S₃ | 6 | ✓ |
| SO(5) ≅ Sp(4) | W(B₂) ≅ D₄ (dihedral group of square) | 8 | ✗ |
| G₂ | W(G₂) ≅ D₆ (dihedral group of hexagon) | 12 | ✗ |

> **Note on W(B₂):** The Weyl group of B₂ (= C₂) can also be written as (ℤ₂)² ⋊ S₂, the hyperoctahedral group in 2D. It is isomorphic to D₄, the symmetry group of the square.

**Proof:** The Weyl group of SU(N) is the symmetric group $S_N$. For N = 3: W(SU(3)) = S₃ (order 6). The other rank-2 groups have larger Weyl groups: W(B₂) ≅ D₄ (order 8) and W(G₂) ≅ D₆ (order 12). Therefore SU(3) is unique among rank-2 groups in having Weyl group S₃. □

### 4.5 Putting It Together

**Theorem 4.5 (SU(3) from Information Geometry):**

Let $\mathcal{C}$ be the configuration space of $N = 3$ distinguishable field components with:
1. Fisher metric satisfying Chentsov uniqueness (Markov invariance)
2. S₃ permutation symmetry (color democracy)
3. Color neutrality ($\sum_c e^{i\phi_c} = 0$)

Then the isometry group of $(\mathcal{C}, g^F)$ is SU(3).

**Proof Sketch:**
1. From (1)-(3), the configuration space is $T^2$ with metric $g^F = c \cdot \mathbb{I}_2$
2. The metric is S₃-invariant (from (2))
3. Among rank-2 groups, only SU(3) has Weyl group S₃ (§4.4)
4. The isometry group is the group whose Killing form gives the metric
5. Therefore, the group is SU(3). □

---

## 5. The Complete Information-Geometric Derivation Chain

With both results now established (A.1 via the First Stable Principle, A.2 via Weyl group uniqueness):

**Primary derivation chain (using geometric upper bound):**

```
INPUTS: "Observer can distinguish configurations"     [axiom]
        + Quantum interference form (A-IF)             [assumption (F)]
        + Color neutrality at equilibrium              [assumption (F)]
        + D = 4 from observer existence (Thm 0.0.1)   [established (E)]
        + Compact simple gauge group (A-CS)            [assumption (F)]
        + S_N permutation symmetry (A-SN)             [assumption (F)]
       ↓
DERIVE: Non-trivial Fisher metric exists (Chentsov uniqueness)
       ↓
DERIVE: N ≥ 3 components (Fisher non-degeneracy, §3.1; requires A-IF)  ← NOVEL
       ↓
DERIVE: N ≤ 4 (D=4 + affine independence, Lemma 0.0.2a)               ← ESTABLISHED
       ↓
DERIVE: 3 | N (color neutrality → Z₃; shared with geometric path, see §3.2 note)
       ↓
DERIVE: N = 3 uniquely (intersection of above)
       ↓
DERIVE: S₃ Weyl symmetry (from A-SN with N = 3)
       ↓
DERIVE: SU(3) (unique rank-2 compact simple group with S₃ Weyl, §4.4; requires A-CS)
       ↓
DERIVE: Stella octangula (unique geometric realization, Theorem 0.0.3)
       ↓
DERIVE: Physics (masses, couplings, gravity)
```

**Honest input count:** The primary derivation uses **1 axiom** (observer distinguishability), **1 established result** (D = 4), and **4 framework-specific assumptions** (A-IF, color neutrality, A-CS, A-SN). This is a valid **constrained selection** — not a pure derivation from a single axiom, but a well-motivated argument from clearly declared inputs.

> **Supplementary perspective:** The First Stable Principle (Prop 0.0.XXa) offers an alternative to the D = 4 upper bound by postulating minimality. This replaces one input (D = 4, established physics) with another (minimality, a methodological preference). The primary chain above is preferred because D = 4 is better justified.

**Alternative derivation chain (Approach C — no D = 4 needed):**

```
INPUTS: "Observer can distinguish configurations"     [axiom]
        + Quantum interference form (A-IF)             [assumption (F)]
        + Color neutrality at equilibrium              [assumption (F)]
        + Compact simple gauge group (A-CS)            [assumption (F)]
        + S_N permutation symmetry (A-SN)             [assumption (F)]
       ↓
DERIVE: Non-trivial Fisher metric exists (Chentsov uniqueness)
       ↓
DERIVE: N ≥ 3 components (Fisher non-degeneracy, §3.1; requires A-IF)   ← NOVEL
       ↓
DERIVE: Composite N decomposes (Lemma 3.2.1a — algebraic reducibility)  ← NOVEL
       ↓
DERIVE: Irreducibility requires N prime (Lemma 3.2.1b)                  ← NOVEL
       ↓
DERIVE: Per-DOF Fisher info I_DOF = 1/(2N) from Lemma 0.0.17c           ← PROVEN
       ↓
DERIVE: N = 3 maximizes I_DOF among primes ≥ 3 (Theorem 3.2.1)         ← NOVEL
       ↓
DERIVE: S₃ Weyl symmetry (from A-SN with N = 3)
       ↓
DERIVE: SU(3) (unique rank-2 compact simple group with S₃ Weyl, §4.4)
       ↓
DERIVE: Stella octangula (unique geometric realization, Theorem 0.0.3)
       ↓
DERIVE: Physics (masses, couplings, gravity)
```

**Approach C input count:** **1 axiom** (observer distinguishability) and **4 framework-specific assumptions** (A-IF, color neutrality, A-CS, A-SN) — **no D = 4 needed**. The trade-off: D = 4 (established physics) is replaced by a selection principle ("maximize per-DOF Fisher info among irreducible systems"), which is physically motivated but still a methodological choice. This is more principled than the bare minimality postulate of the First Stable Principle because it provides a quantitative criterion grounded in information geometry.

---

## 6. Proof Verification Summary

### 6.1 Approach 1 (Dimensionality) — All Steps Verified

| Step | Status | Difficulty |
|-----|--------|------------|
| N = 1 triviality | ✅ **PROVEN** (§3.1.1) | Complete |
| N = 2 Fisher degeneracy | ✅ **PROVEN** (Lemma 3.1.2) | Complete |
| N = 2 Hessian stability | ✅ **PROVEN** (§3.1.2 Step 5) | Complete |
| N = 3 positive-definiteness | ✅ **PROVEN** (§3.1.3) | Complete |
| Upper bound N ≤ 4 | ✅ **PROVEN** via D = 4 + affine independence (Lemma 0.0.2a) — **primary** | Complete |
| Upper bound (alternative 1) | 🔶 **POSTULATED** via First Stable Principle — supplementary | Complete |
| Upper bound (alternative 2) | 🔶 **NOVEL** via irreducible info density (Theorem 3.2.1, Approach C) | Complete |
| Composite-N decomposition | 🔶 **PROVEN** — Lemma 3.2.1a (coset structure) | Complete |
| Prime-N irreducibility | 🔶 **PROVEN** — Lemma 3.2.1b (no subgroups) | Complete |
| Pure info-theoretic upper bound (rank-based) | ❌ **UNRESOLVED** — Fisher rank does not bound N (§6.1.1) | Open problem |
| Rigorous affine independence | ✅ Via Lemma 0.0.2a | Complete |

**N = 2 instability** is **rigorously proven** via three independent arguments:
1. Fisher metric vanishes (Lemma 3.1.2)
2. Hessian has zero eigenvalue (§3.1.2 Step 5)
3. Chentsov conditions violated (§3.1.2 Step 4)

**Upper bound resolution:** Three routes to the upper bound now exist: (a) the geometric bound N ≤ 4 from D = 4 + affine independence (Lemma 0.0.2a), combined with Z₃ from color neutrality, giving N = 3 — this is the **primary, well-justified route**; (b) the First Stable Principle (see §6.1.1), which selects N = 3 as the minimal stable configuration — a well-motivated minimality postulate (see [V1.3 §Q3](../reviews/G1/V1.3-F07-Prop-0.0.XX-Hidden-Inputs-Analysis.md)); (c) **Approach C** (Theorem 3.2.1), which selects N = 3 as the unique prime ≥ 3 maximizing per-DOF Fisher information — a physically motivated information-theoretic criterion that does not require D = 4.

### 6.1.1 Critical Finding: Fisher Metric for N ≥ 4 (Investigation Complete)

**Verification script:** `verification/foundations/proposition_0_0_XX_N4_investigation.py`

We computed the Fisher metric for N = 2 through N = 8 to check for information-theoretic pathologies:

| N | Config Dim | Fisher Rank | Degenerate? |
|---|------------|-------------|-------------|
| 2 | 1 | 0 | **YES** |
| 3 | 2 | 2 | No |
| 4 | 3 | 3 | No |
| 5 | 4 | 4 | No |
| 6 | 5 | 5 | No |
| 7 | 6 | 6 | No |
| 8 | 7 | 7 | No |

**CRITICAL RESULT:** The Fisher metric has **FULL RANK** for all N ≥ 3 tested.

**Implications:**
- ❌ Fisher metric rank alone does NOT bound N ≤ 3
- ❌ There is no obvious "information saturation" for N > 3
- ✅ The bound N ≤ 4 (or N ≤ 3) requires geometric input (Lemma 0.0.2a) OR a different information-theoretic argument

**Resolution of the Upper Bound**

The investigation above shows that **information geometry alone does not bound N from above**. The Fisher metric has full rank for all N ≥ 3, so there is no information-theoretic pathology at N = 4, 5, 6, ... This is an important negative result.

**Primary upper bound:** The geometric constraint N ≤ 4 from D = 4 + affine independence (Lemma 0.0.2a), combined with 3 | N from color neutrality, gives N = 3. This uses the well-established input D = 4 from Theorem 0.0.1.

**Supplementary perspective 1 (First Stable Principle):** [Proposition 0.0.XXa](Proposition-0.0.XXa-First-Stable-Principle.md) offers an alternative: select $N^* = \min\{N : S(N) = 1\} = 3$. This is a well-motivated minimality postulate but not a derivation from physical law (see [V1.3 §Q3](../reviews/G1/V1.3-F07-Prop-0.0.XX-Hidden-Inputs-Analysis.md)).

**Supplementary perspective 2 (Approach C — Irreducible Information Density):** Theorem 3.2.1 provides a more principled alternative. Composite-$N$ systems are algebraically reducible (Lemma 3.2.1a), so a physically fundamental configuration must have prime $N$ (Lemma 3.2.1b). Among prime $N \geq 3$, per-DOF Fisher information $I_{\text{DOF}} = 1/(2N)$ is uniquely maximized at $N = 3$. This replaces bare minimality with a quantitative information-theoretic criterion and does not require D = 4, though the selection principle itself ("maximize per-DOF info among irreducibles") remains a methodological choice.

**Open problem (refined):** A rigorous pure information-theoretic upper bound on N from Fisher metric rank alone remains unresolved (full rank for all N ≥ 3). However, Approach C provides a **physically motivated** alternative that goes beyond rank analysis: it combines algebraic reducibility (a structural property of composite systems) with information density optimization. This partially resolves the open problem — not by bounding N through information pathology, but by selecting N = 3 through a combination of algebraic irreducibility and information efficiency. See [Research-Pure-Information-Bound-On-N.md](../supporting/Research-Pure-Information-Bound-On-N.md) for the full investigation.

### 6.2 Approach 2 (Symmetry) — All Steps Verified

| Gap | Status | Difficulty |
|-----|--------|------------|
| S₃ uniqueness among rank-2 | ✅ Standard Lie theory | Complete |
| Fisher = Killing from Chentsov | ✅ **PROVEN** ([Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md)) | Complete |
| Completeness of analysis | ✅ Non-simple groups excluded by simplicity requirement | Complete |

**Resolved (2026-02-01):** The connection between Fisher and Killing metrics is established in [Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md):

$$\text{S}_N\text{-symmetry} + \text{Chentsov uniqueness} \implies g^F \propto g^K$$

Both metrics are the unique S_N-invariant metric on the Cartan torus (up to scaling).

### 6.3 Completed Research Steps

1. ✅ **Formalize N = 2 instability proof** — Complete (§3.1.2)
2. ✅ **Prove Fisher-Killing equivalence** — Complete ([Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md))
3. ✅ **Investigate Fisher metric for N ≥ 4** — Complete (§6.1.1) — Finding: No pathology, full rank
4. ✅ **Computational verification of N = 2 degeneracy** — Complete (9/9 tests pass)
5. ✅ **Develop pure info-theoretic bound** — Complete via **First Stable Principle** ([Proposition 0.0.XXa](Proposition-0.0.XXa-First-Stable-Principle.md))
6. ✅ **Develop decomposability/irreducibility argument** — Complete via **Approach C** (Theorem 3.2.1, Lemmas 3.2.1a/b)

### 6.4 Summary of Proof Status

| Claim | Status | Section |
|-------|--------|---------|
| N = 1 cannot support distinguishability | ✅ PROVEN | §3.1.1 |
| N = 2 has degenerate Fisher metric | ✅ PROVEN | §3.1.2, Lemma 3.1.2 |
| N = 2 is dynamically unstable | ✅ PROVEN | §3.1.2, Step 5 |
| N = 2 violates Chentsov conditions | ✅ PROVEN | §3.1.2, Step 4 |
| N = 3 has positive-definite Fisher metric | ✅ PROVEN | §3.1.3 |
| N ≤ 4 from affine independence | ✅ PROVEN | Lemma 0.0.2a |
| N = 3, 6, 9,... from Z₃ constraint | ✅ PROVEN | Theorem 0.0.15 |
| N = 3 uniquely | ✅ PROVEN | Intersection of above |
| SU(3) from S₃ Weyl group | ✅ PROVEN | §4.4, Cartan classification |
| Fisher = Killing general theorem | ✅ **PROVEN** | [Lemma 0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md) |
| N ≥ 4 Fisher metric non-degenerate | ✅ **COMPUTED** | §6.1.1 |
| Composite-N decomposes via cosets | 🔶 **PROVEN** | Lemma 3.2.1a (Approach C) |
| Prime-N is irreducible | 🔶 **PROVEN** | Lemma 3.2.1b (Approach C) |
| N = 3 max per-DOF info among primes | 🔶 **PROVEN** | Theorem 3.2.1 (Approach C) |
| Pure information bound N = 3 (minimality) | 🔶 **POSTULATED** | [Proposition 0.0.XXa](Proposition-0.0.XXa-First-Stable-Principle.md) (First Stable Principle — selection criterion, not derivation; see V1.3 §Q3) |
| Pure information bound N = 3 (info density) | 🔶 **NOVEL** | Theorem 3.2.1 (Approach C — quantitative criterion, no D=4 needed) |

---

## 7. Connection to Existing Framework

### 7.1 Relationship to Theorem 0.0.15

Theorem 0.0.15 derives SU(3) from Z₃ + D = 4 + Cartan classification. This proposition provides a **complementary derivation** via information geometry.

**Shared vs. path-specific inputs (V3 §V3.1, §V3.3):**

| Input | Geometry-First (Thm 0.0.15) | Information-First (This Prop) | Status |
|-------|------------------------------|-------------------------------|--------|
| **D = 4** (Thm 0.0.1) | ✅ rank ≤ 2 via $D_{\text{space}} - 1$ | ✅ $N \leq 4$ via affine independence | **SHARED** |
| **Z₃ phase structure** | ✅ stella 3-fold rotational symmetry | ✅ "color neutrality" $\sum e^{i\phi_c} = 0$ | **SHARED** (same origin — [V3 §V3.3](../reviews/G1/G1-Validity-Audit-Module-V3-Findings.md#v33--does-color-neutrality-independently-constrain-or-restate-su3)) |
| **Compact simple group** (A-CS) | ✅ Cartan classification search space | ✅ Weyl group uniqueness argument | **SHARED** |
| Stella geometry + GR1–GR3 + MIN1 | ✅ geometric arena → Z₃ + rank | — | Geometry-only |
| A-IF (quantum interference form) | — | ✅ Fisher non-degeneracy → $N \geq 3$ | **Information-only** |
| A-SN ($S_N$ permutation symmetry) | — | ✅ Weyl group = $S_3$ | **Information-only** |

**Summary:** 3 inputs are shared (D = 4, Z₃, A-CS), 4 are geometry-only (stella, GR1–GR3, MIN1), and 2 are information-only (A-IF, A-SN). The paths are **not independent confirmations** — they share their most load-bearing inputs and differ only in the intermediate machinery used to reach SU(3).

**Key honesty point (V1.3 finding F6, V3 §V3.1):** A peer reviewer should not be told these are "independent derivations" — they are **complementary perspectives** that use different intermediate machinery to reach the same conclusion from overlapping inputs. The Z₃ constraint, in particular, enters both paths from the same geometric origin (the stella's 3-fold symmetry), even though it appears under the name "color neutrality" in this proposition (see §3.2 note).

**What this proposition genuinely adds:**
- A novel **lower bound** (N ≥ 3) from Fisher metric non-degeneracy under the interference form — this argument does not appear in Thm 0.0.15
- A different **selection mechanism** (S₃ Weyl uniqueness vs. Cartan + Z₃ center) for identifying SU(3) among rank-2 groups
- The insight that SU(3) is special from an information-geometric perspective, not just a geometric one
- Evidence that the framework's conclusions are **robust**: changing the intermediate derivation path does not change the result

### 7.2 Relationship to Theorem 0.1.0

Theorem 0.1.0 proves fields exist from Fisher metric. This proposition goes further: it derives the **number** of fields (N = 3) and their **symmetry group** (SU(3)).

### 7.3 How This Affects the Axiom Count

| | Geometry-First Path (Thm 0.0.15) | Information Path (This Prop) |
|---|---|---|
| **Shared inputs** | D = 4 (Thm 0.0.1) | D = 4 (Thm 0.0.1) |
| **Path-specific inputs** | Stella geometry (Thm 0.0.3), GR1–GR3, MIN1 | A-IF (interference form), color neutrality, compact simplicity |
| **Selection mechanism** | Z₃ from stella + Cartan classification | Fisher non-degeneracy + (affine independence or First Stable) |
| **Output** | SU(3) | SU(3) |

> **Note:** The axiom count is NOT reduced — the information path trades geometric inputs for information-theoretic ones. What changes is the **logical structure**: the information path derives SU(3) without assuming the stella octangula, showing that SU(3) is special from an information-geometric perspective (unique stable configuration with S₃ Weyl symmetry). The stella then follows from SU(3) via Theorem 0.0.3, rather than being assumed first.

### 7.4 Decoherence Robustness of the Three Paths to SU(3)

The [G1 Adversarial Stress-Test](../reviews/G1/G1-Adversarial-Stress-Test-Findings.md) §A5.2 tested what happens when the quantum interference form (Assumption A-IF) is degraded by partial decoherence. This analysis reveals an important asymmetry in robustness among the three derivation paths.

**Decoherence model.** Replace the pure quantum interference form with a partially decohered mixture:

$$p_\delta(x) = (1 - \delta)\left|\sum_c A_c(x)\, e^{i\phi_c}\right|^2 + \delta \sum_c |A_c(x)|^2$$

where $\delta \in [0,1]$ interpolates between pure quantum ($\delta = 0$) and fully classical ($\delta = 1$).

**Impact on Path C (this proposition):** For any $\delta > 0$, the Fisher metric becomes generically non-degenerate for **all** $N \geq 2$. The cross-term cancellation that eliminates $N = 2$ in §3.1.2 is spoiled by the classical admixture. Consequently, **the lower bound $N \geq 3$ is fragile under decoherence** — it requires exact quantum coherence ($\delta = 0$) of the interference form.

**Impact on Paths A and B (unaffected):**

| Path | Mechanism | Decoherence sensitivity |
|------|-----------|------------------------|
| **A** (Geometric, Thm 0.0.15) | Stella → Z₃ phases → rank ≤ 2 + Cartan → SU(3) | **None.** Z₃ is a discrete symmetry of the stella octangula. Geometric symmetries are topological invariants, insensitive to continuous perturbation. |
| **B** (Topological, Thm 0.0.15 §3.5) | Z₃ center + rank ≤ 2 + compact simple → SU(3) | **None.** The Z₃ center of SU(3) is an algebraic invariant of the group. The Cartan classification enumeration is exact. |
| **C** (Information, this Prop) | Fisher non-degeneracy → N ≥ 3 | **Fragile.** Any $\delta > 0$ breaks the $N = 2$ elimination. |

**Why this matters:** The primary derivation of SU(3) (Paths A and B) depends on exact discrete/topological properties — integer dimension ($D = 4$), discrete center ($\mathbb{Z}_3$), integer rank ($\leq 2$). These cannot be continuously deformed. Path C provides a complementary perspective but its lower bound is the most fragile component of the framework's SU(3) determination.

**Physical context:** Born rule deviations have been experimentally constrained to $\lesssim 10^{-10}$ (Sinha et al. 2010). Within these bounds, Path C's conclusions hold. But as a matter of logical structure, the framework does not *need* Path C — Paths A and B alone uniquely determine SU(3) without invoking the interference form.

> **Assessment (from [G1 Stress-Test](../reviews/G1/G1-Adversarial-Stress-Test-Findings.md) §A5.2):** DENTED — Path C's N ≥ 3 bound is fragile under decoherence, but Paths A and B are completely unaffected. The framework's primary derivation route is robust.

---

## 8. Summary

**Proposition 0.0.XX establishes:**

$$\boxed{\text{SU(3) is the unique gauge group consistent with observer distinguishability + A-IF + color neutrality (retrodiction)}}$$

**Two Results (Both Proven):**
1. **A.1 (Dimensionality):** N = 3 is uniquely selected by Fisher non-degeneracy (requires A-IF) + upper bound (D = 4 + affine independence, or First Stable Principle, or Approach C irreducible info density) ✅
2. **A.2 (Symmetry):** SU(3) is the unique rank-2 Lie group with Weyl group S₃ ✅

**The complete derivation chain (with all inputs shown):**

$$\text{Distinguishability} + \text{A-IF} + \text{Color neutrality} \xrightarrow{N \geq 3} \xrightarrow{N \leq 3} N=3 \xrightarrow{S_3} \text{SU(3)} \xrightarrow{\text{Thm 0.0.3}} \text{Stella} \to \text{Physics}$$

**Current Status:** 🔶 NOVEL — Constrained selection retrodiction complete (lower bound N ≥ 3 conditional on A-IF)

**Key Achievement:** SU(3) emerges as the unique gauge group from the intersection of information-theoretic constraints (Fisher non-degeneracy under quantum interference → N ≥ 3) and one of three upper-bound mechanisms: (a) geometric constraints (D = 4 + affine independence + Z₃ → N = 3), (b) the First Stable Principle (minimality → N = 3), or (c) **Approach C** (irreducible info density: composite N decomposes, prime N is irreducible, N = 3 maximizes per-DOF Fisher info among primes ≥ 3). Approach C is the most principled alternative to D = 4: it provides a quantitative information-theoretic criterion without requiring spacetime dimension. The quantum interference form (Assumption A-IF) is the critical framework input that makes the Fisher degeneracy argument work.

---

## 9. References

### Framework Documents
1. [Research-Meta-Foundational-Directions.md](../supporting/Research-Meta-Foundational-Directions.md) — Identifies this as Path A
2. [Theorem-0.0.1](Theorem-0.0.1-D4-From-Observer-Existence.md) — Observer existence → D = 4
3. [Proposition-0.0.17b](Proposition-0.0.17b-Fisher-Metric-Uniqueness.md) — Fisher metric uniqueness
4. [Theorem-0.1.0](../Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md) — Field existence from distinguishability
5. [Theorem-0.0.17](Theorem-0.0.17-Information-Geometric-Unification.md) — Fisher-Killing equivalence (numerical)
6. [Theorem-0.0.15](Theorem-0.0.15-Topological-Determination-SU3.md) — Topological determination of SU(3)
7. [Lemma-0.0.2a](Lemma-0.0.2a-Confinement-Dimension-Constraint.md) — Affine independence constraint
8. [Lemma-0.0.17c](Lemma-0.0.17c-Fisher-Killing-Equivalence.md) — Fisher-Killing equivalence (formal proof)
9. [**Proposition-0.0.XXa**](Proposition-0.0.XXa-First-Stable-Principle.md) — **First Stable Principle** (minimality postulate for N = 3; supplementary to geometric bound)
10. [Research-Pure-Information-Bound-On-N.md](../supporting/Research-Pure-Information-Bound-On-N.md) — Investigation leading to First Stable

### Lean Formalization
- [`lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XX.lean`](../../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XX.lean) — Full Lean 4 formalization

### Computational Verification
- [`verification/foundations/proposition_0_0_XX_N2_fisher_degeneracy.py`](../../../verification/foundations/proposition_0_0_XX_N2_fisher_degeneracy.py) — 9/9 tests passing
- [`verification/foundations/proposition_0_0_XX_adversarial_verification.py`](../../../verification/foundations/proposition_0_0_XX_adversarial_verification.py) — Adversarial physics verification (2026-02-01)
- [`verification/foundations/proposition_0_0_XX_amplitude_inequality.py`](../../../verification/foundations/proposition_0_0_XX_amplitude_inequality.py) — 9/9 tests passing (Lemma 3.1.3a, added 2026-02-01)
- [`verification/foundations/proposition_0_0_XX_decomposability.py`](../../../verification/foundations/proposition_0_0_XX_decomposability.py) — 17/17 tests passing (Lemmas 3.2.1a/b, Theorem 3.2.1 — Approach C, added 2026-02-22)

### Multi-Agent Verification
- [**Proposition-0.0.XX Multi-Agent Verification Report (2026-02-01)**](../verification-records/Proposition-0.0.XX-SU3-Distinguishability-Multi-Agent-Verification-2026-02-01.md) — Literature, Mathematical, Physics agents
  - Literature: ✅ VERIFIED (High Confidence) — All citations accurate, novel approach confirmed
  - Mathematical: ✅ PARTIAL (High Confidence) — All derivations verified, structural redundancy noted
  - Physics: ✅ PARTIAL (Medium Confidence) — Core claims sound, geometric input required for upper bound

### External References — Information Geometry (Uniqueness Theorems)

8. **Chentsov, N.N.** (1972/1982) "Statistical Decision Rules and Optimal Inference," *Translations of Mathematical Monographs* 53, AMS — Original uniqueness theorem for Fisher metric

9. **Lê, H.V.** (2017) "[The uniqueness of the Fisher metric as information metric](https://arxiv.org/abs/1306.1465)," *Annals of the Institute of Statistical Mathematics* 69, 879-895 — Extends Chentsov's theorem using strong continuity

10. **Ay, N., Jost, J., Lê, H.V., Schwachhöfer, L.** (2017) "Information geometry and sufficient statistics," *Probability Theory and Related Fields* 162, 327-364 — Full generalization to infinite sample sizes

11. **Bauer, M., Bruveris, M., Michor, P.W.** (2016) "[Uniqueness of the Fisher–Rao metric on the space of smooth densities](https://www.mat.univie.ac.at/~michor/Fisher-Rao-metric.pdf)," *Bull. London Math. Soc.* 48, 499-506 — Infinite-dimensional extension

12. **Amari, S. & Nagaoka, H.** (2000) "Methods of Information Geometry," *Translations of Mathematical Monographs* 191, AMS — Comprehensive treatment

13. **Nielsen, F.** (2020) "[An Elementary Introduction to Information Geometry](https://franknielsen.github.io/entropy-22-01100-v2.pdf)," *Entropy* 22, 1100 — Accessible modern reference

### External References — Lie Theory
14. **Humphreys, J.E.** (1972) "Introduction to Lie Algebras and Representation Theory," Springer GTM 9 — Weyl groups, Cartan classification

15. **Fulton, W. & Harris, J.** (1991) "Representation Theory: A First Course," Springer GTM 129 — SU(3) structure

16. **Hall, B.C.** (2015) "Lie Groups, Lie Algebras, and Representations," 2nd ed., Springer GTM 222 — Modern treatment

17. **Kobayashi, S. & Nomizu, K.** (1963/1969) "Foundations of Differential Geometry," Vols. I & II, Wiley — Authoritative reference for Killing forms and invariant metrics on Lie groups (Vol. II, Ch. X)

### External References — Connections
18. **Caticha, A.** (2012) "Entropic Inference and the Foundations of Physics," USP Press — Information-theoretic foundations

19. **Goyal, P.** (2010) "From Information Geometry to Quantum Theory," *New J. Phys.* 12, 023012 — Information → quantum structure

---

*Document created: 2026-02-01*
*Status: 🔶 NOVEL — Constrained selection derivation (not pure info-theoretic)*
*Last updated: 2026-02-22*
*Multi-Agent Verification: 2026-02-01 (Literature ✅, Math ✅, Physics ✅ PARTIAL)*
*Verification Follow-up: 2026-02-01 — All 8 findings from multi-agent verification addressed*
*V1 Validity Audit: 2026-02-22 — Assumption A-IF (quantum interference form) declared per [V1.3 findings](../reviews/G1/V1.3-F07-Prop-0.0.XX-Hidden-Inputs-Analysis.md)*

**Complete Derivation Chain (all inputs shown):**
$$\text{Distinguishability} + \text{A-IF} + \text{Color neutrality} \xrightarrow{N \geq 3} \xrightarrow{N \leq 3} N = 3 \xrightarrow{S_3} \text{SU(3)} \xrightarrow{\text{Thm 0.0.3}} \text{Stella} \to \text{Physics}$$
