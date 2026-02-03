# Research Direction: Fisher-Killing Equivalence for Loop Groups and Affine Lie Algebras

## Status: 🔮 EXPLORATORY — Research direction, not part of main proof chain

**Created:** 2026-02-01
**Parent Document:** [Lemma-0.0.17c-Fisher-Killing-Equivalence.md](../foundations/Lemma-0.0.17c-Fisher-Killing-Equivalence.md)
**Relationship:** Potential infinite-dimensional extension (not required for framework)

---

## 0. Motivation

Lemma 0.0.17c establishes that for compact simple Lie groups G, the Fisher metric on the Cartan torus equals the Killing metric (up to normalization) due to Weyl group symmetry uniqueness.

**Question:** Does this extend to loop groups LG = Map(S¹, G) and their central extensions (Kac-Moody groups)?

**Why this might matter:**
- Loop groups connect finite Lie theory to string theory
- Could reveal information-geometric structure in 2D conformal field theory
- Tests whether Fisher-Killing equivalence is a "finite accident" or a deeper principle

**Why this might NOT matter for Chiral Geometrogenesis:**
- Framework derives N=3 (finite) from distinguishability
- Stella octangula is a finite geometric object
- No physical motivation for infinite dimensions in current framework

---

## 1. Mathematical Setup

### 1.1 Loop Groups

**Definition:** For a compact simple Lie group G, the loop group is:
$$LG := \{g: S^1 \to G \mid g \text{ smooth}\}$$

with pointwise multiplication. This is an infinite-dimensional Lie group.

**Loop algebra:** The Lie algebra is:
$$L\mathfrak{g} := \{X: S^1 \to \mathfrak{g} \mid X \text{ smooth}\} = \mathfrak{g} \otimes C^\infty(S^1)$$

### 1.2 Affine Lie Algebras (Central Extensions)

The loop algebra has a nontrivial central extension:
$$\hat{\mathfrak{g}} = L\mathfrak{g} \oplus \mathbb{C}c$$

with bracket:
$$[X \otimes f, Y \otimes g] = [X,Y] \otimes fg + \langle X, Y \rangle \oint f \, dg \cdot c$$

where $\langle \cdot, \cdot \rangle$ is the Killing form on $\mathfrak{g}$ and $c$ is central.

### 1.3 Affine Weyl Group

The affine Weyl group is:
$$W_{\text{aff}} = W \ltimes Q^\vee$$

where:
- $W$ = finite Weyl group
- $Q^\vee$ = coroot lattice (translations)

**Key structure:** $W_{\text{aff}}$ acts on the Cartan subalgebra $\hat{\mathfrak{h}}$ as affine reflections.

### 1.4 Cartan Subalgebra of $\hat{\mathfrak{g}}$

For affine $\hat{\mathfrak{g}}$:
$$\hat{\mathfrak{h}} = \mathfrak{h} \oplus \mathbb{C}c \oplus \mathbb{C}d$$

where:
- $\mathfrak{h}$ = finite Cartan subalgebra
- $c$ = central element
- $d$ = derivation (energy/level grading)

**Dimension:** $\dim \hat{\mathfrak{h}} = \text{rank}(G) + 2$

---

## 2. Conjectured Extension

### Conjecture 2.1 (Fisher-Killing for Affine Algebras)

Let $\hat{G}$ be the Kac-Moody group associated to the affine Lie algebra $\hat{\mathfrak{g}}$. Let $\hat{T}$ be the maximal torus with Lie algebra $\hat{\mathfrak{h}}$.

Suppose $\hat{T}$ carries a probability distribution $p_\phi$ that is:
1. $W_{\text{aff}}$-invariant
2. Regular (Fisher metric well-defined and non-degenerate)

**Conjecture:** The Fisher metric on $\hat{T}$ equals the Killing form metric:
$$g^F = c \cdot g^K$$

for some constant $c > 0$.

### 2.1 Challenges

| Issue | Finite Case | Affine Case |
|-------|-------------|-------------|
| Dimension | Finite | Infinite |
| Weyl group | Finite | Infinite (but discrete) |
| Killing form | Non-degenerate | Degenerate on center |
| Cartan torus | Compact | Non-compact (includes $\mathbb{R}$ factor) |

### 2.2 Key Questions

1. **Does the Killing form extend?** The affine Killing form is degenerate (the central element $c$ has zero norm). How does this affect the metric?

2. **What is the space of $W_{\text{aff}}$-invariant metrics?** Is it finite-dimensional? The translations in $W_{\text{aff}}$ impose strong constraints.

3. **What probability distributions are $W_{\text{aff}}$-invariant?** The infinite discrete symmetry is very restrictive.

4. **Regularity:** When is the Fisher metric non-degenerate in infinite dimensions?

---

## 3. Proof Strategy (Sketch)

### Step 1: Characterize $W_{\text{aff}}$-Invariant Metrics

**Claim 3.1:** The space of $W_{\text{aff}}$-invariant symmetric bilinear forms on $\hat{\mathfrak{h}}$ is finite-dimensional.

**Argument:**
- $W_{\text{aff}} = W \ltimes Q^\vee$ with $Q^\vee$ acting by translations
- Translation invariance forces the metric to be constant along $Q^\vee$ directions
- On the quotient $\hat{\mathfrak{h}}/Q^\vee$ (a finite-dimensional torus), we reduce to the finite case
- The central and derivation directions add at most 2 additional parameters

**Expected dimension:** $\leq \text{rank}(G) + 2$ parameters (likely much smaller due to $W$ constraints)

### Step 2: Compute the Affine Killing Form

For $\hat{\mathfrak{g}}$ of type $X_n^{(1)}$ (untwisted affine), the Killing form on $\hat{\mathfrak{h}}$ is:

$$B_{\text{aff}}(H + \alpha c + \beta d, H' + \alpha' c + \beta' d) = B(H, H') + k(\alpha \beta' + \alpha' \beta)$$

where:
- $B$ = finite Killing form
- $k$ = level (normalization constant)

**Note:** $B_{\text{aff}}(c, c) = 0$ (degenerate on center)

### Step 3: Construct $W_{\text{aff}}$-Invariant Probability Distributions

**Approach:** Start with a $W$-invariant distribution on the finite Cartan torus $T$ and extend:

$$p_{\hat{\phi}}(x) = \sum_{q \in Q^\vee} w_q \cdot p_{\phi + q}(x)$$

where $w_q$ are weights summing to 1 (e.g., Gaussian decay).

**Alternative:** Use heat kernel on the affine Cartan torus.

### Step 4: Compute Fisher Metric and Compare

Using Ay-Jost-Lê-Schwachhöfer's infinite-dimensional framework:
1. Verify the Fisher integral converges
2. Compute $g^F$ on $\hat{\mathfrak{h}}$
3. Check if $g^F \propto g^K_{\text{aff}}$ (modulo the degenerate direction)

---

## 4. Special Case: $\widehat{SU(3)}$

### 4.1 Structure

For $\hat{\mathfrak{g}} = \widehat{\mathfrak{su}(3)}$ (type $A_2^{(1)}$):
- Finite Weyl group: $W = S_3$
- Coroot lattice: $Q^\vee = \mathbb{Z}\alpha_1^\vee + \mathbb{Z}\alpha_2^\vee$ (hexagonal)
- Affine Weyl group: $W_{\text{aff}} = S_3 \ltimes \mathbb{Z}^2$

### 4.2 Cartan Subalgebra

$$\hat{\mathfrak{h}} = \mathfrak{h} \oplus \mathbb{C}c \oplus \mathbb{C}d$$

where $\mathfrak{h}$ is the 2D Cartan of $\mathfrak{su}(3)$.

**Coordinates:** $(h_1, h_2, k, \tau)$ where:
- $(h_1, h_2)$ = finite Cartan coordinates
- $k$ = level (central charge)
- $\tau$ = modular parameter

### 4.3 Expected Result

**Conjecture 4.1:** For $W_{\text{aff}}$-invariant distributions at fixed level $k$:

$$g^F|_{\mathfrak{h}} = \frac{1}{6} g^K|_{\mathfrak{h}}$$

recovering the finite SU(3) result on the $\mathfrak{h}$ slice.

The directions involving $c$ and $d$ require separate analysis due to the degenerate Killing form.

---

## 5. Connection to Physics

### 5.1 WZW Models

The Wess-Zumino-Witten model on a Lie group G has:
- Target space: G (or LG in the loop formulation)
- Symmetry: $\hat{\mathfrak{g}}_L \times \hat{\mathfrak{g}}_R$ (two copies of affine algebra)
- Level $k$: Quantized, determines central charge $c = \frac{k \dim G}{k + h^\vee}$

**Potential connection:** The Fisher metric on the space of WZW primaries might equal the Killing metric structure.

### 5.2 Modular Invariance

Affine characters $\chi_\lambda(\tau, z)$ transform under modular group $SL(2,\mathbb{Z})$.

**Question:** Does the Fisher metric on the space of conformal blocks have modular properties?

### 5.3 Relevance to Chiral Geometrogenesis

| If true | Implication |
|---------|-------------|
| Fisher = Killing extends to loops | The principle is universal, not a finite accident |
| New structure at level $k$ | Could hint at quantization mechanism |
| Connection to CFT | Might link to holographic emergence |

**Current assessment:** Interesting but speculative. No direct application to the stella octangula framework.

---

## 6. Required Mathematical Tools

To pursue this direction rigorously:

1. **Infinite-dimensional geometry** — Banach/Fréchet manifolds
2. **Kac-Moody representation theory** — Highest weight modules, characters
3. **Ay-Jost-Lê-Schwachhöfer framework** — Parametrized measure models
4. **Heat kernels on Lie groups** — For constructing invariant measures
5. **Modular forms** — For understanding transformation properties

**Estimated effort:** Several months of focused mathematical work

---

## 7. Next Steps (If Pursued)

- [ ] Verify Claim 3.1: Dimension of $W_{\text{aff}}$-invariant metrics
- [ ] Compute affine Killing form explicitly for $A_2^{(1)}$
- [ ] Construct explicit $W_{\text{aff}}$-invariant probability distribution
- [ ] Apply Ay-Jost-Lê-Schwachhöfer to compute Fisher metric
- [ ] Compare with Killing form on appropriate subspace
- [ ] Investigate connection to WZW model correlation functions

---

## 8. References

### Affine Lie Algebras
1. **Kac, V.G.** (1990) "Infinite Dimensional Lie Algebras" — Standard reference
2. **Pressley, A. & Segal, G.** (1986) "Loop Groups" — Geometric approach
3. [Affine Lie algebra - Wikipedia](https://en.wikipedia.org/wiki/Affine_Lie_algebra)

### Information Geometry
4. **Ay, N., Jost, J., Lê, H.V., Schwachhöfer, L.** (2017) "Information Geometry" — Infinite-dimensional extension
5. [Lemma-0.0.17c](../foundations/Lemma-0.0.17c-Fisher-Killing-Equivalence.md) — Finite case (this framework)

### Physics
6. **Di Francesco, P., Mathieu, P., Sénéchal, D.** (1997) "Conformal Field Theory" — WZW models
7. **Fuchs, J.** (1992) "Affine Lie Algebras and Quantum Groups" — Physics applications

---

## 9. Status Log

| Date | Action |
|------|--------|
| 2026-02-01 | Document created, basic structure outlined |
| | Identified key mathematical challenges |
| | Noted separation from main proof chain |

---

*This document explores a potential extension direction. It is NOT part of the main Chiral Geometrogenesis proof chain and is marked as exploratory research.*
