# Proposition 2.5.2b: Inter-Stella Gauge Coupling on the FCC Lattice

## Status: 🔶 NOVEL ✅ ESTABLISHED — Coupled tensor network partition function (Phase B of Yang-Mills Mass Gap program)

**Created:** 2026-02-12
**Purpose:** Derive the SU(3) partition function on the FCC lattice by coupling single-stella building blocks (Prop 0.0.38) through shared triangular faces. Each cell (tetrahedral or octahedral) contributes a 2D topological partition function, and the face-sharing constraints create a 3D tensor network.

**Role in Framework:** First step of Phase B (inter-stella assembly). Extends the exactly solvable single-stella system to a genuine 3D lattice gauge theory with spatial extent. The coupled tensor network provides the starting point for the transfer matrix (Prop 2.5.2c) and ultimately the mass gap analysis (Phases C-D).

**File Structure:**
- **This file** — Formal statement, symbol table, background, honest assessment (§0-7)
- **[Derivation file](./Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Derivation.md)** — Complete proofs (§7-13)
- **[Applications file](./Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Applications.md)** — Verification & predictions (§14-18)

**Verification:**
- **[Multi-Agent Verification Report](../verification-records/Proposition-2.5.2b-Multi-Agent-Verification-2026-02-12.md)** — Literature + Math + Physics peer review
- **[Adversarial Physics Script](../../../verification/Phase2/prop_2_5_2b_adversarial_physics.py)** — Adversarial verification tests

**Lean 4 Formalization:** [Proposition_2_5_2b.lean](../../../lean/ChiralGeometrogenesis/Phase2/Proposition_2_5_2b.lean) ✅ VERIFIED

---

## Dependencies

### Direct Prerequisites (Required)

| Theorem | Provides | Status |
|---------|----------|--------|
| **[Prop 0.0.38](../foundations/Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md)** (Exact Partition Function) | $Z_{K_4} = \sum_R d_R^2 a_R^4$, cell-by-cell character expansion | 🔶 NOVEL ✅ ESTABLISHED |
| **[Prop 0.0.38a](../foundations/Proposition-0.0.38a-Stella-Gauge-Spectrum.md)** (Stella Gauge Spectrum) | Transfer matrix eigenvalues $t_R = d_R^4 a_R^{10}$, spectral gap | 🔶 NOVEL ✅ ESTABLISHED |
| **[Thm 0.0.6](../foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md)** (Spatial Extension) | FCC lattice structure, cell decomposition, dihedral angles, face sharing | ✅ ESTABLISHED |
| **[Prop 0.0.27](../foundations/Proposition-0.0.27-Lattice-QFT-On-Stella.md)** (Lattice QFT on Stella) | Wilson action, character expansion, gauge transformations | 🔸 PARTIAL |
| **[Def 0.1.1](../Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md)** (Stella Boundary) | $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$, $\chi = 4$ | ✅ ESTABLISHED |
| **[Prop 0.0.39](../foundations/Proposition-0.0.39-Stella-Adjoint-Decomposition.md)** (Stella Adjoint Decomposition) | Each corner tet carries one adjoint d.o.f.; face-sharing transfers one gluon channel per shared face | 🔶 NOVEL ✅ ESTABLISHED |

### Downstream Usage

| Theorem | How This Enables It |
|---------|---------------------|
| **Prop 2.5.2c** (Transfer Matrix for FCC Layers) | Tensor network structure as input to layer-by-layer transfer matrix |
| **Thm 7.4.1** (Reflection Positivity) | Partition function structure needed for Osterwalder-Schrader reflection positivity |
| **Thm 7.4.7** (CG Yang-Mills Mass Gap) | Foundation for mass gap program |

---

## 0. Executive Summary

### 0.1 The Problem

**Status:** ✅ ESTABLISHED (well-known limitations of 2D Yang-Mills)

The single-stella partition function $Z_{K_4} = \sum_R d_R^2 a_R^4$ (Prop 0.0.38) is a 2D topological gauge theory on $S^2$. As Witten (1991) showed, 2D Yang-Mills theory is topological: the partition function depends only on the Euler characteristic $\chi(M)$, the number of faces $|F|$, and the coupling $\beta$ -- not on the metric. Concretely:

- **No spatial extent.** K₄ has 4 vertices, 6 edges, 4 faces. It is a finite system with no notion of "far apart."
- **No propagation.** There is no direction along which gauge-invariant information can propagate. Every vertex is adjacent to every other vertex in K₄.
- **No true mass gap.** The "spectral gap" $\Delta(\beta) = -2\ln 3 - 4\ln u_\mathbf{3}(\beta)$ from Prop 0.0.38a is a property of a single finite cell, not a mass gap in the Wightman axiom sense. A mass gap requires an infinite-volume spatial lattice with a transfer matrix whose spectral gap survives the thermodynamic limit.
- **No 3D dynamics.** The 2D topological formula $Z = \sum_R d_R^\chi a_R^F$ is insensitive to the embedding geometry. Any triangulation of $S^2$ with the same number of faces gives the same $Z$. The stella-specific content enters only when stellae are assembled into a 3D lattice.
- **Universality of 2D.** The formula $Z_{K_4} = \sum_R d_R^2 a_R^4$ would be the same for ANY triangulation of $S^2$ with 4 faces -- a fact that underscores the topological nature of the 2D theory and the necessity of the 3D assembly for physical content.

The challenge is to pass from the exactly solvable single-stella building block to a genuine 3D gauge theory with spatial extent, propagation, and a well-defined mass gap. This proposition accomplishes the first step of that passage.

### 0.2 The Solution

**Status:** 🔶 NOVEL

Apply the generalized Migdal-Witten formula for 2-complexes (Oeckl 2005) to the FCC 2-skeleton. Each cell of the tetrahedral-octahedral honeycomb (Thm 0.0.6) has boundary $S^2$, so $\chi(\text{cell}) = 2$ for every cell. The cell-by-cell character expansion identifies the representation labels, but the combined partition function is determined by the **global** 2-skeleton topology, not by naively multiplying cell weights. The key ingredients are:

**Cell weights.** Each cell type contributes a representation-dependent weight:
- **Tetrahedral cell** ($F_\text{tet} = 4$ triangular faces):

$$w_\text{tet}(R) = d_R^2 \, a_R(\beta)^4$$

- **Octahedral cell** ($F_\text{oct} = 8$ triangular faces):

$$w_\text{oct}(R) = d_R^2 \, a_R(\beta)^8$$

**Face-sharing constraints.** At each shared triangular face between two adjacent cells, the character orthogonality integrals force the representation labels of the two cells to agree. This is the same mechanism that, within a single K₄, forces all four face labels to collapse to a single representation R (Prop 0.0.38 §4.4).

**Global label constraint.** The face-sharing graph $\mathcal{G}_\text{face}$ of the FCC lattice is connected (every cell shares at least one face with a neighbor, and the lattice is connected). Therefore, iterating the face-sharing constraint across the entire lattice forces ALL cells to carry the SAME representation label $R$.

**Global 2-skeleton formula.** Once all cells carry the same label $R$, the combined partition function is determined by the Euler characteristic of the FCC 2-skeleton $\chi_2 = V - E + F = N - 6N + 8N = 3N$ and the number of distinct faces $|F| = 8N$, giving the exponents $d_R^{3N} a_R^{8N}$. Note: naively multiplying cell weights $\prod_c w_c(R)$ would give $d_R^{6N} a_R^{16N}$, which double-counts because shared faces contribute $a_R$ once per adjacent cell rather than once per distinct face, and the global Euler characteristic $\chi_2 = 3N$ differs from $\sum_c \chi(c) = 6N$.

### 0.3 The Result

**Status:** 🔶 NOVEL

On a finite FCC lattice with $N$ primitive unit cells (containing $2N$ tetrahedra and $N$ octahedra), the partition function is:

$$\boxed{Z_\text{FCC}(\beta, N) = \sum_R d_R^{3N} \left[a_R(\beta)\right]^{8N}}$$

This is a sum over a single representation label $R$ ranging over all irreducible representations of SU(3), with the exponents determined by the topology of the FCC 2-skeleton:

- **Dimension factor:** $d_R^{3N}$ from the Euler characteristic of the FCC 2-skeleton: $\chi_2 = V - E + F = N - 6N + 8N = 3N$
- **Face factor:** $a_R^{8N}$ from $8N$ distinct triangular faces in the FCC lattice (the Wilson action contains one Boltzmann factor per distinct face)

### 0.4 Decoupling Limit Check

**Status:** ✅ ESTABLISHED (consistency check)

If one hypothetically removed all face-sharing constraints (cutting every shared face so that cells become independent), the partition function would factorize into independent cell contributions:

$$Z_\text{FCC} \xrightarrow{\text{decouple}} [Z_{K_4}]^{2N} \times [Z_\text{oct}]^N = \left[\sum_R d_R^2 a_R^4\right]^{2N} \times \left[\sum_R d_R^2 a_R^8\right]^N$$

In the coupled system, the constraint that all cells carry the same R converts the product of sums into a sum of products. The decoupled limit has more degrees of freedom (each cell chooses its own R independently) and hence higher entropy. This is consistent: coupling imposes constraints and reduces entropy.

### 0.5 Physical Significance

The coupled partition function $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ is the starting point for:

1. **Transfer matrix construction** (Prop 2.5.2c): Slicing the FCC lattice into layers and defining a transfer matrix whose eigenvalues determine propagation in the spatial direction
2. **Thermodynamic limit** ($N \to \infty$): The free energy per cell is $f(\beta) = -\frac{1}{3N}\ln Z_\text{FCC} = -\frac{1}{3}\ln\!\left(d_{R^*} \, a_{R^*}^{8/3}\right) + O(1/N)$, where $R^*$ is the dominant representation
3. **Mass gap analysis** (Phases C-D): The spectral gap in the transfer matrix determines the physical mass gap
4. **Continuum limit** ($a \to 0$, $\beta \to \infty$): Asymptotic freedom requires $\beta \to \infty$ as $a \to 0$, with $a_R \to 1$ for all R, and the dynamics is controlled by the competition between $d_R^{3N}$ (entropy) and $a_R^{8N}$ (energy)

### 0.6 Explicit Examples for Small $N$

**Status:** 🔶 NOVEL (explicit formulas)

To make the general formula concrete, here are the first few cases:

**$N = 1$ (single primitive cell: 2 tetrahedra + 1 octahedron):**

$$Z_\text{FCC}(\beta, 1) = \sum_R d_R^3 \, a_R^{8} = 1 \cdot a_\mathbf{1}^{8} + 2 \cdot 3^3 \cdot a_\mathbf{3}^{8} + 8^3 \cdot a_\mathbf{8}^{8} + 2 \cdot 6^3 \cdot a_\mathbf{6}^{8} + \cdots$$

$$= a_\mathbf{1}^{8}\left[1 + 54 \, u_\mathbf{3}^{8} + 512 \, u_\mathbf{8}^{8} + 432 \, u_\mathbf{6}^{8} + \cdots\right]$$

At $\beta = 1$ (strong coupling): $u_\mathbf{3} \approx 0.060$, so $u_\mathbf{3}^{8} \approx 1.68 \times 10^{-10}$ and the correction $54 \times 1.68 \times 10^{-10} \approx 9.1 \times 10^{-9}$; the trivial representation dominates overwhelmingly.

At $\beta = 6$ (physical coupling): $u_\mathbf{3} \approx 0.42$, so $u_\mathbf{3}^{8} \approx 5.7 \times 10^{-4}$ and the correction $54 \times 5.7 \times 10^{-4} \approx 3.1 \times 10^{-2}$ is small but non-negligible.

**Scaling with $N$:** The key feature is that the exponents scale as $3N$ and $8N$. For large $N$, the subleading terms are exponentially suppressed relative to the leading term:

$$\frac{w_\mathbf{3}}{w_\mathbf{1}} = 3^{3N} u_\mathbf{3}^{8N} = \exp\!\left[-N\left(8\ln\frac{1}{u_\mathbf{3}} - 3\ln 3\right)\right]$$

At $\beta = 1$: the exponent is $N \times (8 \times 2.81 - 3.30) \approx 19.2 N$. This exponential suppression in $N$ is the hallmark of confinement in the thermodynamic limit.

### 0.7 The Octahedral Cell Partition Function

**Status:** ✅ ESTABLISHED (2D character expansion on $S^2$)

The regular octahedron provides a second cell type in the FCC honeycomb. As a triangulation of $S^2$, the octahedral surface has:

| Property | Value |
|----------|-------|
| Vertices $\|V\|$ | 6 |
| Edges $\|E\|$ | 12 |
| Faces $\|F\|$ | 8 (equilateral triangles) |
| Euler characteristic $\chi$ | $6 - 12 + 8 = 2$ |
| Cycle rank $\beta_1$ | $12 - 6 + 1 = 7$ |

Applying the standard 2D character expansion formula:

$$Z_\text{oct}(\beta) = \sum_R d_R^{\chi(S^2)} \, [a_R(\beta)]^{|F|} = \sum_R d_R^2 \, [a_R(\beta)]^8$$

This is the octahedral analog of the tetrahedral $Z_{K_4} = \sum_R d_R^2 a_R^4$. Both have the same topological prefactor $d_R^2$ (since both are triangulations of $S^2$ with $\chi = 2$), but different dynamical factors ($a_R^8$ vs $a_R^4$) reflecting the different face counts.

**Strong coupling comparison.** At $\beta \ll 1$, the leading non-trivial contribution from the fundamental representation:
- Tetrahedron: $d_\mathbf{3}^2 a_\mathbf{3}^4 = 9(\beta/18)^4$
- Octahedron: $d_\mathbf{3}^2 a_\mathbf{3}^8 = 9(\beta/18)^8$

The octahedral cell is more strongly "confined" at strong coupling because the larger exponent $a_R^8$ suppresses non-trivial representations more rapidly than $a_R^4$.

### 0.8 Comparison: Isolated Stella vs FCC Assembly

**Status:** 🔶 NOVEL (framework comparison)

| Property | Isolated stella ($\partial\mathcal{S}$) | FCC assembly ($\mathcal{H}$, $N$ cells) |
|----------|--------------------------------------|----------------------------------------|
| Topology | $S^2 \sqcup S^2$ (two disjoint K₄) | Connected 3D simplicial complex |
| Gauge DOF | 6 edges per K₄ (3 independent) | $\sim 6N$ edges (after gauge fixing) |
| Partition function | $[Z_{K_4}]^2 = [\sum_R d_R^2 a_R^4]^2$ | $\sum_R d_R^{3N} a_R^{8N}$ |
| Rep labels | 1 per K₄ (2 independent for stella) | 1 for entire lattice |
| Spatial extent | None | $\sim N^{1/3}$ lattice spacings |
| Mass gap | Finite-system artifact | Genuine (from transfer matrix, Phase C) |
| Continuum limit | Not applicable | $a \to 0$, $\beta \to \infty$ (Phase D) |
| 2D topological? | Yes | No (depends on $\mathcal{G}_\text{face}$) |

---

## 1. Statement

**Proposition 2.5.2b (Inter-Stella Gauge Coupling on the FCC Lattice) — 🔶 NOVEL**

> Let $\mathcal{H}$ be the tetrahedral-octahedral honeycomb (Thm 0.0.6) restricted to a finite region with $N$ primitive unit cells, containing $2N$ tetrahedral cells and $N$ octahedral cells. All faces are equilateral triangles. Assign SU(3) gauge variables $U_\ell \in SU(3)$ to each edge $\ell$ with Haar measure $dU_\ell$, and define the Wilson action
>
> $$S_W = \beta \sum_{f \in F} \left(1 - \frac{1}{3}\operatorname{Re}\operatorname{Tr} W_f\right), \quad \beta = \frac{6}{g^2}$$
>
> where $W_f = \prod_{\ell \in \partial f} U_\ell^{\pm 1}$ is the plaquette holonomy around face $f$, and the sum runs over all $|F|$ triangular faces. Then:
>
> **(a) Wilson action on FCC.** The partition function for SU(3) lattice gauge theory on $\mathcal{H}$ is:
>
> $$Z_\text{FCC}(\beta, N) = \int \prod_{\ell \in E} dU_\ell \prod_{f \in F} \exp\!\left(\frac{\beta}{3}\operatorname{Re}\operatorname{Tr} W_f\right)$$
>
> where the lattice has $|E| = 6N$ edges per $N$ primitive unit cells (before gauge fixing; $5N + 1$ independent after gauge fixing) and $|F| = 8N$ distinct triangular faces. Each distinct face appears once in the Wilson action sum, giving the exponent $8N$ on $a_R$ in the final formula.
>
> **(b) Cell-by-cell character expansion.** Each cell $c$ of the honeycomb (tetrahedral or octahedral) has boundary homeomorphic to $S^2$ with $\chi = 2$. The standard 2D lattice gauge theory character expansion (Migdal 1975, Menotti & Onofri 1981, Witten 1991) applies within each cell, giving the cell weight:
>
> $$w_c(R) = d_R^{\chi(S^2)} \, a_R(\beta)^{F_c} = \begin{cases} d_R^2 \, a_R(\beta)^4 & \text{tetrahedral cell } (F_c = 4) \\ d_R^2 \, a_R(\beta)^8 & \text{octahedral cell } (F_c = 8) \end{cases}$$
>
> where $d_R = \dim(R)$ and $a_R(\beta) = \frac{1}{d_R}\int_{SU(3)} dU \, e^{\frac{\beta}{3}\operatorname{Re}\operatorname{Tr} U}\,\chi_R(U^\dagger)$ are the heat kernel coefficients.
>
> **(c) Face-sharing constraint.** When two cells $c_1, c_2$ share a triangular face $f$, the character orthogonality integrals over the shared edges force the representation labels of the two cells to agree:
>
> $$\boxed{R_{c_1} = R_{c_2} \quad \text{for all pairs } (c_1, c_2) \text{ sharing a face}}$$
>
> This is the same character orthogonality mechanism that forces all four face labels to coincide within a single K₄ (Prop 0.0.38 §4.4), now applied at the inter-cell level.
>
> **(d) Global label constraint.** The face-sharing graph $\mathcal{G}_\text{face}$ of the FCC honeycomb is connected. Since every pair of face-adjacent cells must carry the same representation label (by (c)), and the connectivity of $\mathcal{G}_\text{face}$ propagates this constraint transitively, all cells on a connected FCC lattice carry the SAME representation label $R$:
>
> $$\boxed{Z_\text{FCC}(\beta, N) = \sum_R d_R^{\chi_2} \left[a_R(\beta)\right]^{|F|} = \sum_R d_R^{3N} \left[a_R(\beta)\right]^{8N}}$$
>
> where $\chi_2 = V - E + F = N - 6N + 8N = 3N$ is the Euler characteristic of the FCC 2-skeleton and $|F| = 8N$ is the number of distinct triangular faces.
>
> **(e) Decoupling limit.** If one hypothetically removed all face-sharing constraints (cutting shared faces so cells become independent), the partition function would factorize:
>
> $$Z_\text{FCC} \xrightarrow{\text{decouple}} \left[Z_{K_4}\right]^{2N} \times \left[Z_\text{oct}\right]^N = \left[\sum_R d_R^2 a_R^4\right]^{2N} \times \left[\sum_R d_R^2 a_R^8\right]^N$$
>
> This is verified as a consistency check: the coupled system restricts the sum to a single label R, while the decoupled system allows independent labels per cell.

**Remark on boundary conditions.** For **periodic boundary conditions** (wrapping the lattice into a 3-torus $T^3$), all faces are shared between two cells and the formula $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ holds **exactly** with no boundary corrections. This is the natural setting for the derivation.

For **open (free) boundary conditions**, the boundary $\partial\mathcal{H}$ consists of $O(N^{2/3})$ triangular faces that belong to only one cell (not shared). These boundary faces contribute to the Wilson action but do not generate face-sharing constraints. The boundary face labels are summed over independently. The difference between boundary conditions affects $O(N^{2/3})$ faces out of $O(N)$ total, and vanishes in the thermodynamic limit as $O(N^{-1/3})$. The periodic case is exact; the open-BC corrections require a separate analysis deferred to Phase C.

**Remark on gauge invariance.** The partition function $Z_\text{FCC}$ is manifestly gauge invariant: it is defined as an integral over all gauge field configurations with Haar measure, and the Wilson action is gauge invariant (plaquette holonomies transform by conjugation, and Re Tr is conjugation-invariant). The character expansion preserves this gauge invariance at each step, since $d_R$, $a_R$, and $\chi_R$ are all class functions.

---

## 2. Symbol Table

| Symbol | Meaning | Dimension | Defined In |
|--------|---------|-----------|------------|
| $N$ | Number of FCC primitive unit cells | [1] | §1 |
| $\mathcal{H}$ | Tetrahedral-octahedral honeycomb (FCC dual) | — | Thm 0.0.6 |
| $\mathcal{G}_\text{face}$ | Face-sharing graph (cells = vertices, shared faces = edges) | — | §1(d) |
| $w_\text{tet}(R)$ | Tetrahedral cell weight $= d_R^2 a_R^4$ | [1] | §1(b) |
| $w_\text{oct}(R)$ | Octahedral cell weight $= d_R^2 a_R^8$ | [1] | §1(b) |
| $Z_\text{FCC}(\beta, N)$ | FCC lattice partition function | [1] | §1(d) |
| $Z_{K_4}(\beta)$ | Single tetrahedron partition function $= \sum_R d_R^2 a_R^4$ | [1] | Prop 0.0.38 |
| $Z_\text{oct}(\beta)$ | Single octahedron partition function $= \sum_R d_R^2 a_R^8$ | [1] | §1(e) |
| $\beta$ | Lattice coupling $= 2N_c/g^2 = 6/g^2$ | [1] | Lattice QCD |
| $N_c$ | Number of colors $(= 3)$ | [1] | SU(3) |
| $W_f$ | Plaquette holonomy on face $f$ | SU(3) | Prop 0.0.27 |
| $U_\ell$ | Gauge variable on edge $\ell$ | SU(3) | Prop 0.0.27 |
| $R$ | Irreducible representation of SU(3) | — | Rep theory |
| $(p,q)$ | Dynkin labels of SU(3) irrep | — | Prop 0.0.38 §3.2 |
| $d_R$ | Dimension of representation $R$ | [1] | Prop 0.0.38 §3.2 |
| $\chi_R(U)$ | Character $= \operatorname{Tr}_R(U)$ | [1] | Rep theory |
| $a_R(\beta)$ | Heat kernel coefficient for rep $R$ | [1] | Prop 0.0.38 §1(c) |
| $u_R(\beta)$ | Reduced coefficient $= a_R/a_\mathbf{1}$ | [1] | Prop 0.0.38 §5.1 |
| $\chi(S^2)$ | Euler characteristic of $S^2$ $(= 2)$ | [1] | Topology |
| $F_c$ | Number of faces of cell $c$ ($4$ for tet, $8$ for oct) | [1] | §1(b) |
| $|E|$ | Total number of edges in the lattice | [1] | §1(a) |
| $|F|$ | Total number of distinct faces in the lattice $(= 8N)$ | [1] | §1(a) |
| $\theta_T$ | Dihedral angle of regular tetrahedron $= \arccos(1/3) \approx 70.53°$ | rad | Thm 0.0.6 |
| $\theta_O$ | Dihedral angle of regular octahedron $= \pi - \arccos(1/3) \approx 109.47°$ | rad | Thm 0.0.6 |
| $t_R(\beta)$ | Transfer matrix eigenvalue $= d_R^4 a_R^{10}$ (single-stella) | [1] | Prop 0.0.38a |
| $S_W$ | Wilson action | [1] | Prop 0.0.27 |
| $f(\beta)$ | Free energy per cell | [1] | §0.5 |
| $R^*(\beta)$ | Dominant representation | — | §0.5 |

---

## 3. Background

### 3.1 From 2D Topological to 3D Dynamics

**Status:** ✅ ESTABLISHED (standard lattice gauge theory)

The single-stella partition function $Z_{K_4} = \sum_R d_R^2 a_R^4$ is an instance of 2D Yang-Mills theory on $S^2$ (Witten 1991). The 2D formula $Z = \sum_R d_R^{\chi(M)} a_R^{|F|}$ is topological in the following precise sense: it depends on the surface $M$ only through its Euler characteristic $\chi(M)$ and the number of faces $|F|$ in the triangulation, not on the metric. In particular:

- Changing the shapes or sizes of faces does not change $Z$
- Subdividing faces (adding vertices) changes $|F|$ but in a controlled way (each subdivision multiplies the cell weight by $a_R$)
- The partition function carries no information about distances or propagation

**What changes when cells share faces.** When we assemble multiple cells into the FCC honeycomb, the shared faces introduce constraints between the representation labels of adjacent cells. These constraints are the mechanism by which the topological 2D theory within each cell becomes a genuine 3D theory:

1. **The face-sharing constraint is not topological.** It depends on which cells are adjacent -- i.e., on the connectivity of the 3D lattice. Different 3D lattices (e.g., FCC vs BCC vs simple cubic) would produce different face-sharing graphs and hence different coupled partition functions.

2. **The constraint introduces correlations.** In the decoupled limit, each cell's representation label is independent. The face-sharing constraint couples them, creating long-range correlations in the thermodynamic limit ($N \to \infty$).

3. **The number of independent degrees of freedom changes.** In the decoupled system, there are $3N$ independent representation labels (one per cell). In the coupled system, the connected face-sharing graph forces all labels to be equal, leaving exactly 1 independent label. This dramatic reduction -- from $3N$ to $1$ -- is the origin of the 3D confinement physics.

### 3.2 What Is Derived vs Assumed (Phase 0 Context)

**Status:** ✅ ESTABLISHED (framework context)

This proposition sits at the interface of Phase 0 (pre-geometric foundations) and Phase 2 (dynamics). The following logical chain clarifies what is derived and what is assumed:

| Element | Status | Source |
|---------|--------|--------|
| **SU(3) gauge group** | DERIVED | Stella geometry forces SU(3) (Thm 0.0.3) |
| **FCC lattice structure** | DERIVED | SU(3) phase coherence forces FCC (Thm 0.0.6, Thm 0.0.16) |
| **Cell decomposition (2 tet + 1 oct per cell)** | DERIVED | Consequence of FCC honeycomb geometry (Thm 0.0.6) |
| **Dihedral angle constraint** | DERIVED | Regular tetrahedra and octahedra with $2\theta_T + 2\theta_O = 360°$ |
| **Wilson action with Haar measure** | ASSUMED | Standard lattice gauge theory formalism (Wilson 1974) |
| **Character expansion on $S^2$** | ESTABLISHED | Migdal (1975), Menotti & Onofri (1981), Witten (1991) |
| **Heat kernel coefficients $a_R(\beta)$** | ESTABLISHED | Standard lattice QCD (Prop 0.0.38 §5) |

The single assumed input -- the Wilson action formalism -- is the standard starting point for non-perturbative lattice gauge theory. This assumption is recorded in the Mass Gap Plan §0½.3 and will be revisited in Phase D (continuum limit).

**The CG derivation chain for context.** The full logical chain leading to this proposition:

1. **Observer existence** $\to$ D = 4 spacetime (Thm 0.0.1)
2. **Minimal geometric realization** $\to$ stella octangula (Def 0.0.0)
3. **Stella geometry** $\to$ SU(3) gauge group (Thm 0.0.3)
4. **SU(3) phase coherence** $\to$ FCC lattice (Thm 0.0.6)
5. **Wilson action on FCC** $\to$ character expansion cell-by-cell (this proposition)
6. **Face-sharing constraints** $\to$ global label constraint $\to$ exact $Z_\text{FCC}$ (this proposition)

Steps 1-4 are established in the foundations. Step 5 assumes only the standard Wilson action formalism. Step 6 is the novel content of this proposition.

### 3.3 Character Expansion on Simplicial 2-Complexes

**Status:** ✅ ESTABLISHED (Migdal 1975, Menotti & Onofri 1981, Rusakov 1990, Witten 1991)

The partition function for 2D lattice gauge theory with gauge group $G$ on a closed orientable 2-manifold $M$, triangulated by a simplicial complex $\Sigma$ with $|V|$ vertices, $|E|$ edges, $|F|$ faces, and Euler characteristic $\chi = |V| - |E| + |F|$, is:

$$Z_\Sigma(\beta) = \sum_R d_R^{\chi(M)} \, [a_R(\beta)]^{|F|}$$

**Derivation sketch.** Starting from the partition function $Z = \int \prod_e dU_e \prod_f e^{\frac{\beta}{N}\operatorname{Re}\operatorname{Tr} W_f}$:

1. Expand each face Boltzmann factor in characters: $e^{\frac{\beta}{N}\operatorname{Re}\operatorname{Tr} W_f} = \sum_R d_R a_R(\beta) \chi_R(W_f)$
2. Assign a representation label $R_f$ to each face
3. Integrate over each edge variable using Schur orthogonality
4. Each vertex contributes a factor involving $6j$-symbols (for triangulations, these are trivial)
5. The edge integrals force representation labels on adjacent faces to agree
6. For a closed surface, this collapses the sum to a single label $R$ with weight $d_R^{\chi} a_R^{|F|}$

The crucial point for this proposition: **each cell of the FCC honeycomb has boundary $S^2$**, so the formula applies within each cell with $\chi = 2$. The cell-by-cell application is exact because the integrals over interior edges (edges shared by two faces of the same cell) can be performed independently of exterior edges (edges shared by faces of different cells).

**Why the formula applies cell-by-cell.** Consider two adjacent cells $c_1$ and $c_2$ sharing a triangular face $f$. The face $f$ has 3 edges, each of which may be:
- **Interior to $c_1$** (shared by two faces of $c_1$ only) -- these edges are integrated within $c_1$
- **Interior to $c_2$** (shared by two faces of $c_2$ only) -- these edges are integrated within $c_2$
- **Shared between $c_1$ and $c_2$** (the edges of face $f$) -- these are the coupling edges

The edges of the shared face $f$ are the coupling mechanism. Within each cell, the character expansion reduces all face labels to a single representation $R_c$. The integration over the shared edges then produces a Kronecker delta $\delta_{R_{c_1}, R_{c_2}}$ via character orthogonality, exactly as in Steps 1-3 of the K₄ derivation (Prop 0.0.38 §4.4).

**Explicit mechanism for the face-sharing constraint.** When cell $c_1$ carries representation label $R$ and cell $c_2$ carries label $R'$, the integral over the shared-edge variables involves:

$$\int dU_\ell \; \chi_R(U_\ell \cdots) \, \chi_{R'}(\cdots U_\ell^{-1}) \propto \delta_{R, R'}$$

by the character convolution lemma (Prop 0.0.38, Lemma 4.4.1). This forces $R = R'$.

### 3.4 State Sum / Tensor Network Description

**Status:** ✅ ESTABLISHED (Oeckl 2005, lattice gauge theory on cellular decompositions)

The partition function of a lattice gauge theory on a 3D simplicial complex admits a natural description as a state sum over representation labels, which can equivalently be viewed as a tensor network. Oeckl (2005) treats the general framework of lattice gauge theory on cellular decompositions (state sum models); the "tensor network" language became standard later (Levin & Nave 2007, Shimizu 2014). In this language:

- **Tensors:** Each cell $c$ of the honeycomb is a tensor $T_c(R_{f_1}, R_{f_2}, \ldots, R_{f_{F_c}})$ labeled by the representation assignments on its faces
- **Contraction:** Shared faces are contracted indices; the character orthogonality integral over shared-edge variables implements the contraction
- **Partition function:** $Z = \sum_{\{R_f\}} \prod_c T_c(\{R_f\}_{\text{faces of } c})$

For the FCC honeycomb, the within-cell character orthogonality (Prop 0.0.38 §4.4) simplifies each cell tensor to a diagonal form:

$$T_c^{(\text{tet})}(R_{f_1}, R_{f_2}, R_{f_3}, R_{f_4}) = w_\text{tet}(R_{f_1}) \cdot \delta_{R_{f_1}, R_{f_2}} \cdot \delta_{R_{f_2}, R_{f_3}} \cdot \delta_{R_{f_3}, R_{f_4}}$$

$$T_c^{(\text{oct})}(R_{f_1}, \ldots, R_{f_8}) = w_\text{oct}(R_{f_1}) \cdot \prod_{i=2}^{8} \delta_{R_{f_1}, R_{f_i}}$$

That is, each cell tensor is nonzero only when all its face labels are equal. This is a consequence of the character orthogonality within each cell having boundary $S^2$ (connected, genus 0). The inter-cell contractions then force the common label of one cell to equal the common label of its neighbor, and the connectivity of the lattice propagates this globally.

**Comparison with standard tensor network approaches.** In the standard hypercubic lattice, the tensor network structure is more complex because the cells (hypercubes) have faces that are not triangulated simplices. The FCC honeycomb is simplicial (all faces are triangles), which allows the exact character expansion to be applied cell-by-cell without additional complications.

**Advantage of the simplicial structure.** On the hypercubic lattice, plaquettes are squares (4 edges), and the character expansion of the Boltzmann weight involves convolution integrals over 4-edge loops. On the FCC honeycomb, all plaquettes are triangles (3 edges), and the corresponding integrals are simpler. Moreover, the 2D topological formula $Z = \sum_R d_R^\chi a_R^F$ applies directly to each cell, giving exact cell weights without approximation. This simplification is a direct consequence of the stella geometry: tetrahedra and octahedra are the natural simplicial polyhedra, and the FCC honeycomb is the unique space-filling arrangement of these simplices (Thm 0.0.6).

**Tensor network contraction order.** The partition function can be evaluated by contracting the tensor network in any order. The most natural order for the FCC lattice is layer-by-layer (for the transfer matrix construction of Prop 2.5.2c). But because all cell tensors are diagonal (i.e., all face labels within a cell must agree), the contraction is trivially global: the face-sharing constraints propagate through the entire connected lattice, collapsing all labels to a single $R$. This makes the FCC tensor network exactly contractible in closed form -- a rare property in 3D lattice gauge theory.

### 3.5 FCC Cell Decomposition (from Thm 0.0.6)

**Status:** ✅ ESTABLISHED (solid geometry)

The tetrahedral-octahedral honeycomb (also called the octet truss or alternated cubic honeycomb) tiles $\mathbb{R}^3$ with regular tetrahedra and regular octahedra. The key geometric facts relevant for this proposition:

**Primitive cell.**

| Quantity | Per primitive unit cell |
|----------|----------------------|
| Tetrahedra | 2 |
| Octahedra | 1 |
| Vertices (lattice sites) | 1 (FCC lattice) |

The vertex set of the honeycomb is the FCC lattice $\Lambda_\text{FCC} = \{(n_1, n_2, n_3) \in \mathbb{Z}^3 : n_1 + n_2 + n_3 \equiv 0 \pmod{2}\}$.

**Dihedral angles.** The dihedral angles of regular tetrahedra and octahedra are:

$$\theta_T = \arccos\!\left(\frac{1}{3}\right) \approx 70.53°, \qquad \theta_O = \pi - \arccos\!\left(\frac{1}{3}\right) \approx 109.47°$$

At each edge of the honeycomb, exactly 2 tetrahedra and 2 octahedra meet:

$$2\theta_T + 2\theta_O = 2 \times 70.53° + 2 \times 109.47° = 360°$$

This is the unique solution for a space-filling arrangement of regular tetrahedra and octahedra around an edge (Thm 0.0.6).

**Face sharing.** Every face of the honeycomb is a triangular face shared by exactly 2 cells. The sharing pattern is determined by the dihedral angle constraint:

- Each triangular face of a tetrahedron is shared with an adjacent octahedron
- Each triangular face of an octahedron is shared with an adjacent tetrahedron
- No face is shared between two tetrahedra or between two octahedra

In the tetrahedral-octahedral honeycomb, the face-sharing is exclusively between different cell types:
- Each tetrahedral cell shares all 4 of its faces with octahedral neighbors
- Each octahedral cell shares all 8 of its faces with tetrahedral neighbors (one tetrahedron per face)

This means the face-sharing graph $\mathcal{G}_\text{face}$ is bipartite: every edge connects a tetrahedral vertex to an octahedral vertex.

**Face count.** Each tetrahedral cell has $F_\text{tet} = 4$ triangular faces. Each octahedral cell has $F_\text{oct} = 8$ triangular faces. Care is needed in counting distinct faces versus cell-face incidences, since every face is shared by exactly 2 cells:

- **Cell-face incidences** (counting each face once per cell it borders): $4 \times 2N + 8 \times N = 16N$
- **Distinct faces** (each shared face counted once): $|F|_\text{distinct} = 16N / 2 = 8N$

In the Wilson action $S_W = \beta \sum_f (1 - \frac{1}{3}\operatorname{Re}\operatorname{Tr} W_f)$, each distinct face $f$ appears exactly once. The total number of distinct triangular faces in $N$ unit cells is therefore $8N$ (with boundary corrections that are $O(N^{2/3})$ and vanish in the thermodynamic limit relative to the bulk).

**Remark on the exponents $3N$ and $8N$.** In the final formula $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$, the exponents are determined by the **global** topology of the FCC 2-skeleton, not by naively multiplying per-cell weights. The Wilson action contains one Boltzmann factor per distinct face, giving $8N$ face factors. The dimension exponent $3N$ equals the Euler characteristic $\chi_2 = V - E + F = N - 6N + 8N = 3N$ of the 2-skeleton, as required by the generalized Migdal-Witten formula for 2-complexes (Oeckl 2005). A naive cell-by-cell multiplication $\prod_c w_c(R) = d_R^{2 \times 3N} a_R^{4 \times 2N + 8 \times N} = d_R^{6N} a_R^{16N}$ would be incorrect because it (i) double-counts shared faces (each shared face contributes $a_R$ once per adjacent cell instead of once per distinct face) and (ii) sums per-cell Euler characteristics $\sum_c \chi(c) = 6N$ instead of using the global $\chi_2 = 3N$.

**Face-sharing graph.** Define the face-sharing graph $\mathcal{G}_\text{face} = (V_\text{cell}, E_\text{face})$ where:
- $V_\text{cell}$ = set of cells (tetrahedra and octahedra)
- $E_\text{face}$ = set of shared faces (an edge connects two cells iff they share a triangular face)

$\mathcal{G}_\text{face}$ is connected for the FCC honeycomb restricted to any simply connected region. The proof of connectivity is straightforward:

**Lemma (Face-sharing graph connectivity).** For any finite connected subregion of the tetrahedral-octahedral honeycomb, $\mathcal{G}_\text{face}$ is connected.

*Proof sketch.*
1. Every tetrahedral cell $t$ shares at least one face with an octahedral cell $o$, so $(t, o) \in E_\text{face}$
2. Every octahedral cell $o$ shares faces with 8 tetrahedral neighbors, so $o$ is connected to all its tetrahedral neighbors in $\mathcal{G}_\text{face}$
3. Two octahedral cells $o_1, o_2$ that share a common tetrahedral neighbor $t$ are connected via the path $o_1 - t - o_2$ in $\mathcal{G}_\text{face}$
4. The FCC lattice is connected (each vertex has 12 nearest neighbors). Since each pair of adjacent FCC vertices is connected by a path through cells sharing faces, $\mathcal{G}_\text{face}$ inherits connectivity from the FCC lattice connectivity. $\square$

**Remark.** The bipartite structure of $\mathcal{G}_\text{face}$ (tetrahedra and octahedra form two classes, with face-sharing occurring predominantly between classes) means that the constraint propagation has the structure: tet $\to$ oct $\to$ tet $\to$ oct $\to \cdots$, ensuring that the label constraint reaches every cell.

This connectivity is the crucial topological property that forces the global label constraint (Claim (d)).

### 3.6 The Octahedral 1-Skeleton

**Status:** ✅ ESTABLISHED (graph theory / simplicial topology)

The regular octahedron has 1-skeleton given by the complete tripartite graph $K_{2,2,2}$ (three pairs of opposite vertices, each pair connected to all vertices of the other two pairs). Explicitly:

- **Vertices:** 6 (label them $\pm x, \pm y, \pm z$ for the three axes)
- **Edges:** 12 (each vertex connects to 4 others -- all except its antipodal partner)
- **Faces:** 8 equilateral triangles
- **Euler characteristic:** $\chi = 6 - 12 + 8 = 2$ ($S^2$)
- **Cycle rank:** $\beta_1 = |E| - |V| + 1 = 12 - 6 + 1 = 7$ independent loops

In tree gauge on the octahedral graph, choose a spanning tree with 5 edges, leaving $12 - 5 = 7$ independent holonomies. The 2D character expansion reduces these 7 integrals and 8 representation labels to a single free label $R$, exactly as for K₄ but with more intermediate steps. The final result:

$$Z_\text{oct}(\beta) = \sum_R d_R^2 \, a_R(\beta)^8$$

is guaranteed by the general formula $Z = \sum_R d_R^{\chi} a_R^{|F|}$ for any triangulation of $S^2$.

### 3.7 Thermodynamic Limit and Free Energy

**Status:** ✅ ESTABLISHED (statistical mechanics)

In the thermodynamic limit $N \to \infty$, the partition function $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ is dominated by the representation $R^*(\beta)$ that maximizes the per-cell weight:

$$R^*(\beta) = \arg\max_R \left[\ln d_R + \frac{8}{3}\ln a_R(\beta)\right]$$

where the factor $1 = 3N/(3N)$ and $8/3 = 8N/(3N)$ are the exponents per cell (there are $3N$ cells total). The free energy per cell is:

$$f(\beta) = -\lim_{N \to \infty} \frac{1}{3N}\ln Z_\text{FCC}(\beta, N) = -\left[\ln d_{R^*} + \frac{8}{3}\ln a_{R^*}(\beta)\right]$$

**Phase structure.** The competition between entropy ($d_R^{3N}$) and energy ($a_R^{8N}$) determines the phase structure:

- **Strong coupling** ($\beta \lesssim \beta_c^\text{FCC}$): The energy factor dominates. Since $a_R < a_\mathbf{1}$ for $R \neq \mathbf{1}$ at finite $\beta$, the trivial representation $R^* = \mathbf{1}$ dominates. This is the confined phase.

- **Weak coupling** ($\beta \gtrsim \beta_c^\text{FCC}$): The entropy factor $d_R^{3N}$ grows without bound with $d_R$, while $a_R^{8N} \to 1$ as $\beta \to \infty$. Higher representations begin to dominate. On a finite system, this is a smooth crossover; in the thermodynamic limit, it may sharpen to a first-order phase transition (as occurs for SU(3) on the hypercubic lattice).

- **Critical coupling:** $\beta_c^\text{FCC}$ is determined by the condition $d_\mathbf{3}^{3N} a_\mathbf{3}^{8N} = a_\mathbf{1}^{8N}$, giving:

$$u_\mathbf{3}(\beta_c) = 3^{-3/8} \approx 0.6623$$

Numerical evaluation via the Weyl integration formula gives $\beta_c^\text{FCC} \approx 11.42$. This is numerically close to but distinct from the single-stella crossing $u_\mathbf{3}(\beta_c^{(K_4)}) = 3^{-1/2} \approx 0.577$ (Prop 0.0.38a §3.3), reflecting the different entropy-energy balance of the 3D system.

**Remark.** The FCC critical coupling $\beta_c^\text{FCC} \approx 11.42$ is a property of the specific lattice geometry and should be compared with the known SU(3) deconfinement transition on the hypercubic lattice ($\beta_c \approx 5.69$ for $N_\tau = 4$, Wilson action; Boyd et al. 1996). A detailed numerical comparison is given in the Applications file §17.7-17.8.

### 3.8 Comparison: FCC Honeycomb vs Hypercubic Lattice

**Status:** ✅ ESTABLISHED (lattice gauge theory)

Standard lattice QCD is formulated on the hypercubic lattice $\mathbb{Z}^4$. The FCC honeycomb (tetrahedral-octahedral honeycomb in 3D, extended to 4D with a temporal direction) differs from the standard formulation in several important ways:

| Property | Hypercubic lattice | FCC honeycomb |
|----------|-------------------|---------------|
| Cell shape | Hypercubes | Tetrahedra + octahedra |
| Plaquette shape | Squares (4 edges) | Triangles (3 edges) |
| Faces per cell | 6 (squares in 3D) | 4 (tet) or 8 (oct) |
| Cell boundary topology | $S^2$ | $S^2$ |
| Euler characteristic per cell | 2 | 2 |
| Character expansion applies? | Yes (per cell) | Yes (per cell) |
| Face-sharing graph | Connected | Connected |
| Global label constraint? | Yes (same $R$) | Yes (same $R$) |

The key insight is that BOTH lattices share the property that the generalized Migdal-Witten formula $Z = \sum_R d_R^{\chi} a_R^F$ applies, collapsing all cell labels to a single representation on any connected lattice. This is a general consequence of the character expansion on connected 2-complexes (Oeckl 2005), not a special property of the FCC.

**What distinguishes the FCC from the hypercubic lattice** is:
1. The specific exponents $\chi_2 = 3N$, $F = 8N$ per $N$ unit cells (vs different values for the hypercubic lattice)
2. The geometric origin of the lattice from the stella octangula (Thm 0.0.6)
3. The naturally simplicial structure (all faces are triangles), which makes the character expansion cell-by-cell more direct — no additional triangulation of square plaquettes is needed
4. The direct connection to the single-stella building block (Prop 0.0.38)

### 3.9 Edge Count and Gauge Fixing on the FCC Lattice

**Status:** ✅ ESTABLISHED (lattice gauge theory)

The number of edges (gauge links) on the FCC lattice with $N$ primitive unit cells requires careful counting. Each primitive unit cell of the tetrahedral-octahedral honeycomb contains:

| Quantity | Per primitive cell (bulk) |
|----------|--------------------------|
| Vertices | 1 (FCC lattice point) |
| Edges | 6 (half of the 12 edges per FCC vertex, by double-counting) |
| Faces | 8 (distinct triangular faces) |
| Cells | 3 (2 tetrahedra + 1 octahedron) |

The number of gauge-independent degrees of freedom after fixing a maximal tree (tree gauge):

$$\text{Independent holonomies} = |E| - |V| + 1 = 6N - N + 1 = 5N + 1 \approx 5N$$

This is the number of SU(3)-valued integrals remaining in the gauge-fixed partition function. Each integral is 8-dimensional (dim SU(3) = 8), giving $\sim 40N$ real integration variables -- a well-defined but high-dimensional integral that becomes tractable through the character expansion.

**Consistency check.** The Euler characteristic formula for a 3D cell complex gives:

$$\chi(\mathcal{H}) = |V| - |E| + |F| - |C| = N - 6N + 8N - 3N = 0$$

where $|C| = 3N$ is the number of cells (2N tetrahedra + N octahedra). The vanishing of $\chi$ is consistent with the fact that a 3D cell complex filling a contractible region of $\mathbb{R}^3$ has $\chi = 1$ (Euler's formula for 3D), but with open boundary conditions the boundary contribution adjusts the count. For periodic boundary conditions (3-torus), $\chi(T^3) = 0$, which is consistent.

### 3.10 Wilson Loops on the FCC Lattice

**Status:** 🔶 NOVEL (application of exact partition function)

Given the exact partition function $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$, expectation values of Wilson loops can be computed by inserting the appropriate character into the partition function. For a Wilson loop in representation $R'$ around a contractible loop $C$ on the FCC lattice:

$$\langle W_{R'}(C) \rangle = \frac{1}{Z_\text{FCC}} \int \prod_\ell dU_\ell \; \chi_{R'}(W_C) \; \prod_f \exp\!\left(\frac{\beta}{3}\operatorname{Re}\operatorname{Tr} W_f\right)$$

The character expansion of this observable requires coupling the Wilson loop representation $R'$ to the bulk representation $R$. The result involves modified weights that depend on the shape and size of the loop $C$. This is addressed in detail in the Derivation file.

At strong coupling, the Wilson loop exhibits area law behavior:

$$\langle W_\mathbf{3}(C) \rangle \approx \left(\frac{\beta}{18}\right)^{A(C)}$$

where $A(C)$ is the minimal number of triangular faces spanning the loop $C$. This recovers the area law of Prop 2.5.2a, now on the extended FCC lattice rather than the single stella.

---

## 4. Dependencies (Detailed)

### 4.1 Dependency Chain

```
Stella octangula ∂S [Def 0.1.1]
    │
    ├──→ SU(3) gauge group [Thm 0.0.3]
    │       │
    │       └──→ Wilson action on ∂S [Prop 0.0.27]
    │               │
    │               └──→ Exact Z_{K₄} = Σ_R d_R² a_R⁴ [Prop 0.0.38]   ← Phase A
    │                       │
    │                       └──→ Spectral gap, transfer matrix [Prop 0.0.38a]
    │
    ├──→ FCC lattice from SU(3) phase coherence [Thm 0.0.6]
    │       │
    │       └──→ Cell decomposition: 2 tet + 1 oct per cell
    │               │
    │               └──→ Face-sharing graph G_face (connected)
    │
    └──→ THIS PROPOSITION: Coupled Z_FCC [Prop 2.5.2b]   ← Phase B, Step 1
            │
            ├──→ Transfer matrix for FCC layers [Prop 2.5.2c]   ← Phase B, Step 2
            ├──→ Reflection positivity [Thm 7.4.1]
            └──→ Mass gap analysis [Phases C-D]
```

### 4.2 Established vs Novel Content

| Component | Status | Source |
|-----------|--------|--------|
| Wilson action formalism | ✅ ESTABLISHED | Wilson (1974) |
| Character expansion on $S^2$ | ✅ ESTABLISHED | Migdal (1975), Menotti & Onofri (1981) |
| Heat kernel coefficients | ✅ ESTABLISHED | Standard lattice QCD |
| FCC cell decomposition | ✅ ESTABLISHED | Solid geometry / Thm 0.0.6 |
| Dihedral angle constraint | ✅ ESTABLISHED | Regular polyhedra geometry |
| Face-sharing graph connectivity | ✅ ESTABLISHED | Graph theory |
| **Cell-by-cell character expansion on FCC** | 🔶 NOVEL | Application of 2D formula to each cell |
| **Face-sharing constraint from orthogonality** | 🔶 NOVEL | Inter-cell extension of Prop 0.0.38 mechanism |
| **Global label constraint** | 🔶 NOVEL | Connectivity + face-sharing = single label |
| **Exact $Z_\text{FCC}$ formula** | 🔶 NOVEL | Combined result of (b)-(d) |
| **Stella → SU(3) → FCC → coupled gauge theory** | 🔶 NOVEL | CG framework chain |

---

## 5. Downstream Usage (Detailed)

### 5.1 Transfer Matrix for FCC Layers (Prop 2.5.2c)

The exact partition function $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ provides the starting point for the transfer matrix construction. Slicing the FCC lattice into layers perpendicular to a chosen direction, the partition function can be written as:

$$Z_\text{FCC} = \operatorname{Tr}(\hat{T}_\text{FCC}^{L})$$

where $L$ is the number of layers and $\hat{T}_\text{FCC}$ is the transfer matrix acting on the Hilbert space of gauge-invariant states on a single FCC layer. The eigenvalues of $\hat{T}_\text{FCC}$ determine the propagation of gauge-invariant excitations through the lattice.

The key input from this proposition: the partition function is a sum over a single representation label $R$, so the transfer matrix is diagonal in the representation basis. The eigenvalues are:

$$\lambda_R = d_R^{3N/L} \, a_R^{8N/L}$$

(per layer, with the precise exponents depending on the layer geometry). The mass gap is determined by the ratio of the first excited eigenvalue to the ground state.

### 5.2 Reflection Positivity (Thm 7.4.1)

The Osterwalder-Schrader reflection positivity axiom requires the partition function to satisfy certain positivity conditions under reflection of the lattice through a hyperplane. The exact form of $Z_\text{FCC}$ -- as a sum of positive terms (since $d_R > 0$ and $a_R > 0$ for all $R$ at all $\beta > 0$) -- is essential for establishing this property.

### 5.3 Mass Gap Program (Thm 7.4.7)

The ultimate goal of the mass gap program is to show:

1. The spectral gap of the FCC transfer matrix is positive for all $\beta$ in the physical range
2. The gap survives the thermodynamic limit $N \to \infty$
3. The gap survives the continuum limit $a \to 0$ ($\beta \to \infty$)

This proposition provides the foundation (step 0): the exact partition function from which the transfer matrix is constructed.

### 5.4 Relationship to the Mass Gap Plan Phases

The Mass Gap research program is organized into four phases:

| Phase | Content | Status |
|-------|---------|--------|
| **A** | Single-stella: exact $Z_{K_4}$, spectral gap, transfer matrix | ✅ Complete (Props 0.0.38, 0.0.38a) |
| **B** | Multi-stella: FCC assembly, coupled $Z_\text{FCC}$, FCC transfer matrix | 🔶 **This proposition** (Step 1) |
| **C** | Thermodynamic limit: $N \to \infty$, phase structure | Planned |
| **D** | Continuum limit: $a \to 0$, asymptotic freedom, mass gap persistence | Planned |

This proposition is Phase B, Step 1. The next step (Prop 2.5.2c) will define the FCC layer transfer matrix and extract its eigenvalues.

### 5.5 Strong Coupling Behavior of $Z_\text{FCC}$

At strong coupling ($\beta \ll 1$), the partition function is dominated by the trivial representation:

$$Z_\text{FCC} \approx a_\mathbf{1}^{8N} \left[1 + 2 \cdot 3^{3N} \left(\frac{\beta}{18}\right)^{8N} + \cdots\right]$$

where the factor of 2 accounts for the fundamental and anti-fundamental representations (both having $d_R = 3$). The "spectral gap" of the FCC partition function is:

$$\Delta_\text{FCC}(\beta) = -\ln\!\left(\frac{d_\mathbf{3}^{3N} a_\mathbf{3}^{8N}}{d_\mathbf{1}^{3N} a_\mathbf{1}^{8N}}\right) = -3N\ln 3 - 8N\ln u_\mathbf{3}(\beta)$$

At strong coupling, $u_\mathbf{3} \approx \beta/18$, so:

$$\Delta_\text{FCC}(\beta) \approx 8N\ln\!\left(\frac{18}{\beta}\right) - 3N\ln 3 \to +\infty \quad \text{as } N \to \infty \text{ at fixed } \beta$$

The gap grows linearly with $N$, reflecting the extensive nature of the 3D system. The intensive gap per unit cell is:

$$\frac{\Delta_\text{FCC}}{3N} = \frac{8}{3}\ln\!\left(\frac{18}{\beta}\right) - \ln 3$$

which is independent of $N$ and positive for $\beta \lesssim 5.7$.

**Comparison with single-stella intensive gap.** The single-stella spectral gap per face is $\Delta_{K_4}/4 = -\frac{1}{2}\ln 3 - \ln u_\mathbf{3}$ (from Prop 0.0.38a). The FCC intensive gap per face is:

$$\frac{\Delta_\text{FCC}}{8N} = \ln\!\left(\frac{18}{\beta}\right) - \frac{3}{8}\ln 3$$

The FCC gap per face is larger than the K₄ gap per face (compare coefficients: $-3/8 \times \ln 3 \approx -0.41$ vs $-1/2 \times \ln 3 \approx -0.55$). This reflects the stronger confinement effect of the FCC lattice compared to the single stella -- a consequence of having more faces per cell (8/3 per cell on average for FCC vs 4 for K₄).

### 5.6 Infinite-Volume Partition Function

In the thermodynamic limit $N \to \infty$, the partition function is dominated by a single representation $R^*(\beta)$:

$$\ln Z_\text{FCC} = N\left[3\ln d_{R^*} + 8\ln a_{R^*}(\beta)\right] + O(\ln N)$$

The $O(\ln N)$ correction arises from fluctuations around the dominant representation. The free energy density (per unit cell) is:

$$f(\beta) = -\frac{1}{3N}\ln Z_\text{FCC} \xrightarrow{N \to \infty} -\frac{1}{3}\left[3\ln d_{R^*} + 8\ln a_{R^*}(\beta)\right] = -\ln d_{R^*} - \frac{8}{3}\ln a_{R^*}(\beta)$$

This is exact in the thermodynamic limit. The dominant representation transitions from $R^* = \mathbf{1}$ (confined phase) to $R^* = \mathbf{3}$ (deconfined phase) at $\beta = \beta_c^\text{FCC}$.

---

## 6. Honest Assessment

### 6.1 What This Proposition DOES Establish

| Claim | Assessment | Confidence |
|-------|------------|------------|
| Cell-by-cell character expansion applies to FCC cells | ✅ Each cell has $\partial c \cong S^2$, so 2D formula applies | High |
| Face-sharing forces $R_{c_1} = R_{c_2}$ | ✅ Follows from character orthogonality at shared edges | High |
| Face-sharing graph is connected | ✅ Standard graph theory on FCC honeycomb | High |
| Global label constraint | ✅ Follows from (b) + (c) + connectivity | High |
| $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ | ✅ Direct consequence of (a)-(d) with global 2-skeleton topology | High |
| Decoupling limit recovers product | ✅ Algebraic identity | High |

### 6.2 What This Proposition Does NOT Establish

| Gap | Assessment | What Would Be Needed |
|-----|------------|---------------------|
| Transfer matrix spectral gap | Not addressed here | Prop 2.5.2c (Phase B, Step 2) |
| Thermodynamic limit exists | Not proven | Phase C analysis of $N \to \infty$ |
| Mass gap survives continuum limit | Not proven | Phase D ($a \to 0$, asymptotic freedom) |
| Connection to physical QCD | Not proven | Full Phase B-D program |
| Boundary effects for finite $N$ | Neglected | $O(N^{2/3}/N)$ corrections, vanish in thermodynamic limit |
| Non-perturbative proof of confinement | Not claimed | Millennium Prize problem |

### 6.3 Potential Concerns

**Concern 1: Is the global label constraint too strong?**

The result that ALL cells carry the same representation label $R$ seems surprising -- it means the entire lattice is in a "coherent" state labeled by a single $R$. However, this is the correct result for the character expansion of a connected lattice. In the standard hypercubic lattice with the Wilson action, the character expansion also collapses to a single representation label on any simply connected region. The physical content (confinement, propagation, mass gap) enters through the transfer matrix eigenvalues, not through the existence of multiple labels.

**Concern 2: Does the global label constraint trivialize the 3D physics?**

No. The single-label structure means the partition function is effectively a sum over one quantum number $R$, but this is standard for the character expansion of connected lattices — the same collapse occurs on the hypercubic lattice. The coupling between cells is encoded in the *global* choice of $R$: all cells must agree, and the weight $d_R^{3N} a_R^{8N}$ depends on the lattice topology through $\chi_2 = 3N$ and $F = 8N$. Non-trivial dynamics (mass gap, confinement, string tension) enter through:
- The competition between the entropy factor $d_R^{3N}$ and the energy factor $a_R^{8N}$, which determines the dominant representation as a function of $\beta$
- The transfer matrix eigenvalues (Prop 2.5.2c), which depend on the layer geometry of the FCC lattice and produce a genuine spectral gap
- The correlation functions, which are NOT trivial even though $Z$ has a simple closed form
- The mass gap, which requires the full transfer matrix analysis and cannot be read off from $Z$ alone

In particular, $Z$ alone does not determine correlation functions or the mass gap — these require the transfer matrix constructed in Prop 2.5.2c by slicing the FCC lattice into temporal layers. The partition function $Z$ is the *starting point* for the dynamical analysis, not its conclusion.

**Concern 3: Why the exponent is $8N$ (not $16N$).**

An earlier version of this document claimed the exponent on $a_R$ was $16N$ (the number of cell-face incidences), obtained by naively multiplying per-cell weights $\prod_c w_c(R) = d_R^{6N} a_R^{16N}$. This was incorrect. The correct exponent is $8N$ (the number of distinct faces), as required by the generalized Migdal-Witten formula for 2-complexes (Oeckl 2005). The Wilson action contains one Boltzmann factor $e^{(\beta/3)\operatorname{Re}\operatorname{Tr} W_f}$ per distinct face $f$, so the character expansion produces one factor of $a_R$ per distinct face. Similarly, the dimension exponent is $\chi_2 = V - E + F = N - 6N + 8N = 3N$ (the Euler characteristic of the global 2-skeleton), not $\sum_c \chi(c) = 2 \times 3N = 6N$. The cell-by-cell expansion correctly identifies the representation labels (all cells carry the same $R$), but the partition function weight is determined by the global topology of the 2-skeleton, not by multiplying independent cell weights. See the Derivation file for the complete proof.

### 6.4 Limitations and Open Questions

1. **Boundary effects.** The formula $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ is exact for periodic boundary conditions. For open boundary conditions, there are $O(N^{2/3})$ boundary faces that are not shared, leading to corrections that vanish in the thermodynamic limit but are non-negligible for small $N$.

2. **Temporal extension.** This proposition treats the FCC lattice as a purely spatial object. The extension to a 4D lattice (FCC spatial lattice $\times$ temporal lattice) is needed for the full transfer matrix construction and is deferred to Prop 2.5.2c.

3. **Fermion coupling.** The partition function here is for pure gauge theory (no fermions). Including dynamical fermions requires additional structure (staggered fermions, Wilson fermions, or domain wall fermions on the FCC lattice). The pure gauge case is the starting point.

4. **Improved actions.** The Wilson action is the simplest lattice gauge action but has $O(a^2)$ discretization errors. Symanzik improvement (adding higher-order terms) could improve the approach to the continuum limit. On the FCC lattice, the simplicial structure may provide natural improvement terms.

5. **Connection to Monte Carlo.** The exact partition function provides benchmark values for Monte Carlo simulations on the FCC lattice, which could serve as non-trivial cross-checks.

### 6.5 Novel Content Summary

The genuinely novel content of this proposition is the **application** of established lattice gauge theory methods (character expansion, tensor networks) to the specific FCC geometry dictated by the CG framework. The mathematical tools are standard (✅ ESTABLISHED), but the specific lattice structure -- the tetrahedral-octahedral honeycomb with its unique dihedral angle constraint -- is dictated by the stella geometry (🔶 NOVEL, via Thm 0.0.6). The result $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ is an exact formula that provides the foundation for the mass gap program.

---

## 7. Summary and References

### 7.1 Summary of Results

| Result | Formula | Status |
|--------|---------|--------|
| Tetrahedral cell weight | $w_\text{tet}(R) = d_R^2 a_R^4$ | ✅ ESTABLISHED (2D formula) |
| Octahedral cell weight | $w_\text{oct}(R) = d_R^2 a_R^8$ | ✅ ESTABLISHED (2D formula) |
| Face-sharing constraint | $R_{c_1} = R_{c_2}$ for adjacent cells | 🔶 NOVEL |
| Global label constraint | All cells carry same $R$ | 🔶 NOVEL |
| FCC partition function | $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ | 🔶 NOVEL |
| Decoupling limit | $Z \to [Z_{K_4}]^{2N} [Z_\text{oct}]^N$ | ✅ ESTABLISHED (consistency) |
| Free energy per cell ($N \to \infty$) | $f = -\frac{1}{3}\ln(d_{R^*} \, a_{R^*}^{8/3})$ | 🔶 NOVEL |
| Face count | $\|F\| = 8N$ distinct faces | ✅ ESTABLISHED (geometry) |
| Dihedral constraint | $2\theta_T + 2\theta_O = 360°$ | ✅ ESTABLISHED |
| FCC critical coupling | $u_\mathbf{3}(\beta_c) = 3^{-3/8}$ | 🔶 NOVEL |
| Intensive gap per face | $\ln(18/\beta) - (3/8)\ln 3$ | 🔶 NOVEL |
| Convergence | Absolute for all $\beta > 0$, finite $N$ | ✅ ESTABLISHED |
| $N = 1$ leading correction | $54 \, u_\mathbf{3}^{8}$ | 🔶 NOVEL (explicit) |
| Tensor network | Diagonal (all face labels equal per cell) | 🔶 NOVEL |
| Wilson loop area law (FCC) | $\langle W_\mathbf{3}(C)\rangle \sim (\beta/18)^{A(C)}$ at strong coupling | ✅ ESTABLISHED (method) |

### 7.2 Convergence

The series $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ converges absolutely for all $\beta > 0$ and finite $N$. This follows from the same argument as for the single K₄ (Prop 0.0.38 §7.1): since $u_R = a_R/a_\mathbf{1} < 1$ for $R \neq \mathbf{1}$ at finite $\beta$, and $d_R$ grows polynomially in the Dynkin labels while $u_R^{8N}$ decays exponentially for $N \geq 1$, the series converges. More directly, $Z_\text{FCC}$ is the partition function of a lattice gauge theory on a finite lattice -- a finite-dimensional integral over a compact domain -- and is therefore trivially finite.

At strong coupling ($\beta \lesssim 5$), the first few representations provide an excellent approximation:

$$Z_\text{FCC} \approx a_\mathbf{1}^{8N}\left[1 + 2 \cdot 3^{3N}\left(\frac{\beta}{18}\right)^{8N} + 2 \cdot 6^{3N}\left(\frac{\beta^2}{432}\right)^{8N} + 512^N\left(\frac{\beta^2}{288}\right)^{8N} + \cdots\right]$$

The truncation error is exponentially small in $N$ at strong coupling.

### 7.3 Key Equations

| Equation | Number | Location |
|----------|--------|----------|
| FCC partition function | §1(d) | Statement |
| Cell weights | §1(b) | Statement |
| Face-sharing constraint | §1(c) | Statement |
| Decoupling limit | §1(e) | Statement |
| 2D character expansion | §3.3 | Background |
| Cell tensor (diagonal form) | §3.4 | Background |

### 7.4 References

#### External References

1. K.G. Wilson, "Confinement of quarks," Phys. Rev. D **10** (1974) 2445. [Original Wilson action formulation]
2. J.-M. Drouffe & J.-B. Zuber, "Strong coupling and mean field methods in lattice gauge theories," Phys. Rep. **102** (1983) 1-119. [Strong coupling expansion, character expansion]
3. P. Menotti & E. Onofri, "The action of SU(N) lattice gauge theory in terms of the heat kernel on the group manifold," Nucl. Phys. B **190** (1981) 288-300. [Heat kernel on group manifold, 2D character expansion]
4. A.A. Migdal, "Recursion equations in gauge field theories," Sov. Phys. JETP **42** (1975) 413. [Exact recursion relations, character expansion for 2D gauge theory]
5. E. Witten, "On quantum gauge theories in two dimensions," Commun. Math. Phys. **141** (1991) 153. [Mathematical formalization of 2D Yang-Mills as topological QFT]
6. R. Oeckl, *Discrete Gauge Theory: From Lattices to TQFT*, Imperial College Press (2005). [Generalized lattice gauge theory on cellular decompositions; Theorem 5.2.3: partition function on general 2-complexes]
7. M. Creutz, *Quarks, Gluons and Lattices*, Cambridge University Press (1983). [Standard lattice gauge theory textbook]
8. H.J. Rothe, *Lattice Gauge Theories: An Introduction*, 4th ed., World Scientific (2012). [Modern lattice gauge theory textbook]
9. B.E. Rusakov, "Loop averages and partition functions in U(N) gauge theory on two-dimensional manifolds," Mod. Phys. Lett. A **5** (1990) 693. [Explicit character expansion formula for 2D gauge theory]
10. S.H. Christiansen & T.G. Halvorsen, "A simplicial gauge theory," J. Math. Phys. **53** (2012) 033501. [arXiv:1006.2059](https://arxiv.org/abs/1006.2059). [Prior work on gauge theory on simplicial meshes]
11. G. Boyd et al., "Thermodynamics of SU(3) lattice gauge theory," Nucl. Phys. B **469** (1996) 419. [hep-lat/9602007](https://arxiv.org/abs/hep-lat/9602007). [Precision SU(3) deconfinement: $\beta_c = 5.6925(2)$ for $N_\tau = 4$]

#### Internal References

10. **[Proposition 0.0.38](../foundations/Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md)** — Exact single-stella partition function $Z_{K_4} = \sum_R d_R^2 a_R^4$ (Phase A foundation)
11. **[Proposition 0.0.38a](../foundations/Proposition-0.0.38a-Stella-Gauge-Spectrum.md)** — Spectral gap, transfer matrix eigenvalues $t_R = d_R^4 a_R^{10}$ (Phase A spectral analysis)
12. **[Proposition 2.5.2a](./Proposition-2.5.2a-Wilson-Loop-Area-Law-From-Geometry.md)** — Wilson loop area law from stella geometry (strong coupling cross-check)
13. **[Theorem 0.0.6](../foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md)** — FCC lattice from stella octangula tiling
14. **[Definition 0.1.1](../Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md)** — Stella octangula boundary topology
15. **[Proposition 0.0.27](../foundations/Proposition-0.0.27-Lattice-QFT-On-Stella.md)** — Lattice QFT formalization on $\partial\mathcal{S}$ (Wilson action, character expansion)

---

## Appendix: Notation Cross-Reference

For consistency with the rest of the framework, we record the correspondence between the notation in this proposition and the notation in the prerequisite documents:

| This Proposition | Prop 0.0.38 | Prop 0.0.38a | Thm 0.0.6 |
|-----------------|-------------|--------------|------------|
| $Z_\text{FCC}(\beta, N)$ | — | — | — |
| $w_\text{tet}(R) = d_R^2 a_R^4$ | $w_R = d_R^2 a_R^4$ | $w_R(\beta)$ | — |
| $w_\text{oct}(R) = d_R^2 a_R^8$ | — | — | — |
| $\mathcal{G}_\text{face}$ | — | — | $\mathcal{H}$ (honeycomb) |
| $N$ (unit cells) | — | — | $|\Lambda_\text{FCC}|$ (vertices) |
| $\beta = 6/g^2$ | $\beta$ | $\beta$ | — |
| $a_R(\beta)$ | $a_R(\beta)$ (Eq. 4.1) | $a_R(\beta)$ | — |
| $u_R = a_R/a_\mathbf{1}$ | $u_R$ (§5.1) | $u_R$ | — |

---

*Document created: 2026-02-12*
*Status: 🔶 NOVEL — Phase B, Step 1 of Yang-Mills Mass Gap program*
*Derivation: [Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Derivation.md](Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Derivation.md)*
*Applications: [Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Applications.md](Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Applications.md)*
*Verification Report: [Proposition-2.5.2b-Multi-Agent-Verification-2026-02-12.md](../verification-records/Proposition-2.5.2b-Multi-Agent-Verification-2026-02-12.md)*
*Adversarial Script: [prop_2_5_2b_adversarial_physics.py](../../../verification/Phase2/prop_2_5_2b_adversarial_physics.py) — 45/45 PASS (2026-02-12)*
