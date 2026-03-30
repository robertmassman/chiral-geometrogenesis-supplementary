# Proposition 7.6.3: Regular Configurations and Variational Problem — Applications

## Navigation

| File | Purpose | Sections |
|------|---------|----------|
| [Proposition-7.6.3-Regular-Configurations-Variational-Problem.md](./Proposition-7.6.3-Regular-Configurations-Variational-Problem.md) | Statement & motivation | §1–4, §9–10 |
| [Proposition-7.6.3-Regular-Configurations-Variational-Problem-Derivation.md](./Proposition-7.6.3-Regular-Configurations-Variational-Problem-Derivation.md) | Complete derivation | §5–8, Appendices |
| **Proposition-7.6.3-Regular-Configurations-Variational-Problem-Applications.md** (this file) | Verification & physics | §9–12 |

---

## §9. Numerical Verification

### §9.1 Test Suite Overview

The verification script `verification/Phase7/prop_7_6_3_regular_configs_variational.py` tests the key claims of Prop 7.6.3. The tests are organized by proposition part:

| Test ID | Part | Description | Status |
|---------|------|-------------|--------|
| T1 | (a) | Plaquette count: 96 per vertex on $D_4$ | Expected: PASS |
| T2 | (a) | Plaquettes per link: 8 on $D_4$ | Expected: PASS |
| T3 | (a) | Plaquette inner product condition $v_i \cdot v_j = 1$ | Expected: PASS |
| T4 | (a) | Openness: perturbed configs remain in/outside $\Omega_k^s$ | Expected: PASS |
| T5 | (a) | Contractibility: homotopy preserves small-field bound | Expected: PASS |
| T6 | (a) | Gauge invariance: $\|U_p^g - \mathbb{1}\| = \|U_p - \mathbb{1}\|$ | Expected: PASS |
| T7 | (b) | Gauge fixing: spanning tree on small $D_4$ lattice | Expected: PASS |
| T8 | (b) | Independent variable count: $11 N_V + 1$ | Expected: PASS |
| T9 | (c) | Variational problem: embedding approximation $Q(V^{\text{embed}}) \approx V$ | Expected: PASS |
| T10 | (c) | Regularity preservation: $B_*$ satisfies fine small-field condition | Expected: PASS |
| T11 | (d) | Hessian lower bound: positive definite in gauge-fixed sector | Expected: PASS |
| T12 | (d) | Hessian upper bound: bounded by massive Laplacian | Expected: PASS |
| T13 | (d) | Hessian constant $c_H \approx \sqrt{3}/4 \approx 0.433$ | Expected: PASS |

### §9.2 Test Details

**T1: Plaquette count per vertex.** Generate the 24 NN vectors of $D_4$. For each pair $(v_i, v_j)$, check if $v_i \cdot v_j = 1$ and $|v_i - v_j|^2 = 2$. Count ordered pairs and divide by 2 (each plaquette counted from each of its three vertices).

Expected result: $24 \times 8 / 2 = 96$ unordered plaquettes per vertex.

**T2: Plaquettes per link.** For a fixed link direction $v_i = (1,1,0,0)$, count the number of $v_j$ with $v_i \cdot v_j = 1$.

Expected result: 8 plaquettes per link.

**T3: Inner product condition.** Verify that every pair $(v_i, v_j)$ of $D_4$ NN vectors with $v_i \cdot v_j = 1$ satisfies $|v_i - v_j|^2 = 2$ (so $v_i - v_j$ is also a NN vector, confirming the triangle is equilateral).

**T4: Openness test.** Generate a random small-field configuration $U$ with $\|U_p - \mathbb{1}\| \leq 0.9 p_0 g_k^{1-\delta}$ (inside $\Omega_k^s$). Perturb $U$ slightly ($\epsilon = 0.01$). Verify the perturbed config remains in $\Omega_k^s$. Generate a config at the boundary and verify that a larger perturbation can push it out.

**T5: Contractibility homotopy.** Generate a random small-field config. Apply $h_t(U)_\ell = \exp(t \log U_\ell)$ for $t \in \{0, 0.25, 0.5, 0.75, 1.0\}$. Verify $\max_p \|h_t(U)_p - \mathbb{1}\|$ decreases monotonically and equals 0 at $t = 0$.

**T6: Gauge invariance.** Generate a random gauge transformation $g$ and small-field config $U$. Compute $\|U_p^g - \mathbb{1}\|$ and $\|U_p - \mathbb{1}\|$ for all plaquettes. Verify they are equal to machine precision.

**T7: Spanning tree.** Construct a small $D_4$ lattice (e.g., $L = 4$ with periodic BCs). Build a spanning tree by BFS. Verify: tree has $N_V - 1$ edges, tree is connected, all vertices reached.

**T8: Variable count.** On the $L = 4$ lattice, compute $N_V$ (number of $D_4$ sites in the periodic box), $N_E$ (total links), $N_E - (N_V - 1)$ (independent links in axial gauge). Verify $N_E = 12 N_V$ and independent links $= 11 N_V + 1$.

**T9: Embedding approximation.** Construct a random coarse field $V$ satisfying the coarse small-field condition. Embed via $V^{\text{embed}}$ (§7.2 of Derivation). Apply $Q_\text{FCC}$. Measure $\|Q_\text{FCC}(V^{\text{embed}}) - V\|$ and verify it is $O(g_k^2)$.

**T10: Regularity preservation.** Starting from $V^{\text{embed}}$, apply a Newton iteration to solve the constrained minimization (numerically). Verify the resulting $B_*$ satisfies $\|B_{*,p} - \mathbb{1}\| \leq C_{\text{reg}} g_k^{1-\delta}$ with $C_{\text{reg}} \leq 2 p_0$.

**T11–T12: Hessian bounds.** Construct the Hessian matrix numerically at $B_*$ on a small lattice. Compute eigenvalues. Compare with $c_H / g_k^2 \cdot \text{spec}(-\Delta_{B_*}^{D_4})$ (lower bound) and $C_H/g_k^2 \cdot \text{spec}(-\Delta_{B_*}^{D_4} + m_k^2)$ (upper bound).

**T13: Hessian constant verification.** Compute $c_H$ numerically from the ratio of the smallest Hessian eigenvalue to the corresponding covariant Laplacian eigenvalue, scaled by $g_k^2$. Verify $c_H \approx \sqrt{3}/4 = 0.433$.

---

## §10. Consistency Checks

### §10.1 Dimensional Analysis

| Quantity | Dimensions (lattice units, $\eta_k = 1$) | Verification |
|----------|------------------------------------------|-------------|
| $\|U_p - \mathbb{1}\|$ | Dimensionless | Matrix norm of $SU(3)$ element ✓ |
| $p_0 g_k^{1-\delta}$ | Dimensionless | Product of dimensionless constants ✓ |
| $\mathcal{S}_\text{FCC}$ | Dimensionless | Action is always dimensionless ✓ |
| $Q_\text{FCC}(B)$ | $SU(3)$-valued | Maps links to links ✓ |
| $\mathcal{H}_k$ | $\eta_k^{-2}$ (in $g_k^{-2}$ units) | Second derivative of action ✓ |
| $-\Delta_{B_*}^{D_4}$ | $\eta_k^{-2}$ | Laplacian has dimensions of inverse length squared ✓ |
| $c_H, C_H$ | Dimensionless | Ratio of quadratic forms ✓ |

### §10.2 Limiting Cases

**$g_k \to 0$ (weak coupling).** The small-field region $\Omega_k^s$ shrinks (tighter plaquette bound), but the background field $B_*$ approaches the embedding $V^{\text{embed}}$ (corrections are $O(g_k^2)$). The Hessian approaches $(c_H/g_k^2)(-\Delta_{B_*}^{D_4})$ with $c_H \to \sqrt{3}/4$. This is the free-field (Gaussian) limit, consistent with asymptotic freedom.

**$g_k \to g_*$ (edge of small-field regime).** The regularity constant $p_0 g_k^{1-\delta}$ approaches $O(1)$, and the link variables can be far from $\mathbb{1}$. The contractibility proof still works (as long as $p_0 g_k^{1-\delta} < \pi/2$ for the logarithm to be defined). The Hessian corrections $C_1 g_k^{1-\delta}$ become $O(1)$, weakening the lower bound — this is where the large-field analysis (Prop 7.6.4) takes over.

**Hypercubic limit.** If we replace $D_4$ plaquettes (triangular) with $\mathbb{Z}^4$ plaquettes (square), the regularity constant becomes $p_0^{\text{cubic}}$, the plaquette count becomes 24/vertex and 6/link, the Hessian leading factor becomes $1/4$ (from square plaquette area), and all results reduce to Balaban's original Paper IV–VI statements.

### §10.3 Comparison with Balaban's Hypercubic Results

| Result | Balaban (Hypercubic) | This Work (FCC/$D_4$) | Ratio |
|--------|---------------------|------------------------|-------|
| Plaquettes/vertex | 24 | 96 | 4.0 |
| Plaquettes/link | 6 | 8 | 1.33 |
| Regularity constant | $p_0^{\text{cubic}}$ | $2p_0^{\text{cubic}}/\sqrt{3} \approx 1.15\, p_0^{\text{cubic}}$ | 1.15 |
| Hessian leading factor | $1/4$ | $\sqrt{3}/4 \approx 0.433$ | $\sqrt{3} \approx 1.73$ |
| Independent links/vertex | 3 | 11 | 3.67 |
| Gauge-fixed dim./vertex | $3 \times 8 = 24$ | $11 \times 8 = 88$ | 3.67 |
| Constraint dim./vertex | $2$ | $6$ | 3.0 |
| Fluctuation dim./vertex | $24 - 2 = 22$ | $88 - 6 = 82$ | 3.73 |

**Dimension breakdown.** On $\mathbb{Z}^4$ with factor-2 blocking: $3N_V + 1$ gauge-fixed links give $24N_V + 8$ real parameters. The coarse lattice $\mathbb{Z}^4(2\eta)$ has $N_V/16$ vertices and $4 \times N_V/16 = N_V/4$ undirected coarse links, giving $2N_V$ constraint parameters (i.e., $(N_V/4) \times 8$), or $2$ per fine vertex. Fluctuation dimensions per vertex: $24 - 2 = 22$. On $D_4$: $11N_V + 1$ gauge-fixed links give $88N_V + 8$ real parameters; coarse $D_4(2\eta)$ has $12 \times N_V/16 = 3N_V/4$ undirected coarse links, giving $6N_V$ constraint parameters, or $6$ per fine vertex; fluctuations $= 88 - 6 = 82$ per vertex. The ratio of fluctuations to constraints is $22/2 = 11$ on $\mathbb{Z}^4$ and $82/6 \approx 13.7$ on FCC — both large, confirming the saddle-point approximation is well-justified on both lattices, with the FCC ratio slightly more favorable.

### §10.4 Self-Consistency of the Hessian Bounds

The Hessian bounds from Part (d) must be consistent with the propagator bounds from Prop 7.6.2:

**Check 1:** The Hessian lower bound $c_H/g_k^2 \cdot (-\Delta_{B_*}^{D_4})$ implies the fluctuation propagator satisfies:

$$\langle \phi_\ell \phi_{\ell'} \rangle \leq \frac{g_k^2}{c_H}\, G_{B_*}(x_\ell, x_{\ell'}) \tag{10.1}$$

Using the Combes-Thomas bound (Prop 7.6.2, Part (c)):

$$\langle \phi_\ell \phi_{\ell'} \rangle \leq \frac{C g_k^2}{c_H m_k^2}\, e^{-\gamma_{D_4}(m_k) |x_\ell - x_{\ell'}|/(\eta_k\sqrt{2})} \tag{10.2}$$

This gives exponential decay of the fluctuation correlator — essential for the cluster expansion in the next RG step.

**Check 2:** The Hessian determinant satisfies:

$$\ln \det \mathcal{H}_k = \sum_i \ln \lambda_i(\mathcal{H}_k) = \operatorname{Tr} \ln \mathcal{H}_k \tag{10.3}$$

Using the Hessian bounds:

$$\operatorname{Tr} \ln \left[\frac{c_H}{g_k^2}(-\Delta_{B_*}^{D_4})\right] \leq \operatorname{Tr} \ln \mathcal{H}_k \leq \operatorname{Tr} \ln \left[\frac{C_H}{g_k^2}(-\Delta_{B_*}^{D_4} + m_k^2)\right] \tag{10.4}$$

The log-determinant controls the one-loop correction to the effective action. The difference between upper and lower bounds is:

$$\operatorname{Tr} \ln(1 + m_k^2 (-\Delta_{B_*}^{D_4})^{-1}) + O(g_k^{1-\delta}) \times N_V \tag{10.5}$$

which is bounded and contributes a local (extensive) correction to the effective action — consistent with the Symanzik improvement program (Prop 7.5.1).

---

## §11. Physical Interpretation

### §11.1 The Small-Field Region as the Perturbative Domain

The small-field region $\Omega_k^s$ is the domain where the gauge field is "close to vacuum" — the field strength is bounded by $O(g_k^{1-\delta})$, which vanishes as $g_k \to 0$ (weak coupling). In this region:

- The Wilson action can be expanded around the trivial vacuum $U = \mathbb{1}$
- The Hessian is positive (the action is convex)
- The saddle-point (Gaussian) approximation is justified
- Perturbative corrections are organized in powers of $g_k^2$

The boundary $\partial \Omega_k^s$ is where the field strength reaches $O(g_k^{1-\delta})$ — large enough for non-perturbative effects to become relevant but still parametrically smaller than $O(1)$ (the strong-field regime).

### §11.2 Physical Content of the Variational Problem

The background field $B_*$ is the **most probable configuration** on the fine lattice that is compatible with the observed coarse-grained field $V$. It is the "classical solution" around which quantum fluctuations are expanded.

The Hessian $\mathcal{H}_k$ determines the **stiffness of the fluctuations**: large eigenvalues mean the fluctuations are tightly constrained (small amplitude), while small eigenvalues correspond to "soft modes" with large fluctuations.

The lower bound $\mathcal{H}_k \geq (c_H/g_k^2)(-\Delta_{B_*}^{D_4})$ ensures that **all modes are massive** (in the gauge-fixed sector) — there are no zero modes or near-zero modes that could destabilize the expansion. This is physically reasonable: at each RG scale, the mass gap $\mu(\beta) > 0$ provides an infrared cutoff, and the gauge fixing eliminates the flat directions.

### §11.3 The Triangular Plaquette Advantage

The $D_4$ lattice has 96 triangular plaquettes per vertex (vs. 24 square plaquettes on $\mathbb{Z}^4$). This has both advantages and disadvantages for the constructive program:

**Advantages:**
- **More action terms per link:** Each link participates in 8 plaquettes (vs. 6 on $\mathbb{Z}^4$), giving a larger action penalty for large-field configurations. This strengthens the Peierls bounds (Prop 7.6.4).
- **Better isotropy:** The triangular plaquettes, combined with $D_4$ fourth-moment isotropy, provide $O(a^4)$ rotational artifacts (vs. $O(a^2)$ on $\mathbb{Z}^4$).
- **Higher Hessian coefficient:** The leading Hessian factor $\sqrt{3}/4 \approx 0.433$ is larger than the hypercubic factor $1/4 = 0.25$ by a factor of $\sqrt{3}$, giving stronger convexity.

**Disadvantages:**
- **More constraints:** The 96 plaquette conditions are more restrictive, potentially making $\Omega_k^s$ smaller.
- **More complex variational problem:** The constraint $Q_\text{FCC}(B) = V$ involves 25 paths per direction (each with up to 3 steps), compared to ~41 paths (4-step) on $\mathbb{Z}^4$.

Overall, the advantages dominate: the stronger convexity and better isotropy more than compensate for the larger number of constraints.

### §11.4 Connection to the RG Iteration

At each RG step, the effective action is computed as:

$$e^{-\mathcal{A}_{k+1}(V)} = \int_{\Omega_k^s} dU\, e^{-\mathcal{S}_\text{FCC}(U)} \delta(Q_\text{FCC}(U) - V) + \int_{\Omega_k^\ell} dU\, e^{-\mathcal{S}_\text{FCC}(U)} \delta(Q_\text{FCC}(U) - V) \tag{11.1}$$

**Small-field contribution (this proposition):** The first integral is evaluated by saddle-point expansion around $B_*$:

$$\int_{\Omega_k^s} \approx e^{-\mathcal{S}(B_*)} \cdot (\det \mathcal{H}_k)^{-1/2} \cdot \exp\!\left(\sum_{n \geq 1} g_k^{2n} C_n[V]\right) \tag{11.2}$$

where $C_n[V]$ are connected Feynman diagram contributions (the "perturbative corrections"). The Hessian bounds ensure this integral is well-defined and produces a finite, smooth function of $V$.

**Large-field contribution (Prop 7.6.4):** The second integral is bounded by Peierls estimates:

$$\int_{\Omega_k^\ell} \leq e^{-c/g_k^2 \cdot |\Omega_k^\ell|} \tag{11.3}$$

The combined effective action $\mathcal{A}_{k+1}(V)$ has the same structure as $\mathcal{S}_\text{FCC}$ (Wilson action form) plus irrelevant operators and counterterms — this is the content of Balaban's UV stability theorem (future Thm 7.6.5).

---

## §12. Connections to Other Propositions

### §12.1 Backward Dependencies

| Dependency | What is used | Where |
|------------|-------------|-------|
| Prop 7.4.3 | $D_4$ NN vectors, fourth-moment isotropy | Plaquette counting (§5.1), Hessian isotropy (§8.2) |
| Prop 7.5.1 | BCH expansion for triangular plaquettes | Plaquette expansion (§5.2, §8.1) |
| Prop 7.6.1 | Averaging kernel $Q_\text{FCC}$, 25 paths/direction | Constraint in variational problem (§7.1) |
| Prop 7.6.2 | Covariant Laplacian, Combes-Thomas bounds | Hessian bounds (§8.2–8.5) |
| Thm 7.5.3 | Crossover path, $\mu > 0$ | Operating environment (mass gap provides IR control) |

### §12.2 Forward Connections

| Enabled Result | What is provided | How |
|----------------|-----------------|-----|
| Prop 7.6.4 (Large-Field Estimates) | Boundary of $\Omega_k^s$ | Peierls estimates on $\Omega_k^\ell = \mathcal{A}_k \setminus \Omega_k^s$ |
| Thm 7.6.5 (Small-Field UV Stability) | Full small-field analysis | Saddle-point expansion with controlled Hessian |
| Phase G.4 (IR Control) | Regularity preservation under RG | $B_* \in \Omega_k^s$ ensures regularity propagates |

### §12.3 Consistency with Phase F Results

The regularity constant $p_0^{D_4} = 2p_0^{\text{cubic}}/\sqrt{3}$ is consistent with the Symanzik analysis (Prop 7.5.1): the leading irrelevant operator on the FCC lattice enters at $O(a^4)$, not $O(a^2)$, so the regularity threshold can be slightly relaxed compared to the hypercubic lattice. The ratio $p_0^{D_4}/p_0^{\text{cubic}} \approx 1.15$ is modest and does not affect the qualitative conclusions.

The Hessian constant $c_H = \sqrt{3}/4$ is consistent with the universality analysis (Thm 7.5.2): in the continuum limit, the second variation of the Yang-Mills action is the same on both lattices (Laplacian + curvature terms), and the lattice-specific Hessian constants are absorbed into the running coupling. The ratio $c_H^{D_4}/c_H^{\text{cubic}} = \sqrt{3}$ appears because the FCC plaquette area is $\sqrt{3}/2$ times the hypercubic plaquette area, but the FCC lattice has proportionally more plaquettes — the net effect cancels in the continuum limit.

---

## §13. Open Questions and Future Work

### §13.1 Questions Resolved by This Proposition

- **Q:** Can the small-field region be defined consistently on $D_4$ with triangular plaquettes? **A:** Yes, with regularity constant $p_0^{D_4} = 2p_0^{\text{cubic}}/\sqrt{3}$ (§5.2).
- **Q:** Does the variational problem have a unique solution on $D_4$? **A:** Yes, by strict convexity + implicit function theorem (§7.4).
- **Q:** Is the Hessian controlled by the covariant Laplacian? **A:** Yes, with explicit bounds $c_H = \sqrt{3}/4 \cdot (1 + O(g_k^{1-\delta}))$ (§8.2–8.3).

### §13.2 Questions for Prop 7.6.4 (Large-Field Estimates)

- What is the Peierls entropy for connected large-field regions on $D_4$ ($z = 24$ vs. $z = 8$ on $\mathbb{Z}^4$)?
- Does the higher plaquette density (96 vs. 24 per vertex) provide sufficient action penalty to compensate the larger entropy?
- What is the explicit Peierls threshold $g_k^*$ below which the small-field/large-field decomposition is valid?

### §13.3 Questions for Thm 7.6.5 (UV Stability)

- Can the one-loop effective action be computed explicitly on $D_4$, including the log-determinant of the Hessian?
- Do the FCC-specific Feynman diagram contributions (from the 96-plaquette action) produce different counterterms than the hypercubic case?
- Is the FCC effective action analytic in $g_k^2$ uniformly in the lattice size?

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (D₄ construction) / ✅ ESTABLISHED (Balaban framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G, Step G.2b*
