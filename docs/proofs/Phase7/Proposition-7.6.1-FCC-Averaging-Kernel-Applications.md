# Proposition 7.6.1: FCC Averaging Kernel — Applications

## Navigation

| File | Purpose | Sections |
|------|---------|----------|
| [Proposition-7.6.1-FCC-Averaging-Kernel.md](./Proposition-7.6.1-FCC-Averaging-Kernel.md) | Statement & motivation | §1–4, §9–10 |
| [Proposition-7.6.1-FCC-Averaging-Kernel-Derivation.md](./Proposition-7.6.1-FCC-Averaging-Kernel-Derivation.md) | Complete derivation | §5–8, Appendices |
| **Proposition-7.6.1-FCC-Averaging-Kernel-Applications.md** (this file) | Verification & physics | §9–12 |

---

## §9. Physical Interpretation

### §9.1 Role of the Averaging Kernel in the RG Flow

The averaging kernel $Q_\text{FCC}$ is the geometric engine of the multi-scale renormalization group. At each RG step, it performs three conceptual operations:

1. **Coarse-graining:** Maps the $D_4(\eta_k)$ gauge field to $D_4(2\eta_k)$, reducing the number of degrees of freedom by a factor of 16 (the coset index)
2. **Smoothing:** Averages over 25 fine-lattice paths per coarse link, suppressing short-wavelength fluctuations while preserving long-wavelength physics
3. **Gauge-covariant projection:** Maintains exact SU(3) gauge symmetry at every step via the projection $\text{Proj}_{SU(3)}$

The entire Balaban RG iteration has the structure:

$$\mathcal{A}_{k+1}(V) = -\ln \int \prod_\ell dU_\ell\, \exp(-\mathcal{A}_k(U))\, \delta(Q_\text{FCC}(U) - V) \tag{9.1}$$

where $\mathcal{A}_k$ is the effective action at scale $k$ and $V$ is the coarse field. The delta function imposes the blocking constraint, and the integral over $U$ integrates out the "fast" modes. The kernel $Q_\text{FCC}$ enters as the blocking constraint.

### §9.2 How the 24-Cell Geometry Improves Averaging

The FCC/D₄ lattice offers structural advantages over the hypercubic lattice for the averaging operation:

**More averaging paths (25 vs. ~13).** The higher coordination number ($z = 24$) provides more independent paths per coarse link. Each 3-step detour path samples the gauge field in a different direction, providing more information about the local field strength. The average over more paths is statistically more stable and has better cancellation properties.

**D₄ fourth-moment isotropy.** The exact isotropy of the $D_4$ fourth-moment tensor (Lemma 6.3.1, Prop 7.4.3) means that the averaged field preserves rotational symmetry at $O(a^2)$. On the hypercubic lattice, the averaging kernel inherits the lattice's $O(a^2)$ rotational breaking, which must be corrected by Symanzik improvement. On FCC, no such correction is needed at leading order.

**Self-coarsening.** The $D_4 \to D_4$ blocking preserves the lattice type, ensuring that the same kernel applies at every scale. This is the same structural advantage that the hypercubic lattice has ($\mathbb{Z}^4 \to \mathbb{Z}^4$), but with the additional benefit of $D_4$ isotropy at each step.

### §9.3 Connection to Block-Spin Transformations

The averaging kernel $Q_\text{FCC}$ is the gauge-theory analogue of the Kadanoff block-spin transformation in statistical mechanics. The key differences are:

| Property | Block-spin (Ising) | Gauge averaging ($Q_\text{FCC}$) |
|----------|-------------------|--------------------------------|
| Variables | Scalar spins $\sigma_i \in \{-1, +1\}$ | $SU(3)$ link matrices |
| Averaging | Majority vote / spatial average | Path-averaging + SU(3) projection |
| Symmetry | Global $\mathbb{Z}_2$ | Local $SU(3)$ gauge symmetry |
| Covariance | Trivial | Non-trivial (Eq. 6.3) |
| Blocking factor | $L = 2$ | $L = 2$ |
| Sites per cell | $2^d = 16$ | $[D_4 : 2D_4] = 16$ |

The gauge covariance requirement — absent in scalar theories — is what makes the non-Abelian averaging kernel technically challenging. Balaban's Theorem 3.1 (CMP 98, 1985) resolves this by showing that any path-based average automatically preserves gauge symmetry.

---

## §10. Numerical Verification

### §10.1 Verification Script

The verification script `prop_7_6_1_fcc_averaging_kernel.py` performs 12 independent tests. All 12 pass.

### §10.2 Test Results Summary

| Test | Claim | Result | Status |
|------|-------|--------|--------|
| 1 | $[D_4:2D_4] = 16$ | 16 cosets found | ✅ PASS |
| 2 | Coset completeness | 16 distinct representatives cover all $D_4$ points | ✅ PASS |
| 3 | Voronoi cell: 16 fine sites per coarse cell | Origin cell has 16 sites | ✅ PASS |
| 4 | Path count: 1 (2-step) + 24 (3-step) = 25 | Confirmed for $(1,1,0,0)$ and $(1,-1,0,0)$ | ✅ PASS |
| 5 | Path validity: intermediate sites in $D_4$ | All 24 three-step paths checked | ✅ PASS |
| 6 | Gauge covariance: $Q(U^g) = Q(U)^{g'}$ | Error $= 9.1 \times 10^{-16}$ | ✅ PASS |
| 7 | Trivial field: $Q(\mathbb{1}) = \mathbb{1}$ | Error $= 0$ | ✅ PASS |
| 8 | Small perturbation scaling | Deviations decrease with $\varepsilon$ | ✅ PASS |
| 9 | SU(3) projection: $\det Q = 1$, $QQ^\dagger = \mathbb{1}$ | Max error $< 10^{-15}$ | ✅ PASS |
| 10 | Self-coarsening: blocked $D_4$ is $D_4$ | 24 NN vectors, all in $2D_4$ | ✅ PASS |
| 11 | $D_4$ fourth-moment isotropy | Max deviation $= 4.4 \times 10^{-16}$ | ✅ PASS |
| 12 | $C_\text{avg}$ comparison: FCC vs cubic | Both finite, $O(1)$; ratio $\approx 1.87$ (equal-weight convention) | ✅ PASS |

### §10.3 Key Numerical Values

| Quantity | Value | Source |
|----------|-------|--------|
| $[D_4 : 2D_4]$ | 16 | Test 1 (exact) |
| Paths per coarse direction | 25 (1 + 24) | Test 4 (exact) |
| Gauge covariance error | $9.1 \times 10^{-16}$ | Test 6 (machine precision) |
| $C_\text{avg}^{\text{FCC}} / C_\text{avg}^{\text{cubic}}$ | $\approx 1.87$ (equal-weight) | Test 12 (note: comparison is approximate since $\mathbb{Z}^4$ detours are 4-step vs $D_4$ 3-step) |
| Fourth-moment isotropy error | $4.4 \times 10^{-16}$ | Test 11 (machine precision) |

---

## §11. Self-Consistency Checks

### §11.1 Dimensional Analysis

The smallness bound (Part c) in lattice units ($\eta_k = 1$) states:

$$\|Q_\text{FCC}(U) - U_\text{direct}\| \leq C_\text{avg} \cdot g_k^{1-\delta}$$

Checking dimensions in lattice units:
- $\|Q - U\|$: dimensionless (matrix norm of SU(3) elements) ✓
- $C_\text{avg} \approx 2.49\, C_F$: dimensionless (geometry-dependent constant) ✓
- $g_k^{1-\delta}$: dimensionless (power of the dimensionless gauge coupling) ✓

The bound is dimensionless throughout. ✓

**Physical-unit consistency.** In physical units, the lattice link variable encodes the gauge connection as $U_{x,x+v} = P\exp(ig_k \eta_k \int A_\mu v^\mu\, ds)$, where $A_\mu$ has dimension $[\text{mass}]$. The plaquette variable satisfies $U_p - \mathbb{1} \approx ig_k \eta_k^2 F_{\mu\nu}^{\text{phys}} \Sigma_p^{\mu\nu}$, where $F_{\mu\nu}^{\text{phys}}$ has dimension $[\text{mass}]^2$ and the factor $g_k \eta_k^2$ renders $U_p - \mathbb{1}$ dimensionless. The small-field condition $|F_p| \leq C g_k^{1-\delta}$ constrains the dimensionless plaquette deviation, so the bound remains dimensionless regardless of the physical value of $\eta_k$. ✓

**Note on Balaban's $\eta_k^{d/2}$ convention.** In some formulations of Balaban's program, bounds are written as $O(g_k \cdot \eta_k^{d/2})$ to track the lattice-spacing dependence explicitly when comparing fields at different scales. In lattice units ($\eta_k = 1$ at each scale), this factor is unity and does not appear. The $\delta$ exponent in $g_k^{1-\delta}$ is the more fundamental quantity: it controls how tightly the small-field region constrains the gauge field fluctuations.

### §11.2 Limiting Cases

**$g_k \to 0$ (weak coupling):** The bound $\|Q - U_\text{direct}\| \leq C_\text{avg}\, g_k^{1-\delta} \to 0$. In the free-field limit, all link variables are $\mathbb{1}$, and $Q = \mathbb{1} = U_\text{direct}$. Consistent. ✓

**$\eta_k \to 0$ (continuum limit):** As the lattice spacing vanishes, the gauge field becomes smooth and all plaquette deviations $|F_p| \to 0$. The small-field condition is trivially satisfied and the bound $\|Q - U_\text{direct}\| \to 0$. Consistent. ✓

**$g_k \to \infty$ (strong coupling):** The bound breaks down, as expected. The small-field condition $|F_p| \leq C g_k^{1-\delta}$ is no longer meaningful when $g_k^{1-\delta}$ is large. This is the regime where the large-field analysis (Balaban Paper X) is needed. Consistent. ✓

### §11.3 Consistency with Prop 7.5.1 Symanzik Expansion

The Symanzik expansion (Prop 7.5.1) classifies lattice artifacts at each order in $a$. The averaging kernel introduces $O(a^2)$ corrections through the path-averaging procedure. The key consistency check is:

**The $O(a^2)$ rotational-breaking artifact vanishes for $Q_\text{FCC}$.** This follows from the $D_4$ fourth-moment isotropy (Prop 7.5.1 Part c): the coefficient $c_4^{(\text{FCC})} = 0$ at $O(a^2)$. The averaging kernel inherits this isotropy because:
1. The path set $P(\hat{n})$ is $W(D_4)$-symmetric for each direction $\hat{n}$
2. The sum over paths preserves the fourth-moment isotropy of the direction set
3. The SU(3) projection does not break rotational symmetry

Therefore, the averaged field $Q_\text{FCC}(U)$ on the coarse lattice has the same Symanzik structure as the fine-lattice field — with vanishing rotational breaking at $O(a^2)$. ✓

### §11.4 Consistency with Research Note §4.3

The [Research Note: Balaban RG Adaptation to FCC](../supporting/Research-Note-Balaban-RG-Adaptation-FCC.md) §4.3 identified the averaging operation as the **hardest** component to adapt. This proposition resolves the adaptation by:

1. Constructing the explicit blocking decomposition ($D_4/2D_4 = 16$) — §5
2. Defining the path-based averaging kernel with 25 paths per direction — §6
3. Proving gauge covariance using Balaban's Theorem 3.1 — §6.3
4. Establishing the smallness bound with explicit $C_\text{avg}$ — §7
5. Verifying the four inductive requirements — §8.3

The Research Note's estimate that the averaging deviation is $O(g_k)$ in the small-field region is confirmed with the explicit FCC-specific bound $\|Q(U) - U_\text{direct}\| \leq C_\text{avg}\, g_k^{1-\delta}$, where $C_\text{avg} \approx 2.49\, C_F$. ✓

---

## §12. Connections and Forward-Looking

### §12.1 What Phase G.2 (UV Stability) Needs from This Kernel

Phase G.2 will establish UV stability for the FCC lattice gauge theory, adapting Balaban Papers VII–IX. The key inputs from this proposition are:

1. **The blocking map $Q_\text{FCC}$** — defines the RG transformation
2. **The smallness bound** (Part c) — controls the difference between fine and coarse fields in the small-field region
3. **Gauge covariance** (Part b) — ensures the effective action at each scale is gauge-invariant
4. **Self-similarity** (Part d) — enables the inductive argument across scales

Specifically, the RG transformation at scale $k$ is:

$$e^{-\mathcal{A}_{k+1}(V)} = \int \prod_\ell dU_\ell\, e^{-\mathcal{A}_k(U)}\, \delta(Q_\text{FCC}(U) - V) \tag{12.1}$$

The delta function constraint is evaluated by saddle-point expansion (Balaban Paper VI). The saddle point is the "background field" $B$ minimizing $\mathcal{A}_k(U)$ subject to $Q_\text{FCC}(U) = V$. The fluctuation integral around the saddle point is controlled by the propagator bounds (Balaban Papers I–II, IV) adapted to FCC geometry.

### §12.2 Preview of the Variational Problem (Paper VI Adaptation)

The next geometric input needed is the **variational problem**: given a coarse field $V$ on $D_4(2\eta)$, find the fine-lattice background field $B$ on $D_4(\eta)$ that minimizes the action subject to $Q_\text{FCC}(B) = V$.

On the hypercubic lattice, Balaban (Paper VI, CMP 102, 1985) shows that:
- The minimizer exists and is unique in the small-field region
- The minimizer satisfies lattice gauge-field equations with the constraint
- Perturbative expansion around the coarse field gives controlled corrections

On the FCC lattice, the variational problem involves:
- The FCC Wilson action (triangular plaquettes)
- The constraint $Q_\text{FCC}(B) = V$ using our 25-path kernel
- The FCC Hessian (second variation of the triangular plaquette action)

This is a natural next step (future Prop 7.6.2) building directly on the kernel constructed here.

### §12.3 Preview of UV Stability Argument

The full UV stability argument (Phase G.2) proceeds inductively. At each scale $k$:

1. **Block average:** Apply $Q_\text{FCC}$ to map $D_4(\eta_k) \to D_4(2\eta_k)$
2. **Saddle-point expansion:** Find background field $B_k$ minimizing action with blocking constraint
3. **Fluctuation integral:** Integrate out the fluctuation $\xi_k = U - B_k$ using the propagator at scale $k$
4. **Small-field/large-field decomposition:** Control the integral in both regions
5. **Renormalization:** Extract the running coupling $g_{k+1}^2$ and irrelevant operators

The self-coarsening property of $D_4$ (Part d) ensures that **all geometric inputs are identical at every scale**: same kernel, same propagator structure, same Voronoi cell, same path counts. This makes the FCC inductive argument structurally identical to Balaban's hypercubic argument — with different numerical constants but the same functional form.

### §12.4 Summary: Where This Proposition Fits

```
Phase F (Universality)          Phase G (Constructive Continuum Limit)
━━━━━━━━━━━━━━━━━━━━           ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Prop 7.5.1 (Symanzik)          ┌─────────────────────────────────┐
  Thm 7.5.2 (Universality)  ──▶ │ Prop 7.6.1 (Averaging Kernel)   │ ◀── G.1
  Thm 7.5.3 (Crossover)         │ [THIS PROPOSITION]               │
  Research Note (Balaban)        └───────────┬─────────────────────┘
                                             │
                                             ▼
                                 ┌─────────────────────────────────┐
                                 │ Prop 7.6.2 (Variational Problem) │ ◀── G.1 (cont.)
                                 └───────────┬─────────────────────┘
                                             │
                                             ▼
                                 ┌─────────────────────────────────┐
                                 │ UV Stability (Papers VII-IX)     │ ◀── G.2
                                 └───────────┬─────────────────────┘
                                             │
                                             ▼
                                 ┌─────────────────────────────────┐
                                 │ IR Control (mass gap regulator)  │ ◀── G.4
                                 └───────────┬─────────────────────┘
                                             │
                                             ▼
                                 ┌─────────────────────────────────┐
                                 │ Continuum Limit + Mass Gap       │ ◀── G.7
                                 └─────────────────────────────────┘
```

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (FCC-specific) / ✅ ESTABLISHED (Balaban framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G, Step G.1*
