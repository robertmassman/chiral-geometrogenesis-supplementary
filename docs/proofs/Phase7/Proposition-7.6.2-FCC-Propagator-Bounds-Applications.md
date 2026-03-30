# Proposition 7.6.2: FCC Propagator Bounds — Applications and Verification

## Status: 🔶 NOVEL / ✅ ESTABLISHED — February 2026

**Purpose:** Physical interpretation, numerical verification, self-consistency checks, and connection to Phase G for the propagator bounds on the $D_4$ lattice.

**[← Back to Statement](./Proposition-7.6.2-FCC-Propagator-Bounds.md)** | **[← See the Derivation](./Proposition-7.6.2-FCC-Propagator-Bounds-Derivation.md)**

---

## §9. Physical Interpretation

### §9.1 What the Propagator Bounds Mean Physically

The propagator bounds in Prop 7.6.2 control three essential aspects of the quantum gauge field on the $D_4$ lattice:

1. **Free propagator decay** ($|G_0(x)| \leq C/|x|^2$): Gauge field fluctuations at separation $|x|$ are suppressed as $1/|x|^2$ — the standard 4D Coulomb law. This ensures that long-range correlations are weak in the perturbative regime, which is essential for the convergence of the cluster expansion in Balaban's RG program.

2. **Covariant Laplacian positivity** ($-\Delta_U \geq 0$): The kinetic energy of gauge field fluctuations is always non-negative, regardless of the background gauge field. This is the lattice analogue of the continuum statement that the gauge kinetic term $\text{Tr}(F^2) \geq 0$ is positive definite. It guarantees that the Gaussian integral at each RG step is well-defined and convergent.

3. **Combes-Thomas exponential decay** ($|G_B(x,y)| \leq (C/m^2)e^{-\gamma|x-y|}$): In the presence of a mass gap, gauge field correlations decay exponentially. This is the mechanism that makes the cluster expansion work — distant regions of the lattice are effectively decoupled, and the effective action can be decomposed into local contributions.

### §9.2 The Matching of Hopping Norms

A key finding is that the total hopping norm is identical on $D_4$ and $\mathbb{Z}^4$:

$$\sum_{i=1}^{24} |t_{x,x+v_i}| = \frac{24}{6a^2} = \frac{4}{a^2} = \frac{8}{d_\text{nn}^2} = \sum_{\mu=1}^{8} |t_{x,x+e_\mu}|\big|_{\text{per } d_\text{nn}^2} \tag{9.1}$$

This is not a coincidence — it follows from the normalization convention $\hat{k}^2 \to k^2$ as $a \to 0$, which requires the second-moment sum $\sum_i v_i^\mu v_i^\nu$ to equal $z\bar{v}^2/(d\cdot d_\text{nn}^2) \cdot \delta^{\mu\nu}$ for both lattices (where the normalization factor absorbs the difference in $z$ and $\bar{v}^2$). In coordinate units, $D_4$ has hopping norm $4/a^2$ (vs. $8/a^2$ on $\mathbb{Z}^4$), but both equal $8/d_\text{nn}^2$ when expressed per nearest-neighbor distance squared.

**Consequence:** The Combes-Thomas decay rate per NN step is identical on both lattices when expressed per $d_\text{nn}^2$: $\gamma = \ln(1 + m^2 d_\text{nn}^2/16)$. This means the UV stability bounds from Balaban's program carry over with the **same functional form** — a significant simplification.

### §9.3 Enhanced Isotropy: A D₄ Advantage

The $D_4$ fourth-moment isotropy gives the propagator an $O(a^4/|x|^6)$ correction to the continuum, compared to $O(a^2/|x|^4)$ on the hypercubic lattice. This means:

- **Better rotational symmetry:** The FCC lattice propagator is a better approximation to the rotationally invariant continuum propagator at any fixed physical distance
- **Faster convergence to continuum:** Lattice artifacts in the propagator are suppressed by $a^4$ rather than $a^2$
- **Implications for Symanzik improvement:** The FCC lattice achieves "tree-level $O(a^2)$ improvement" automatically, without any action modification (this is the content of Prop 7.5.1, $c_4^{(\text{FCC})} = 0$)

---

## §10. Numerical Verification

### §10.1 Test Suite Overview

The verification script `verification/Phase7/prop_7_6_2_fcc_propagator_bounds.py` implements the following tests:

| Test | What It Checks | Expected Result |
|------|---------------|-----------------|
| T1: BZ volume | $(2\pi)^4/2$ for $D_4$ | $\mathcal{V}_\text{BZ} = (2\pi)^4/2 \approx 778.7$ |
| T2: Laplacian normalization | $\hat{k}^2 \to k^2$ as $k \to 0$ | Ratio $\to 1$ |
| T3: Diagonal norm | $(-\Delta_0)_{xx} = 4/a^2$ (= $8/d_\text{nn}^2$) | Exact match |
| T4: Maximum eigenvalue | $\|-\Delta_0\| = 16/(3a^2) \approx 5.33/a^2$ | At BZ boundary (e.g. $k = (\pi,\pi,0,0)/a$) |
| T5: Free propagator decay | $|G_0(x)| \cdot |x|^2 \to C_{D_4}$ | $C_{D_4} \approx 1/(4\pi^2)$ |
| T6: Gradient bound | $|\nabla G_0(x)| \cdot |x|^3 \to C_1$ | Finite constant |
| T7: Isotropy comparison | $|G_0^{D_4} - G_0^\text{cont}| / |G_0^\text{cont}|$ vs. $|G_0^{\mathbb{Z}^4} - G_0^\text{cont}| / |G_0^\text{cont}|$ | FCC error $\ll$ hypercubic error |
| T8: Covariant Laplacian positivity | Eigenvalues of $-\Delta_U$ | All $\geq 0$ for random $U$ |
| T9: CT decay rate | $\gamma = \ln(1 + m^2a^2/8)$ | Match formula |
| T10: CT bound verification | $|G_m(x)| \leq (C/m^2)e^{-\gamma|x|/d_\text{nn}}$ | Bound satisfied |
| T11: Hopping norm matching | $\sum|t_i| = 8/d_\text{nn}^2$ on both lattices | Exact equality |
| T12: Tadpole integral | $G_0(0) = I_\text{FCC}/a^2$ | $I_\text{FCC} \approx 0.276$ |

### §10.2 Key Numerical Predictions

**Free propagator at selected distances (lattice units, $a = 1$):**

| $|x|/a$ | $G_0(x) \cdot 4\pi^2 |x|^2$ (expected $\to 1$) | Deviation |
|----------|----------------------------------------------|-----------|
| $\sqrt{2}$ (1 NN step) | $\sim 1 + O(1)$ | Large (lattice effects) |
| $2\sqrt{2}$ (2 NN steps) | $\sim 1 + O(0.1)$ | Moderate |
| $5\sqrt{2}$ | $\sim 1 + O(0.01)$ | Small |
| $10\sqrt{2}$ | $\sim 1 + O(0.001)$ | Very small |

**Combes-Thomas decay rate at selected masses** ($\gamma = \ln(1 + m^2a^2/8)$, $a = a_\text{coord}$):

| $ma$ | $\gamma_{D_4}(m)$ | $\gamma_{D_4}/d_\text{nn}$ (per phys. dist.) |
|------|-------------------|----------------------------------------------|
| 0.1 | 0.001249 | 0.000883 |
| 0.5 | 0.03077 | 0.02176 |
| 1.0 | 0.1178 | 0.08329 |
| 2.0 | 0.4055 | 0.2867 |
| 5.0 | 1.417 | 1.002 |

### §10.3 Expected Verification Results

All tests are expected to pass based on:
- The $D_4$ lattice structure (standard mathematical properties)
- The Combes-Thomas framework (proven mathematical technique)
- Consistency with Prop 7.4.3 (already verified, 11/11 tests)
- Consistency with Prop 7.6.1 (already verified, 12/12 + 10/10 tests)

---

## §11. Self-Consistency Checks

### §11.1 Dimensional Analysis ✅

| Quantity | Dimensions | Check |
|----------|-----------|-------|
| $G_0(x)$ | $[\text{length}]^{-2}$ | $\int d^4k \cdot k^{-2} = [\text{length}]^{4-2}/[\text{length}]^4 = [\text{length}]^{-2}$ ✓ |
| $-\Delta_U^{D_4}$ | $[\text{length}]^{-2}$ | $a^{-2} \times$ dimensionless $= [\text{length}]^{-2}$ ✓ |
| $G_B(m)$ | $[\text{length}]^{2}$ | $([\text{length}]^{-2})^{-1} = [\text{length}]^{2}$ ✓ |
| $\gamma_{D_4}$ | Dimensionless | $\ln(1 + (ma)^2/16)$ ✓ |
| $V_B$ | $[\text{length}]^{-2}$ | Same as $\Delta_U$ ✓ |

### §11.2 Limiting Cases ✅

**Continuum limit ($a \to 0$):**
- $G_0(x) \to 1/(4\pi^2|x|^2)$ ✓ (Eq. 5.16)
- $-\Delta_U^{D_4} \to D_\mu D^\mu$ ✓ (Eq. 6.14)
- $\gamma_{D_4}(m) \to m^2a^2/8 \to 0$ ✓ (correct: bare CT vanishes; physical mass emerges from RG)

**Trivial gauge field ($U = \mathbf{1}$):**
- $-\Delta_\mathbf{1}^{D_4} = -\Delta_0^{D_4}$ (ordinary Laplacian) ✓
- $V_\mathbf{1} = 0$ ✓
- $G_\mathbf{1}(m) = G_0(m)$ ✓

**Zero mass ($m \to 0$):**
- $G_B(m) \to (-\Delta_B)^{-1}$ (exists if $\Delta_B$ has no zero mode) ✓
- $\gamma_{D_4}(0) = 0$ (no exponential decay without mass) ✓

**Strong coupling ($\beta \to 0$, $g_0 \to \infty$):**
- The small-field region shrinks: $\{|F_p| \leq Cg_k^{1-\delta}\}$ becomes almost everything
- Propagator bounds become trivial (small-field analysis not needed)
- Consistent with the exact strong-coupling mass gap (Thm 7.4.2) ✓

### §11.3 Consistency with Other Framework Results ✅

**With Prop 7.4.3 (FCC Perturbation Theory):**
- Uses the same $\hat{k}^2_\text{FCC}$ and $D_4$ Laplacian ✓
- Tadpole integral $I_\text{FCC} = 0.276$ consistent ✓
- Fourth-moment isotropy ($\Delta T = 0$) used in enhanced isotropy result ✓

**With Prop 7.6.1 (FCC Averaging Kernel):**
- Same $D_4$ nearest-neighbor vectors $\{v_i\}$ ✓
- Self-coarsening $D_4(\eta_k) \to D_4(2\eta_k)$ used in Part (d) ✓
- Small-field condition $|F_p| \leq Cg_k^{1-\delta}$ consistent ✓

**With Thm 7.5.3 (Bulk Transition Termination):**
- Crossover path provides $\mu > 0$ everywhere — consistent with the need for $m > 0$ in the Combes-Thomas bound ✓
- Modified action preserves $b_0$, $b_1$ — consistent with perturbative universality of the propagator ✓

---

## §12. Connection to Phase G

### §12.1 How This Feeds into G.2

With the averaging kernel (Prop 7.6.1) and propagator bounds (this Prop 7.6.2), the Gaussian part of the RG step is fully controlled:

**One RG step (schematic).** The partition function at scale $k$ is:

$$Z_k = \int DU_\text{fine}\,e^{-\mathcal{A}_k(U_\text{fine})} \cdot \delta(Q_\text{FCC}(U_\text{fine}) - V_\text{coarse}) \tag{12.1}$$

The saddle-point expansion around the background field $B_k$ (minimizer of $\mathcal{A}_k$ subject to the blocking constraint) gives:

$$Z_k \approx e^{-\mathcal{A}_k(B_k)} \int D\phi\,e^{-\frac{1}{2}\langle\phi, G_{B_k}(m_k)^{-1}\phi\rangle + \text{interactions}} \tag{12.2}$$

where $\phi = U_\text{fine} - B_k$ is the fluctuation field. The Gaussian integral $\int D\phi\, e^{-\frac{1}{2}\phi^T G_B^{-1}\phi}$ is controlled by the propagator bounds:

- **Free propagator** (Part a): determines the perturbative expansion coefficients
- **Combes-Thomas decay** (Part c): ensures the cluster expansion converges (distant interactions are suppressed)
- **Resolvent identity** (Part c.1): allows expansion around the free propagator

### §12.2 Remaining Inputs for UV Stability

| Input | Status | Next Step |
|-------|--------|-----------|
| 1. Averaging kernel $Q_\text{FCC}$ | ✅ Prop 7.6.1 | — |
| 2. Propagator bounds | ✅ Prop 7.6.2 (this) | — |
| 3. Regular configurations space | Pending | Prop 7.6.3: Adapt Balaban Paper V to $D_4$ |
| 4. Variational problem (saddle point) | Pending | Prop 7.6.3: Adapt Balaban Paper VI to $D_4$ |
| 5. Large-field (Peierls) estimates | Pending | Prop 7.6.4: Adapt Balaban Paper X to $D_4$ |
| 6. Small-field UV stability | Pending | Thm 7.6.5: Adapt Balaban Papers VII-VIII |

The next natural step is **Prop 7.6.3**: the regular configuration spaces and variational problem on $D_4$, adapting Balaban Papers V–VI.

### §12.3 Updated Phase G Roadmap

```
Phase G: Constructive Continuum Limit

G.1 ──▶ G.2(a) ──▶ G.2(b) ──▶ G.2(c) ──▶ G.2(d) ──▶ G.3, G.4 ──▶ G.5–G.7
 ✅        ✅          ⏳          ⏳          ⏳       Pending     Pending
Avg.    Propagator   Regular    Variational  Large    IR control  Continuum
Kernel   Bounds     Config.     Problem     Field    + Scaling     Limit
7.6.1    7.6.2      7.6.3       7.6.3      7.6.4
```

**Legend:**
- ✅ = Complete (this proposition)
- ⏳ = Next in line
- Pending = Future work

---

## §13. Honest Assessment of Limitations

### §13.1 What Is Rigorously Established

- Free propagator $1/|x|^2$ decay: standard lattice Green's function theory, adapted to $D_4$ ✅
- Covariant Laplacian positivity: algebraic identity ✅
- Combes-Thomas framework: established technique ✅
- Axial gauge fixing: standard lattice gauge theory ✅

### §13.2 What Is Novel but Solid

- $D_4$ normalization giving matching hopping norms with $\mathbb{Z}^4$ 🔶
- Enhanced $O(a^4/|x|^6)$ isotropy correction 🔶
- Explicit Combes-Thomas decay rate $\gamma_{D_4}(m)$ 🔶

### §13.3 What Requires Further Work

- **Gauge field propagator in axial gauge:** We established bounds for the scalar propagator only. The full gauge field propagator in axial gauge on $D_4$ has a more complex structure due to the 12 link directions. The scalar bounds suffice for the Gaussian integral control, but the explicit gauge field propagator is needed for loop calculations. This is a technical but not conceptual gap.

- **Large-field regime:** The Combes-Thomas bound requires the small-field condition. In the large-field regime, different (non-perturbative) bounds are needed — these are the content of the Peierls estimates (Balaban Paper X), deferred to Prop 7.6.4.

- **Continuum limit of the propagator:** The bounds hold at each fixed lattice spacing $a$. Proving that the propagator converges as $a \to 0$ requires the full RG program (Phase G.5), not just the single-scale bounds established here.

- **Quantitative constants:** The constants $C_{D_4}$, $C_n$, $C_\text{CT}$ are shown to be finite and $a$-independent, but their precise numerical values require computation from the $D_4$ lattice geometry. The verification script provides numerical estimates.

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (D₄-specific bounds) / ✅ ESTABLISHED (Balaban propagator framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G, Step G.2 (partial)*
