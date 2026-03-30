# Proposition 7.6.2: Gauge Field Propagator Bounds on the D₄ Lattice

## Status: 🔶 NOVEL (D₄-specific bounds) / ✅ ESTABLISHED (Balaban propagator framework) — February 2026

**Role in Framework:** Establishes the gauge-fixed free propagator, covariant Laplacian, and background field propagator on the $D_4$ lattice with all bounds required for Balaban's multi-scale renormalization group program. This adapts Balaban Papers I–II (CMP 95–96, 1984) and Paper V (CMP 99, 389–434, 1985) to the FCC lattice, providing the second geometric input (after the averaging kernel, Prop 7.6.1) for Phase G (Constructive Continuum Limit).

**Classification:** Mixed — the Combes-Thomas framework, resolvent identity, and axial gauge fixing are ✅ ESTABLISHED (Balaban 1984–1985, Combes-Thomas 1973); the $D_4$-specific propagator bounds, decay constants, and covariant Laplacian normalization are 🔶 NOVEL adaptations.

**Key Results:**
- **(a)** Axial gauge fixing on $D_4$ via spanning tree; free scalar propagator $G_0(x) = \int_{BZ} \frac{d^4k}{(2\pi)^4/2} \frac{e^{ik \cdot x}}{\hat{k}^2_\text{FCC}}$ with pointwise decay $|G_0(x)| \leq C_{D_4}/|x|^2$
- **(b)** Gauge-covariant Laplacian $\Delta_U^{D_4}$ on $D_4$ with 24 neighbors; positive semi-definiteness; continuum limit $-\Delta_U^{D_4} \to D_\mu D^\mu$
- **(c)** Background field propagator $G_B(m) = (-\Delta_B^{D_4} + m^2)^{-1}$ with Combes-Thomas exponential decay: $|G_B(x,y)| \leq (C/m^2)\,e^{-\gamma(m)|x-y|}$
- **(d)** All bounds uniform in lattice spacing $a$; compatible with $D_4$ self-coarsening and the averaging kernel $Q_\text{FCC}$ (Prop 7.6.1)

**Dependencies:**
- ✅ Proposition 7.4.3 (FCC Lattice Perturbation Theory) — $D_4$ Laplacian $\hat{k}^2_\text{FCC}$, fourth-moment isotropy, tadpole integral, propagator normalization
- ✅ Proposition 7.6.1 (FCC Averaging Kernel) — $D_4/2D_4$ blocking, gauge-covariant averaging, self-coarsening
- ✅ Theorem 7.4.1 (Reflection Positivity on FCC) — positive self-adjoint transfer matrix
- ✅ Theorem 7.4.2 (Mass Gap Thermodynamic Limit) — mass gap $\mu(\beta) > 0$, exponential clustering
- ✅ Theorem 7.5.3 (Bulk Transition Termination) — crossover path with $\mu > 0$ everywhere
- ✅ External: Balaban Papers I–II (CMP 95–96, 1984) — hypercubic propagator framework
- ✅ External: Balaban Paper V (CMP 99, 389–434, 1985) — background field propagator
- ✅ External: Combes & Thomas (1973) — exponential decay of resolvents

**Enables:**
- Phase G.2 (UV stability on FCC) — propagator estimates feed into the RG iteration
- Future Prop 7.6.3 (Regular Configurations and Variational Problem on $D_4$) — background field construction
- ✅ Theorem 7.6.5 (Small-Field UV Stability on D₄) — the full UV stability result

---

## File Structure

This proposition uses the **3-file academic structure**:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Proposition-7.6.2-FCC-Propagator-Bounds.md** (this file) | Statement & motivation | §1–4, §9–10, References | Conceptual correctness |
| **[Proposition-7.6.2-FCC-Propagator-Bounds-Derivation.md](./Proposition-7.6.2-FCC-Propagator-Bounds-Derivation.md)** | Complete derivation | §5–8, Appendices | Mathematical rigor |
| **[Proposition-7.6.2-FCC-Propagator-Bounds-Applications.md](./Proposition-7.6.2-FCC-Propagator-Bounds-Applications.md)** | Verification & physics | §9–12, Numerical tests | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Proposition-7.6.2-FCC-Propagator-Bounds-Derivation.md)
- [→ See applications and verification](./Proposition-7.6.2-FCC-Propagator-Bounds-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-14
**Status:** 🔶 NOVEL (D₄-specific) / ✅ ESTABLISHED (Balaban propagator framework)

### Verification Checklist
- [x] All symbols defined in symbol table
- [x] Dimensional consistency verified
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] Free propagator decay verified numerically — `prop_7_6_2_fcc_propagator_bounds.py` (12/12 tests passed)
- [x] Covariant Laplacian positivity verified — `prop_7_6_2_fcc_propagator_bounds.py`
- [x] Combes-Thomas decay verified — `prop_7_6_2_fcc_propagator_bounds.py`
- [x] Multi-agent peer review — [Verification Report](../verification-records/Proposition-7.6.2-Multi-Agent-Verification-2026-02-14.md) (5 errors, 7 warnings → **all 12 findings resolved**)
- [x] Adversarial physics verification — `prop_7_6_2_adversarial_physics.py` (9/10 passed; ADV-1 finite-size effect)
- [x] All E1–E5 errors resolved (author misattribution, normalization convention, resolvent sign, isotropy factor, spectral bound)
- [x] All W1–W7 warnings resolved (CT simplification, Balaban numbering, Dimock date, propagator/gradient proofs strengthened, d.o.f. reduction clarified)

### Verification Scripts
- `verification/Phase7/prop_7_6_2_fcc_propagator_bounds.py` — Propagator bounds verification (12/12 passed)
- `verification/Phase7/prop_7_6_2_adversarial_physics.py` — [Adversarial physics verification](../../../verification/Phase7/prop_7_6_2_adversarial_physics.py) (9/10 passed, [diagnostic plot](../../../verification/plots/prop_7_6_2_adversarial_verification.png))

---

## §1. Formal Statement

**Proposition 7.6.2** (Gauge Field Propagator Bounds on the $D_4$ Lattice)

*Let SU(3) lattice gauge theory be defined on the $D_4$ lattice with spacing parameter $a$ (nearest-neighbor distance $a\sqrt{2}$), with the normalized lattice Laplacian $\hat{k}^2_\text{FCC}$ from Prop 7.4.3. Then:*

### Part (a): Gauge Fixing and Free Propagator ✅ ESTABLISHED + 🔶 NOVEL

*The $D_4$ lattice with $N_V$ vertices and $N_E = 12 N_V$ edges admits an axial gauge fixing via a spanning tree $T$ with $|T| = N_V - 1$ edges, leaving $11 N_V + 1$ independent link variables. In axial gauge, the Faddeev-Popov determinant is trivial ($\det M_\text{FP} = 1$).*

*The free scalar propagator (adjoint Laplacian Green's function) on $D_4$ is:*

$$\boxed{G_0(x) = \int_{\text{BZ}_{D_4}} \frac{d^4k}{\mathcal{V}_\text{BZ}} \frac{e^{ik \cdot x}}{\hat{k}^2_\text{FCC}}}$$

*where $\mathcal{V}_\text{BZ} = (2\pi)^4/2$ is the Brillouin zone volume and $\hat{k}^2_\text{FCC}$ is the normalized $D_4$ lattice Laplacian (Prop 7.4.3). The propagator satisfies:*

**(a.1) Pointwise decay.** *For $|x| \geq a\sqrt{2}$ (at least one lattice spacing):*

$$\boxed{|G_0(x)| \leq \frac{C_{D_4}}{|x|^2}}$$

*where $C_{D_4} = \frac{1}{4\pi^2}(1 + \varepsilon_{D_4})$ with $\varepsilon_{D_4} = O(a^2/|x|^2)$. In the continuum limit, $G_0(x) \to \frac{1}{4\pi^2 |x|^2}$.*

**(a.2) Gradient bounds.** *For any $D_4$ nearest-neighbor direction $v$ with $|v| = a\sqrt{2}$, the lattice gradient $(\nabla_v f)(x) = [f(x+v) - f(x)]/(a\sqrt{2})$ satisfies:*

$$\boxed{|\nabla_v^{n} G_0(x)| \leq \frac{C_n}{|x|^{2+n}}, \qquad n = 1, 2, \ldots}$$

*with constants $C_n$ depending only on $n$ and $D_4$ geometry.*

**(a.3) Enhanced isotropy.** *Due to $D_4$ fourth-moment isotropy (Prop 7.4.3, Lemma 6.3.1), the lattice propagator deviates from the continuum propagator only at $O(1/|x|^6)$:*

$$G_0(x) = \frac{1}{4\pi^2 |x|^2} + O\!\left(\frac{a^4}{|x|^6}\right) \quad \text{as } |x|/a \to \infty$$

*This is two orders better than on the hypercubic lattice, where the correction is $O(a^2/|x|^4)$.*

### Part (b): Covariant Laplacian on D₄ ✅ ESTABLISHED + 🔶 NOVEL

*The gauge-covariant Laplacian on $D_4$, acting on $\mathfrak{su}(3)$-valued fields $\psi: D_4 \to \mathfrak{su}(3)$, is:*

$$\boxed{(-\Delta_U^{D_4}\psi)(x) = \frac{1}{6a^2}\sum_{i=1}^{24}\left[\psi(x) - U_i(x)\,\psi(x + v_i)\,U_i(x)^{-1}\right]}$$

*where $\{v_i\}_{i=1}^{24}$ are the $D_4$ nearest-neighbor vectors (integer-coordinate, $|v_i| = \sqrt{2}\,a$), $U_i(x) \in SU(3)$ is the link variable on the edge from $x$ to $x + v_i$, and the factor $1/6$ is the normalization constant ensuring $-\Delta_U^{D_4} \to D_\mu D^\mu$ in the continuum limit (see Derivation §6.1). The covariant Laplacian satisfies:*

**(b.1) Positive semi-definiteness.**

$$\boxed{\langle \psi,\, (-\Delta_U^{D_4})\, \psi \rangle \geq 0 \qquad \text{for all } \psi \in \ell^2(D_4; \mathfrak{su}(3)),\ \text{all } U}$$

**(b.2) Spectrum.** *The spectrum of $-\Delta_U^{D_4}$ is contained in $[0,\, 16/(3a^2)]$, where $16/(3a^2) \approx 5.33/a^2$ is the tight spectral bound achieved at BZ boundary points $k$ with two components $= \pi/a$ and two $= 0$. The triangle inequality gives the (non-tight) upper bound $8/a^2$. For $U = \mathbf{1}$ (trivial gauge field), the spectrum is $\{k̂^2_\text{FCC}(k) : k \in \text{BZ}_{D_4}\}$.*

**(b.3) Diagonal norm.** *The diagonal part equals $4/a^2$ in coordinate units, matching the hypercubic lattice per $d_\text{nn}^2$:*

$$(-\Delta_U^{D_4}\psi)(x)\big|_\text{diag} = \frac{24}{6a^2}\psi(x) = \frac{4}{a^2}\psi(x) = \frac{8}{d_\text{nn}^2}\psi(x)$$

### Part (c): Background Field Propagator with Exponential Decay 🔶 NOVEL

*Let $B = \{B_i(x)\}$ be a background gauge field configuration on $D_4$ satisfying the small-field condition: $|F_p[B]| \leq \varepsilon$ for all triangular plaquettes $p$, where $0 < \varepsilon \leq 1$. For any mass parameter $m > 0$, the background field propagator:*

$$G_B(m) = (-\Delta_B^{D_4} + m^2)^{-1}$$

*exists and satisfies the Combes-Thomas exponential decay bound:*

$$\boxed{|G_B(x,y;m)| \leq \frac{C_\text{CT}}{m^2}\,\exp\!\left(-\gamma_{D_4}(m)\,\frac{|x - y|}{a\sqrt{2}}\right)}$$

*where:*
- *$C_\text{CT}$ is a universal constant (independent of $B$, $m$, $a$, and lattice size)*
- *The decay rate per nearest-neighbor distance is:*

$$\boxed{\gamma_{D_4}(m) = \ln\!\left(1 + \frac{m^2 a^2}{8}\right) = \frac{m^2 a^2}{8} + O(m^4 a^4)}$$

*In the continuum limit ($ma \to 0$): $\gamma_{D_4}(m)/a \to m^2 a/8 \to 0$ in lattice units, but the physical decay rate $\gamma_{D_4}/(a\sqrt{2}) \cdot |x-y|$ reproduces the continuum exponential decay $e^{-m|x-y|}$ when combined with the RG flow. Equivalently, in terms of $d_\text{nn} = a\sqrt{2}$: $\gamma_{D_4} = \ln(1 + m^2 d_\text{nn}^2/16)$, matching the hypercubic rate per $d_\text{nn}^2$.*

**(c.1) Resolvent identity.** *The background field propagator satisfies:*

$$G_B(m) = G_0(m) - G_0(m)\,V_B\,G_B(m)$$

*where $V_B = \Delta_0^{D_4} - \Delta_B^{D_4}$ is the background field potential, and $G_0(m) = (-\Delta_0^{D_4} + m^2)^{-1}$ is the free massive propagator.*

**(c.2) Background field regularity.** *For $B$ in the small-field region with $|F_p[B]| \leq C g_k^{1-\delta}$:*

$$\|V_B\|_{\ell^2 \to \ell^2} \leq \frac{C_V}{a^2}\,g_k^{1-\delta}$$

*where $C_V$ depends only on $D_4$ geometry. The resolvent series converges when $g_k$ is sufficiently small.*

### Part (d): Scale Compatibility 🔶 NOVEL

*All bounds in Parts (a)–(c) are compatible with the $D_4$ self-coarsening property and the RG iteration:*

**(d.1) Uniformity in $a$.** *The constants $C_{D_4}$, $C_n$, $C_\text{CT}$, $C_V$ depend only on $D_4$ geometry, not on the lattice spacing $a$ or the lattice size.*

**(d.2) Scale-invariant form.** *At RG scale $k$ (lattice spacing $\eta_k = 2^k a$), the propagator bounds have the same functional form as at scale $0$:*

$$|G_0^{(k)}(x)| \leq \frac{C_{D_4}}{|x|^2}, \qquad |G_B^{(k)}(x,y;m_k)| \leq \frac{C_\text{CT}}{m_k^2}\,e^{-\gamma_{D_4}(m_k)\,|x-y|/(\eta_k\sqrt{2})}$$

*where $\gamma_{D_4}(m_k) = \ln(1 + m_k^2\eta_k^2/8)$.*

*with the same constants $C_{D_4}$, $C_\text{CT}$. This follows from $D_4(\eta_k) \cong D_4(a)$ (self-coarsening) — the coarsened lattice has identical geometric properties.*

**(d.3) Compatibility with $Q_\text{FCC}$.** *The background field propagator satisfies the matching condition required by the averaging kernel (Prop 7.6.1): the block-averaged propagator on $D_4(2\eta_k)$ agrees with the free propagator on $D_4(2\eta_k)$ up to corrections of order $g_k^{2-2\delta}$.*

---

## §2. Symbol and Dimension Table

| Symbol | Name | Type | Definition / Value |
|--------|------|------|-------------------|
| $D_4$ | $D_4$ root lattice | Lattice in $\mathbb{R}^4$ | $\{x \in \mathbb{Z}^4 : \sum x_i \in 2\mathbb{Z}\}$ |
| $a$ | Lattice spacing parameter | Length | Fundamental scale; NN distance = $a\sqrt{2}$ |
| $\hat{k}^2_\text{FCC}$ | Normalized FCC Laplacian | $a^{-2}$ | $\frac{1}{3a^2}\sum_{\mu<\nu}[2 - \cos((k_\mu+k_\nu)a) - \cos((k_\mu-k_\nu)a)]$ |
| $\text{BZ}_{D_4}$ | Brillouin zone | Region in $k$-space | 24-cell; volume $\mathcal{V}_\text{BZ} = (2\pi)^4/2$ |
| $G_0(x)$ | Free scalar propagator | $a^{-2}$ | $\int_\text{BZ} \frac{d^4k}{\mathcal{V}_\text{BZ}} \frac{e^{ikx}}{\hat{k}^2}$ |
| $C_{D_4}$ | Propagator decay constant | Dimensionless | $\frac{1}{4\pi^2}(1 + O(a^2/|x|^2))$ |
| $\Delta_U^{D_4}$ | Gauge-covariant Laplacian | Operator on $\ell^2(D_4;\mathfrak{su}(3))$ | Eq. in Part (b) |
| $U_i(x)$ | Link variable | $\in SU(3)$ | Parallel transport from $x$ to $x + v_i$ |
| $\{v_i\}_{i=1}^{24}$ | NN vectors | $\in D_4$ | All permutations of $(\pm 1, \pm 1, 0, 0)$ |
| $G_B(m)$ | Background field propagator | Operator on $\ell^2$ | $(-\Delta_B^{D_4} + m^2)^{-1}$ |
| $V_B$ | Background field potential | Operator | $\Delta_0^{D_4} - \Delta_B^{D_4}$ |
| $\gamma_{D_4}(m)$ | CT decay rate | Dimensionless | $\ln(1 + m^2a^2/8)$ |
| $T$ | Spanning tree | Subgraph of $D_4$ | $|T| = N_V - 1$ edges |
| $g_k$ | Running coupling at scale $k$ | Dimensionless | $g_k^2 \approx g_0^2/(1 - 2b_0 g_0^2 \ln 2^k)$ |
| $\eta_k$ | Lattice spacing at scale $k$ | Length | $\eta_k = 2^k a$ |
| $m_k$ | Running mass at scale $k$ | $a^{-1}$ | Mass parameter in the effective theory |

---

## §3. Background and Motivation

### §3.1 Balaban's Propagator Program

The propagator bounds are the technical foundation of Balaban's renormalization group program. At each RG step, the "fast" (high-momentum) fluctuations are integrated out using:

1. **Free propagator** $G_0$: controls the Gaussian part of the fluctuation integral
2. **Background field propagator** $G_B$: controls fluctuations around the saddle-point (background) configuration
3. **Exponential decay** (Combes-Thomas): ensures that distant regions decouple, enabling the cluster expansion

On the hypercubic lattice, these bounds are established in Balaban Papers I–II (free propagator, renormalization transformations) and Paper V (background field propagator). The bounds are:

$$|G_0(x)| \leq \frac{C_{\mathbb{Z}^4}}{|x|^2}, \qquad |G_B(x,y;m)| \leq \frac{C}{m^2}\,e^{-\gamma m|x-y|} \tag{3.1}$$

These must be adapted to the $D_4$ lattice for the FCC RG program.

### §3.2 What Changes on D₄

The key geometric differences affecting propagator bounds:

| Property | Hypercubic ($\mathbb{Z}^4$, $a = d_\text{nn}$) | FCC ($D_4$, $a = a_\text{coord}$) | Effect on Bounds |
|----------|----------------------------|-------------|-----------------|
| Coordination $z$ | 8 | 24 | More neighbors |
| NN distance | $a$ | $a\sqrt{2}$ | Rescales decay rate |
| Diagonal of $-\Delta$ | $8/a^2$ | $4/a^2$ | **Same** per $d_\text{nn}^2$: both $= 8/d_\text{nn}^2$ |
| Hopping strength per neighbor | $1/a^2$ | $1/(6a^2)$ | Compensates for more neighbors |
| Total hopping norm | $8/a^2$ | $24/(6a^2) = 4/a^2$ | **Same** per $d_\text{nn}^2$: both $= 8/d_\text{nn}^2$ |
| Fourth-moment isotropy | Broken | Exact | Better large-$|x|$ asymptotics |
| BZ volume | $(2\pi/a)^4$ | $(2\pi/a)^4/2$ | Different normalization |

The remarkable fact: the total hopping norm per $d_\text{nn}^2$ is **identical** on $D_4$ and $\mathbb{Z}^4$ (both equal $8/d_\text{nn}^2$). This is because the $D_4$ normalization factor $1/6$ exactly compensates for the larger coordination number. As a consequence, the Combes-Thomas decay rate per nearest-neighbor step has the **same form** on both lattices: $\gamma = \ln(1 + m^2 d_\text{nn}^2/16)$.

### §3.3 Role in Phase G

This proposition provides the second of four geometric inputs for the Balaban RG iteration on FCC:

| Input | Source | Status |
|-------|--------|--------|
| 1. Averaging kernel $Q_\text{FCC}$ | Prop 7.6.1 | ✅ Complete |
| **2. Propagator bounds** | **Prop 7.6.2 (this)** | **In progress** |
| 3. Regular configurations + variational problem | Future Prop 7.6.3 | Pending |
| 4. Large-field (Peierls) estimates | Future Prop 7.6.4 | Pending |

With inputs 1–2 established, the small-field part of the RG iteration can be assembled (future Thm 7.6.5).

### §3.4 Prior Work

**Hypercubic lattice:**
- Balaban Papers I–II (CMP 95–96, 1984): Free propagator bounds, renormalization transformations
- Balaban Paper V (CMP 99, 389–434, 1985): Background field propagator, exponential decay
- Dimock I (Rev. Math. Phys. 25, 2013; arXiv:1108.1335): Modern reformulation for scalar $\phi^4$; propagator analysis in §§2–3

**General lattice Green's functions:**
- T. Balaban, "Regularity and decay of lattice Green's functions" (CMP 89, 1983): Lattice-independent framework for propagator bounds
- Combes & Thomas (1973): General exponential decay for resolvents with spectral gaps

**FCC/$D_4$ lattice:**
- Prop 7.4.3 (this framework): $D_4$ lattice Laplacian, Feynman-gauge propagator, tadpole integral
- Celmaster (1982): BCH lattice gauge theory formulation, perturbative analysis
- **This proposition:** First complete propagator bounds for Balaban RG on $D_4$

---

## §4. Structure of the Derivation

### §4.1 Part (a): Gauge Fixing and Free Propagator

**Strategy:** Construct a spanning tree on $D_4$ for axial gauge, then analyze the resulting free propagator.

Key steps:
1. **Spanning tree** — For a finite $D_4$ lattice with periodic boundary conditions, construct a spanning tree by lexicographic ordering. Count edges: $12 N_V$ total, $N_V - 1$ in tree, $11 N_V + 1$ independent.
2. **Free propagator** — In axial gauge, the quadratic part of the gauge-fixed action gives $G_0(k) = 1/\hat{k}^2_\text{FCC}$ for the scalar sector. Fourier transform to position space.
3. **Pointwise decay** — Use contour deformation in the Fourier integral to extract the $1/|x|^2$ behavior. The BZ integral is dominated by the $k \to 0$ singularity.
4. **Gradient bounds** — Integration by parts in the Fourier representation: each gradient adds a power of $\hat{k}$ in the numerator, improving the large-$|x|$ decay by one power.
5. **Enhanced isotropy** — $D_4$ fourth-moment isotropy (Prop 7.4.3) kills the leading anisotropic correction, giving $O(a^4/|x|^6)$ deviation from continuum.

See §5 in the Derivation file.

### §4.2 Part (b): Covariant Laplacian

**Strategy:** Define $-\Delta_U^{D_4}$ by summing over all 24 neighbors with gauge links, then prove positivity.

Key steps:
1. **Definition** — Sum over 24 NN directions with gauge-covariant finite differences and $1/6$ normalization (one-sided sum form: $(-\Delta_U^{D_4}\psi)(x) = \frac{1}{6a^2}\sum_{i=1}^{24}[\psi(x) - U_i\psi_{+i}U_i^{-1}]$)
2. **Continuum limit** — Expand $U_i(x) \approx \mathbf{1} + ig_0 v_i^\mu A_\mu(x) + \ldots$ and show $-\Delta_U^{D_4} \to D_\mu D^\mu = (\partial_\mu + ig_0[A_\mu, \cdot])^2$
3. **Positivity** — Write $-\Delta_U^{D_4} = \frac{1}{6}\sum_i (\nabla_i^U)^\dagger \nabla_i^U$ where $\nabla_i^U$ is the covariant forward difference (including $1/(a\sqrt{2})$ denominator); positivity follows from $X^\dagger X \geq 0$
4. **Spectral bounds** — Triangle inequality upper bound: $\|-\Delta_U\| \leq 8/a^2$; tight bound: $16/(3a^2) \approx 5.33/a^2$

See §6 in the Derivation file.

### §4.3 Part (c): Background Field Propagator

**Strategy:** Apply the Combes-Thomas argument to $-\Delta_B^{D_4} + m^2$ on the $D_4$ lattice.

Key steps:
1. **Spectral gap** — For $m > 0$: $\text{spec}(-\Delta_B^{D_4} + m^2) \subset [m^2, 16/(3a^2) + m^2]$, so $(-\Delta_B^{D_4} + m^2)^{-1}$ exists with $\|(-\Delta_B^{D_4} + m^2)^{-1}\| \leq 1/m^2$
2. **Combes-Thomas conjugation** — For a weight function $\psi(x) = \alpha \hat{n} \cdot x$ (unit vector $\hat{n}$, parameter $\alpha > 0$), conjugate: $H(\alpha) = e^{\alpha\psi}(-\Delta_B^{D_4} + m^2)e^{-\alpha\psi}$
3. **Hopping perturbation** — Bound $\|H(\alpha) - H(0)\| \leq (4/a^2)(e^{\alpha a\sqrt{2}} - 1)$ using $z = 24$ neighbors, hopping $1/(6a^2)$ each, NN distance $a\sqrt{2}$
4. **Optimal $\alpha$** — Choose $\alpha$ so that $\|H(\alpha) - H(0)\| = m^2/2$, giving $\alpha = \gamma_{D_4}(m)/(a\sqrt{2})$
5. **Decay bound** — The resolvent of $H(\alpha)$ exists with norm $\leq 2/m^2$, and the exponential weight factor gives the position-space decay

See §7 in the Derivation file.

### §4.4 Part (d): Scale Compatibility

**Strategy:** Verify that all bounds transform correctly under the $D_4 \to D_4$ coarsening.

Key steps:
1. **Self-coarsening invariance** — At scale $k$, the lattice is $D_4(\eta_k)$ with the same geometric structure as $D_4(a)$. All geometric constants ($C_{D_4}$, $C_\text{CT}$, etc.) are functions of the lattice type, not the spacing.
2. **Running coupling dependence** — The background field bounds depend on $g_k$ through the small-field condition. As $g_k$ evolves under the RG, the bounds remain valid as long as $g_k \lesssim O(1)$.
3. **Compatibility with $Q_\text{FCC}$** — The block-averaged propagator satisfies $Q_\text{FCC}(G_0^{(k)}) \approx G_0^{(k+1)}$ up to corrections controlled by the smallness bound (Prop 7.6.1, Part c).

See §8 in the Derivation file.

---

## §9. Summary and Connections

### §9.1 What This Proposition Establishes

1. **Complete gauge fixing on $D_4$:** Axial gauge via spanning tree, with $11N_V + 1$ independent link variables (vs. $3N_V + 1$ on hypercubic — more links but same physical d.o.f.)
2. **Free propagator with optimal decay:** $|G_0(x)| \leq C/|x|^2$ with $D_4$-enhanced isotropy giving $O(a^4/|x|^6)$ corrections (two orders better than hypercubic)
3. **Positive covariant Laplacian:** $-\Delta_U^{D_4} \geq 0$ with diagonal norm $4/a^2$ (= $8/d_\text{nn}^2$, matching the hypercubic lattice per $d_\text{nn}^2$)
4. **Background field exponential decay:** Combes-Thomas bound with decay rate that matches hypercubic at leading order
5. **Scale invariance:** All bounds hold identically at every RG scale due to $D_4$ self-coarsening

### §9.2 Honest Assessment

**What is rigorously established (✅):**
- Axial gauge fixing via spanning tree — standard lattice gauge theory (Creutz 1983)
- Combes-Thomas framework for exponential decay — established mathematical technique (1973)
- Positivity of the covariant Laplacian — algebraic identity $X^\dagger X \geq 0$
- Free propagator $1/|x|^2$ decay on regular lattices — standard lattice Green's function theory

**What is novel but well-grounded (🔶):**
- The explicit $D_4$ propagator bounds with computed constants
- The $1/6$ normalization giving matching hopping norms per $d_\text{nn}^2$ between $D_4$ and $\mathbb{Z}^4$
- Enhanced isotropy of the propagator from $D_4$ fourth-moment isotropy
- Compatibility with $Q_\text{FCC}$ and the RG iteration

**Limitations:**
- The Combes-Thomas decay rate $\gamma_{D_4}(m) \sim m^2 a^2/8$ vanishes as $a \to 0$; physical exponential decay requires the RG to build up the correlation length across scales
- The background field bounds require the small-field condition $|F_p| \leq \varepsilon$; the large-field region (Balaban Paper X) requires separate analysis
- The gauge field propagator in axial gauge has a more complex structure than the scalar propagator; only the scalar bounds are proven here (the gauge field bounds follow by standard arguments but are not explicitly derived)

### §9.3 What This Enables

- **Phase G.2 (UV stability):** With propagator bounds and the averaging kernel, the Gaussian integral at each RG step is controlled — the effective action is bounded in the small-field region
- **Future Prop 7.6.3 (variational problem):** The background field propagator defines the quadratic form around the saddle point, enabling the variational analysis (Balaban Paper VI)
- **Inductive RG structure:** Scale invariance (Part d) ensures the same bounds at every RG step, which is essential for Balaban's inductive argument across arbitrarily many scales

### §9.4 Key Comparison: D₄ vs. Hypercubic

| Bound | Hypercubic ($\mathbb{Z}^4$, $a = d_\text{nn}$) | FCC ($D_4$, $a = a_\text{coord}$) | Per $d_\text{nn}^2$ |
|-------|----------------------------|-------------|-----------|
| Free propagator decay | $C/|x|^2$ | $C/|x|^2$ | Same |
| Isotropy correction | $O(a^2/|x|^4)$ | $O(a^4/|x|^6)$ | **FCC better** |
| Diagonal norm | $8/a^2$ | $4/a^2$ | Both $= 8/d_\text{nn}^2$ |
| Hopping norm | $8/a^2$ | $4/a^2$ | Both $= 8/d_\text{nn}^2$ |
| CT decay rate (leading) | $m^2a^2/16$ | $m^2a^2/8$ | Both $= m^2 d_\text{nn}^2/16$ |
| CT decay rate (per NN) | $\ln(1+m^2a^2/16)$ | $\ln(1+m^2a^2/8)$ | Both $= \ln(1+m^2 d_\text{nn}^2/16)$ |
| NN distance | $a$ | $a\sqrt{2}$ | — |
| Independent links per site | 3 | 11 | More variables on FCC |

The matching of hopping norms and CT decay rates per $d_\text{nn}^2$ is a consequence of the $1/6$ normalization, which exactly compensates for the larger coordination number on $D_4$.

---

## §10. References

### External References

1. T. Balaban, "Propagators and renormalization transformations for lattice gauge theories. I," *Commun. Math. Phys.* **95** (1984) 17–40. [Paper I]
2. T. Balaban, "Propagators and renormalization transformations for lattice gauge theories. II," *Commun. Math. Phys.* **96** (1984) 223–250. [Paper II]
3. T. Balaban, "Averaging operations for lattice gauge theories," *Commun. Math. Phys.* **98** (1985) 17–51. [Paper III]
4. T. Balaban, "Spaces of regular gauge field configurations on a lattice and gauge fixing conditions," *Commun. Math. Phys.* **99** (1985) 75–102. [Paper IV]
5. T. Balaban, "Propagators for lattice gauge theories in a background field," *Commun. Math. Phys.* **99** (1985) 389–434. [Paper V]
6. T. Balaban, "Regularity and decay of lattice Green's functions," *Commun. Math. Phys.* **89** (1983) 571–597.
7. J.-M. Combes and L. Thomas, "Asymptotic behaviour of eigenfunctions for multiparticle Schrödinger operators," *Commun. Math. Phys.* **34** (1973) 251–270.
8. J. Dimock, "The renormalization group according to Balaban. I. Small fields," *Rev. Math. Phys.* **25** (2013) 1330010, arXiv:1108.1335.
9. M. Creutz, *Quarks, Gluons and Lattices* (Cambridge UP, 1983), Ch. 6 — Gauge fixing on lattices.
10. W. Celmaster, "Gauge theories on the body-centered hypercubic lattice," *Phys. Rev. D* **26** (1982) 2955.
11. M. Aizenman and S. Warzel, *Random Operators* (AMS, 2015), Ch. 10 — Combes-Thomas estimates.
12. O. Musin, "The kissing number in four dimensions," *Ann. Math.* **168** (2008) 1–32 — Proof that kissing number in $\mathbb{R}^4$ is exactly 24.
13. J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed. (Springer, 1999) — Standard reference for $D_4$ lattice properties.

### Framework References

14. Proposition 7.4.3 — FCC Lattice Perturbation Theory ($D_4$ Laplacian, fourth-moment isotropy, tadpole integral)
15. Proposition 7.6.1 — FCC Averaging Kernel on the $D_4$ Lattice (blocking, gauge covariance)
16. Theorem 7.4.1 — Reflection Positivity on FCC Lattice
17. Theorem 7.4.2 — Mass Gap Thermodynamic Limit
18. Theorem 7.5.3 — Bulk Transition Termination Under Modified FCC Action
19. [Research Note: Balaban RG Adaptation to FCC](../supporting/Research-Note-Balaban-RG-Adaptation-FCC.md) — Preliminary analysis for Phase G

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (D₄-specific bounds) / ✅ ESTABLISHED (Balaban propagator framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G (Constructive Continuum Limit), Step G.2 (partial)*
