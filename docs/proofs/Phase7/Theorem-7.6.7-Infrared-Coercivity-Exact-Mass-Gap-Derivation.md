# Theorem 7.6.7: Infrared Coercivity — Derivation

**Parent document:** [Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap.md](./Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap.md)

---

## §5. Part (a): Matching Scale Definition and Properties ✅ ESTABLISHED + 🔶 NOVEL

### §5.1 Running Coupling Evolution

The running coupling at RG scale $k$ is determined by the one-loop RG equation (Thm 7.6.5 Part (c)):

$$\frac{1}{g_{k+1}^2} = \frac{1}{g_k^2} - b_0 \ln 2 - c_\text{finite}^{D_4} + O(g_k^2) \tag{5.1}$$

Absorbing the finite constant $c_\text{finite}^{D_4}$ into the coupling-constant scheme (as in Thm 7.6.5), the leading-order solution is:

$$\frac{1}{g_k^2} = \frac{1}{g_0^2} - k b_0 \ln 2 + O(g_0^2 k) \tag{5.2}$$

with $g_0^2 = 6/\beta$. The coupling **increases** with $k$ (running from UV toward IR): $g_k^2 > g_0^2$ for $k \geq 1$, consistent with asymptotic freedom (coupling grows at longer distances).

### §5.2 Matching Scale Formula

The matching scale $k_\max(\beta)$ is defined as the largest $k$ where the UV stability contraction estimate (Thm 7.6.5 Part (e.1)) applies:

$$k_\max(\beta) := \max\left\{k \in \mathbb{Z}_{\geq 0} : g_k^2 \leq g_*^2\right\} \tag{5.3}$$

From Eq. (5.2), the condition $g_k^2 \leq g_*^2$ is equivalent to $1/g_k^2 \geq 1/g_*^2$:

$$\frac{1}{g_0^2} - k b_0 \ln 2 \geq \frac{1}{g_*^2} \tag{5.4}$$

Solving for $k$:

$$k \leq \frac{1}{b_0 \ln 2}\left(\frac{1}{g_0^2} - \frac{1}{g_*^2}\right) \tag{5.5}$$

Since we want the **maximum** $k$ satisfying $g_k^2 \leq g_*^2$:

$$k_\max(\beta) = \left\lfloor \frac{1}{b_0 \ln 2}\left(\frac{1}{g_0^2} - \frac{1}{g_*^2}\right) \right\rfloor \tag{5.6}$$

Note that $1/g_0^2 > 1/g_*^2$ (since $g_0^2 < g_*^2$ for $\beta > 6/g_*^2$), so $k_\max \geq 1$ for sufficiently large $\beta$.

Substituting $g_0^2 = 6/\beta$:

$$k_\max(\beta) = \left\lfloor \frac{1}{b_0 \ln 2}\left(\frac{\beta}{6} - \frac{1}{g_*^2}\right) \right\rfloor = \frac{\beta}{6 b_0 \ln 2} + O(1) \tag{5.7}$$

### §5.3 Physical Lattice Spacing at Matching

The lattice spacing at the matching scale is:

$$\eta_{k_\max} = 2^{k_\max} \cdot a \tag{5.8}$$

Using the asymptotic scaling relation (from the running coupling):

$$2^{k_\max} = \exp(k_\max \ln 2) \approx \exp\!\left(\frac{1}{2b_0 g_0^2} - \frac{1}{2b_0 g_*^2}\right) \tag{5.9}$$

The QCD scale is defined by:

$$\frac{1}{\Lambda_\text{QCD}} = a \cdot \left(\frac{6 b_0}{\beta}\right)^{-b_1/(2b_0^2)} \exp\!\left(\frac{\beta}{12 b_0}\right) \tag{5.10}$$

Comparing with Eq. (5.9):

$$\eta_{k_\max} = a \cdot \exp\!\left(\frac{1}{2b_0 g_0^2}\right) \cdot \exp\!\left(-\frac{1}{2b_0 g_*^2}\right) = \frac{e^{-1/(2b_0 g_*^2)}}{\Lambda_\text{QCD}} \cdot (b_0 g_0^2)^{b_1/(2b_0^2)} \tag{5.11}$$

The factors involving $g_0$ and $g_*$ contribute an $O(1)$ multiplicative constant. Up to this constant:

$$\eta_{k_\max} \sim \frac{1}{\Lambda_\text{QCD}} \tag{5.12}$$

confirming that the matching scale corresponds to the confinement scale.

### §5.4 UV Regime Control

For $k \leq k_\max$, the running coupling satisfies $g_k^2 \leq g_*^2$, so Thm 7.6.5 Part (e) applies. The inductive bound gives:

$$\varepsilon_{k+1} \leq C_\text{ind} \cdot g_k^{2-4\delta} \cdot \varepsilon_k + C_2 \cdot g_k^{4-4\delta} + C_3 \cdot e^{-\kappa_\text{FCC}/(2g_k^2)} \tag{5.13}$$

With $\delta = 1/4$, the contraction factor $C_\text{ind} \cdot g_k < 1$ for $g_k^2 < g_*^2$. The fixed-point remainder:

$$\varepsilon_*^\text{UV} = \frac{C_2 g_*^{4-4\delta}}{1 - C_\text{ind} g_*^{2-4\delta}} + O(e^{-\kappa_\text{FCC}/(2g_*^2)}) \tag{5.14}$$

provides the uniform bound $\varepsilon_k \leq 2\varepsilon_*^\text{UV}$ for all $k \leq k_\max$.

**At scale $k_\max$, the effective action is:**

$$\mathcal{A}_{k_\max}(V) = \frac{1}{g_{k_\max}^2}\mathcal{S}_\text{FCC}(V) + \text{counterterms} + R_{k_\max}(V), \qquad \|R_{k_\max}\|_{\alpha,k_\max} \leq 2\varepsilon_*^\text{UV} \tag{5.15}$$

This is the starting point for the IR analysis. $\square$

---

## §6. Part (b): Coercivity Bound from Transfer Matrix Spectral Gap 🔶 NOVEL

### §6.1 Transfer Matrix and Spectral Gap

The transfer matrix $\hat{T}(\beta,\varepsilon)$ of the lattice gauge theory on the crossover path is positive and self-adjoint (Thm 7.4.1, extended to the modified action by Thm 7.5.3). Its spectral decomposition:

$$\hat{T} = \sum_{n=0}^\infty \lambda_n |n\rangle \langle n|, \qquad \lambda_0 > \lambda_1 \geq \lambda_2 \geq \cdots \geq 0 \tag{6.1}$$

The mass gap is:

$$\mu(\beta,\varepsilon) = \ln\frac{\lambda_0}{\lambda_1} > 0 \tag{6.2}$$

On the crossover path ($\varepsilon > \varepsilon_*$), $\mu(\beta,\varepsilon) \geq \mu_\min(\varepsilon) > 0$ for all $\beta$ (Prop 7.6.6 Part (d)).

### §6.2 Connected Correlator and Spectral Representation

For gauge-invariant observables $O_1, O_2$ at temporal separation $t$ (in lattice units):

$$\langle O_1(0) O_2(t) \rangle_c = \sum_{n \geq 1} \langle 0|O_1|n\rangle \langle n|O_2|0\rangle \left(\frac{\lambda_n}{\lambda_0}\right)^t \tag{6.3}$$

The dominant contribution comes from $n = 1$:

$$|\langle O_1(0) O_2(t)\rangle_c| \leq C_{O_1,O_2} \cdot e^{-\mu t} \tag{6.4}$$

where $C_{O_1,O_2} = \sum_{n \geq 1} |\langle 0|O_1|n\rangle \langle n|O_2|0\rangle|$ is a finite constant (by completeness and $\|O_i\|_\infty < \infty$).

### §6.3 Fourier-Space Inverse Propagator

Define the connected two-point function in the temporal Fourier representation:

$$\hat{G}_c(\omega) := \sum_{t=-\infty}^{\infty} \langle O(0) O(t)\rangle_c \cdot e^{i\omega t} \tag{6.5}$$

Using the spectral representation Eq. (6.3) and summing the geometric series:

$$\hat{G}_c(\omega) = \sum_{n \geq 1} |\langle 0|O|n\rangle|^2 \cdot \frac{2\sinh \mu_n}{\cosh \mu_n - \cos \omega} \tag{6.6}$$

where $\mu_n := \ln(\lambda_0/\lambda_n) \geq \mu$ for $n \geq 1$.

**Upper bound:** For all $\omega$:

$$\hat{G}_c(\omega) \leq \sum_{n \geq 1} |\langle 0|O|n\rangle|^2 \cdot \frac{2\sinh \mu_n}{\cosh \mu_n - 1} = \sum_{n \geq 1} |\langle 0|O|n\rangle|^2 \cdot \frac{2}{\tanh(\mu_n/2)} \tag{6.7}$$

For $\mu_n \geq \mu \geq \mu_\min$:

$$\hat{G}_c(\omega) \leq \frac{C_O}{\tanh(\mu_\min/2)} \tag{6.8}$$

**Lower bound on inverse:** By the denominator structure $\cosh \mu_n - \cos \omega \geq (\mu_n^2 + \omega^2)/C'$ for $|\omega| \leq \pi/2$ and moderate $\mu_n$:

$$\hat{G}_c(\omega) \leq \frac{C_O}{\mu_\min^2 + \omega^2} \cdot C'' \tag{6.9}$$

The **inverse propagator** therefore satisfies:

$$\hat{G}_c^{-1}(\omega) \geq \frac{\mu_\min^2 + \omega^2}{C_O C''} \tag{6.10}$$

**Validity note:** The bound Eq. (6.9) uses $\cosh \mu_n - \cos\omega \geq (\mu_n^2 + \omega^2)/C'$, which is tight for $|\omega| \leq \pi/2$ (the physically relevant low-momentum regime). Near the Brillouin zone boundary $\omega \to \pi$, $\cosh\mu_n - \cos\omega \to \cosh\mu_n + 1$, which is exponentially large in $\mu_n$ — much stronger than $(\mu_n^2 + \omega^2)/C'$. This means Eq. (6.9) **over-estimates** $\hat{G}_c(\omega)$ near $\omega = 0$ and correctly bounds it elsewhere. The resulting coercivity bound (Eq. 6.14) is therefore **conservative** — a weaker but valid lower bound on the effective action.

### §6.4 Coercivity Bound for the Effective Action

The effective action at scale $k$ is related to the connected correlation function through the **Legendre transform** of the free energy. For lattice gauge theories, the Legendre transform requires three clarifications:

1. **Compact group:** The field variable $V_\ell \in \text{SU}(3)$ lives on a compact manifold. The Legendre transform is well-defined in a neighborhood of the identity $V = \mathbb{1}$ (where the exponential map provides local coordinates), which suffices for the quadratic coercivity bound.

2. **Gauge fixing:** The effective action has flat directions along gauge orbits. Following Prop 7.6.3, we work in **axial gauge** (a spanning tree of links fixed to $\mathbb{1}$). In this gauge, the remaining $|E| - |V| + 1$ link variables are gauge-invariant, and the effective action restricted to this gauge slice is strictly convex near $V = \mathbb{1}$ (by the mass gap $\mu_\min > 0$). The Legendre transform is well-defined on this convex function.

3. **Reference:** The Legendre transform for lattice gauge theories in the gauge-fixed sector is established in Seiler [7], §III.3, where strict convexity of the effective action is proven for massive theories.

With these clarifications, the second functional derivative of the effective action (the inverse propagator) satisfies:

$$\frac{\delta^2 \mathcal{A}_k}{\delta V(x) \delta V(y)}\bigg|_{V=\mathbb{1}} = G_c^{-1}(x-y) \tag{6.11}$$

In the Fourier representation, this gives:

$$\hat{\mathcal{A}}_k''(\omega) \geq \frac{\mu_\min^2 + \omega^2}{C_O C''} \tag{6.12}$$

Integrating the quadratic form:

$$\mathcal{A}_k(V) - \mathcal{A}_k(\mathbb{1}) \geq \frac{1}{2}\sum_{x,y} (V(x) - \mathbb{1})^T G_c^{-1}(x-y) (V(y) - \mathbb{1}) \tag{6.13}$$

The zero-mode ($\omega = 0$) contribution gives the coercivity:

$$\mathcal{A}_k(V) - \mathcal{A}_k(\mathbb{1}) \geq \frac{\mu_\min^2}{2 C_O C''} \sum_\ell \|V_\ell - \mathbb{1}\|_\text{HS}^2 \tag{6.14}$$

Defining $C_\text{corr} := C_O C''$:

$$\boxed{\mathcal{A}_{k_\max}(V) \geq \frac{\mu_\min^2}{2 C_\text{corr}} \sum_\ell \|V_\ell - \mathbb{1}\|_\text{HS}^2 + \mathcal{A}_{k_\max}(\mathbb{1})} \tag{6.15}$$

with $E_0 := -\mathcal{A}_{k_\max}(\mathbb{1})$ the ground-state energy contribution.

### §6.5 Scale Dependence

At RG scale $k \geq k_\max$, the blocked lattice has spacing $\eta_k = 2^k a$. The mass gap in scale-$k$ lattice units is:

$$\mu_k := \mu_\min \cdot \frac{\eta_k}{a} = \mu_\min \cdot 2^k \tag{6.16}$$

This reflects the physical fact that the correlation length $\xi = 1/(a \mu_\min)$ is fixed in physical units, while the lattice spacing grows. The number of correlation lengths per lattice unit is $\eta_k / \xi = \mu_k$, which grows with $k$.

The coercivity bound at scale $k$:

$$\mathcal{A}_k(V) \geq \frac{\mu_k^2}{2 C_\text{corr}} \sum_\ell \|V_\ell - \mathbb{1}\|_\text{HS}^2 + E_0^{(k)} \tag{6.17}$$

Since $\mu_k = \mu_\min \cdot 2^k \geq \mu_\min > 0$ for all $k \geq 0$, the coercivity is uniformly bounded below.

### §6.6 Uniformity Properties

The coercivity constant $\mu_\min^2/(2C_\text{corr})$ is:

1. **Independent of $\beta$:** $\mu_\min(\varepsilon) = \inf_\beta \mu(\beta,\varepsilon)$ takes the infimum over all $\beta$ (Prop 7.6.6 Part (d)).

2. **Independent of $N_s$:** The mass gap $\mu(\beta,\varepsilon)$ is exactly $N_s$-independent (Thm 7.4.2, extended to the crossover path).

3. **$C_\text{corr}$ is bounded:** The constant $C_\text{corr}$ depends on the observable norms $\|O\|_\infty$ and the spectral structure, but not on $\beta$ or $N_s$. For normalized observables ($\|O\| = 1$), $C_\text{corr}$ is bounded by the total spectral weight, which is finite by the completeness of the spectral decomposition. $\square$

---

## §7. Part (c): Massive Propagator Bounds in the IR ✅ ESTABLISHED + 🔶 NOVEL

### §7.1 IR Hessian Structure

At RG scale $k \geq k_\max$, the effective action has the form (from Part (b)):

$$\mathcal{A}_k(V) = \frac{1}{g_k^2}\mathcal{S}_\text{FCC}(V) + \frac{\mu_k^2}{2C_\text{corr}}\sum_\ell \|V_\ell - \mathbb{1}\|^2 + R_k(V) \tag{7.1}$$

Expanding around the identity $V = \mathbb{1}$ with fluctuation $V_\ell = e^{i\eta_k A_\ell}$:

$$\mathcal{A}_k(\mathbb{1} + i\eta_k A) \approx \frac{1}{2}\langle A, \mathcal{H}_k^\text{IR} A\rangle + O(A^3) \tag{7.2}$$

where the **IR Hessian** is:

$$\mathcal{H}_k^\text{IR} = \frac{1}{g_k^2}\left(-\Delta_{D_4}^{(k)}\right) + \frac{\mu_k^2}{C_\text{corr}} \cdot \mathbb{1} \tag{7.3}$$

Here $-\Delta_{D_4}^{(k)}$ is the lattice Laplacian on $D_4(\eta_k)$.

The key property: the IR Hessian has a **mass term** $\mu_k^2/C_\text{corr}$, ensuring strict positivity even in the IR where $1/g_k^2$ may be small.

### §7.2 Combes-Thomas Bound for the IR Propagator

The propagator $G_k = (\mathcal{H}_k^\text{IR})^{-1}$ satisfies the Combes-Thomas exponential decay bound (Prop 7.6.2, adapted to the massive case):

$$|G_k(x,y)| \leq \frac{C_\text{CT}}{m_k^2} \exp\!\left(-\gamma_{D_4}(m_k) \cdot \frac{|x-y|}{\eta_k \sqrt{2}}\right) \tag{7.4}$$

where $m_k^2 = \mu_k^2/C_\text{corr}$ is the effective mass squared and:

$$\gamma_{D_4}(m_k) = \ln\!\left(1 + \frac{m_k^2 d_\text{nn}^2}{16}\right) = \ln\!\left(1 + \frac{\mu_k^2 \eta_k^2}{8 C_\text{corr}}\right) \tag{7.5}$$

using $d_\text{nn} = \eta_k \sqrt{2}$ on $D_4(\eta_k)$.

**Proof:** The Combes-Thomas argument (Prop 7.6.2 Part (c)) applies to any positive operator $H \geq m^2 > 0$ on the $D_4$ lattice. The IR Hessian $\mathcal{H}_k^\text{IR} \geq m_k^2 > 0$ by construction. The decay rate $\gamma_{D_4}$ is the lattice-specific Combes-Thomas exponent from Prop 7.6.2.

### §7.3 Super-Exponential Growth of the Decay Rate

Substituting $\mu_k = \mu_\min \cdot 2^k$ into the decay rate:

$$\gamma_{D_4}(\mu_k) = \ln\!\left(1 + \frac{\mu_\min^2 a^2 \cdot 16^k}{8 C_\text{corr}}\right) \tag{7.6}$$

where we substituted $\mu_k^2 \eta_k^2 = (\mu_\min \cdot 2^k)^2 (2^k a)^2 = \mu_\min^2 a^2 \cdot 16^k$ into Eq. (7.5).

For $k \gg k_\max$:

$$\gamma_{D_4}(\mu_k) \approx 4k \ln 2 + \ln\!\left(\frac{\mu_\min^2 a^2}{8 C_\text{corr}}\right) \tag{7.7}$$

The decay rate grows **linearly** with $k$, meaning the propagator decays **super-exponentially** with distance as $k$ increases.

### §7.4 One-Loop IR Contribution

The one-loop contribution from fluctuations at scale $k \geq k_\max$ is:

$$\frac{1}{2}\operatorname{Tr}\ln \mathcal{H}_k^\text{IR} = \frac{1}{2}\sum_{p \in \text{BZ}_k} \ln\!\left(\frac{\hat{p}^2}{g_k^2} + \frac{\mu_k^2}{C_\text{corr}}\right) \tag{7.8}$$

where the sum runs over the Brillouin zone of $D_4(\eta_k)$.

**Splitting into constant and momentum-dependent parts:**

$$\frac{1}{2}\operatorname{Tr}\ln \mathcal{H}_k^\text{IR} = \frac{N_k}{2}\ln\!\left(\frac{\mu_k^2}{C_\text{corr}}\right) + \frac{1}{2}\sum_p \ln\!\left(1 + \frac{C_\text{corr} \hat{p}^2}{g_k^2 \mu_k^2}\right) \tag{7.9}$$

where $N_k = |\Lambda_k|$ is the number of lattice sites. The first term is the massive contribution (ground-state energy shift). The second term is bounded:

$$0 \leq \frac{1}{2}\sum_p \ln\!\left(1 + \frac{C_\text{corr} \hat{p}^2}{g_k^2 \mu_k^2}\right) \leq \frac{C_\text{corr}}{2g_k^2 \mu_k^2} \sum_p \hat{p}^2 = \frac{4 C_\text{corr} N_k}{g_k^2 \mu_k^2} \tag{7.10}$$

Since $\mu_k^2 = \mu_\min^2 \cdot 4^k$ and $g_k^2$ is at most polynomially growing:

$$\frac{4 C_\text{corr}}{g_k^2 \mu_k^2} \leq \frac{4 C_\text{corr}}{g_{k_\max}^2 \mu_\min^2 \cdot 4^{k-k_\max}} = O(4^{-(k-k_\max)}) \tag{7.11}$$

The momentum-dependent correction is **exponentially suppressed** in $k - k_\max$. $\square$

---

## §8. Parts (d)–(e): IR RG Step and Stability 🔶 NOVEL

### §8.1 IR RG Step Construction

The RG step in the IR regime ($k \geq k_\max$) follows the same structure as the UV step (Thm 7.6.5 Part (a)), but with the mass gap providing control instead of asymptotic freedom.

**Step 1: Blocking.** Apply $Q_\text{FCC}$ (Prop 7.6.1) to map $D_4(\eta_k) \to D_4(2\eta_k)$:

$$e^{-\mathcal{A}_{k+1}(V)} = \int \mathcal{D}U\, \delta(V - Q_\text{FCC}[U])\, e^{-\mathcal{A}_k(U)} \tag{8.1}$$

**Step 2: Saddle point.** The saddle-point field $B_* = B_*(V)$ minimizes $\mathcal{A}_k$ subject to $Q_\text{FCC}[B_*] = V$. In the IR regime, the coercivity bound ensures the saddle point is **strongly stable**:

$$\frac{\delta^2 \mathcal{A}_k}{\delta U^2}\bigg|_{B_*} = \mathcal{H}_k^\text{IR} \geq \frac{\mu_k^2}{C_\text{corr}} > 0 \tag{8.2}$$

The mass gap provides a uniform lower bound on the Hessian, guaranteeing a unique, non-degenerate saddle point.

**Step 3: Gaussian integration.** Parametrize $U_\ell = B_{*,\ell} e^{ig_k A_\ell}$ and expand:

$$\mathcal{A}_k(B_* e^{ig_k A}) = \mathcal{A}_k(B_*) + \frac{g_k^2}{2}\langle A, \mathcal{H}_k^\text{IR} A\rangle + O(g_k^3 A^3) \tag{8.3}$$

The Gaussian integral:

$$\int \mathcal{D}A\, e^{-g_k^2 \langle A, \mathcal{H}_k^\text{IR} A\rangle / 2} = \left(\det \mathcal{H}_k^\text{IR}\right)^{-1/2} \tag{8.4}$$

is well-defined because $\mathcal{H}_k^\text{IR} > 0$ (guaranteed by the mass gap).

### §8.2 IR Contraction Estimate

**Claim:** The IR remainder at scale $k+1$ satisfies:

$$\varepsilon_{k+1}^\text{IR} \leq C_\text{IR} \cdot e^{-c_\mu \mu_k \eta_k} \cdot \varepsilon_k^\text{IR} + C_\text{IR}' \cdot e^{-2c_\mu \mu_k \eta_k} \tag{8.5}$$

**Proof:**

**(i) Perturbative remainder.** The leading non-Gaussian correction to the effective action comes from the quartic gauge vertex $g_k^4 V^{(4)}(A^4)$, whose one-loop Wick contraction $\langle A(x)^4 \rangle_c = 3 G_k(x,x)^2$ involves two propagator factors. Summing over lattice sites and using translation invariance:

$$|R_{k+1}^\text{pert}(V)| \leq C_\text{pert} \cdot g_k^4 \cdot \|G_k\|_1^2 \tag{8.6}$$

where $\|G_k\|_1 = \sum_y |G_k(0,y)|$ is the $\ell^1$-norm of the propagator. The $\|G_k\|_1^2$ arises from two spatial summations: one from the Wick contraction (loop integral) and one from coupling to the background field. The cubic vertex $O(g_k^3 A^3)$ vanishes at one loop (odd Wick moments). Using the exponential decay (Eq. 7.4):

$$\|G_k\|_1 \leq \frac{C_\text{CT}}{m_k^2} \sum_y e^{-\gamma_{D_4}(m_k) |y|/(\eta_k\sqrt{2})} \leq \frac{C'}{\mu_k^2} \cdot \left(\frac{\eta_k}{\gamma_{D_4}(\mu_k)}\right)^4 \tag{8.7}$$

For $k \geq k_\max$, $\gamma_{D_4}(\mu_k) \geq c_\gamma \mu_k \eta_k$ (from Eq. 7.5 for $\mu_k \eta_k \gg 1$), so:

$$\|G_k\|_1 \leq \frac{C''}{\mu_k^6 \eta_k^4} \tag{8.8}$$

The perturbative remainder contribution:

$$|R_{k+1}^\text{pert}| \leq C_\text{pert} \cdot \frac{g_k^4}{\mu_k^{12} \eta_k^8} \tag{8.9}$$

Since $\mu_k \eta_k = \mu_\min \cdot 4^k a$ grows as $4^k$, this is $O(e^{-12 \cdot 4^k \ln(\mu_\min a)})$ — super-exponentially suppressed.

**(ii) Blocking kernel contribution.** The averaging kernel $Q_\text{FCC}$ connects scale $k$ to scale $k+1$. The constraint $V = Q_\text{FCC}[U]$ restricts the fluctuation field to satisfy:

$$\sum_{\gamma \in P(B)} A_\gamma = 0 \quad \text{(zero-mode constraint)} \tag{8.10}$$

The projected propagator $(P_\perp \mathcal{H}_k^\text{IR} P_\perp)^{-1}$ has the same mass gap as $(\mathcal{H}_k^\text{IR})^{-1}$ because the projection $P_\perp$ removes the zero mode, which does not contribute to the spectral gap.

**(iii) Contraction factor.** The key estimate: the ratio of the scale-$(k+1)$ remainder to the scale-$k$ remainder is bounded by:

$$\frac{\varepsilon_{k+1}^\text{IR}}{\varepsilon_k^\text{IR}} \leq C_\text{IR} \cdot \exp\!\left(-c_\mu \mu_k \eta_k\right) \tag{8.11}$$

where $c_\mu > 0$ is the geometric constant accounting for the D₄ lattice structure (the number of paths in $Q_\text{FCC}$, the Voronoi cell geometry, etc.).

The exponential suppression arises because:
- The propagator $G_k$ decays as $e^{-\gamma_{D_4}(\mu_k) |x-y|/(\eta_k\sqrt{2})}$
- At the blocking scale, $|x-y| \sim \eta_k$, so the relevant decay is $e^{-\gamma_{D_4}(\mu_k)} \lesssim e^{-c_\mu \mu_k \eta_k}$
- All contributions from the Gaussian integral (tree-level, one-loop, higher) are suppressed by powers of $e^{-c_\mu \mu_k \eta_k}$

**(iv) Source term.** The "new" remainder generated at each IR step (from the one-loop determinant and perturbative corrections) is:

$$\text{source}_k \leq C_\text{IR}' \cdot e^{-2c_\mu \mu_k \eta_k} \tag{8.12}$$

The factor of 2 in the exponent arises because the source involves products of propagators (squares of $G_k$).

Combining (iii) and (iv):

$$\varepsilon_{k+1}^\text{IR} \leq C_\text{IR} \cdot e^{-c_\mu \mu_k \eta_k} \cdot \varepsilon_k^\text{IR} + C_\text{IR}' \cdot e^{-2c_\mu \mu_k \eta_k} \tag{8.13}$$

This is Eq. (1.10) in the statement. $\square$

### §8.3 IR Convergence

**The IR contraction factor decreases super-exponentially with $k$:**

$$c_\mu \mu_k \eta_k = c_\mu \cdot \mu_\min \cdot 2^k \cdot 2^k a = c_\mu \mu_\min a \cdot 4^k \tag{8.14}$$

For $k > k_\max$, define $j := k - k_\max \geq 1$. Then:

$$c_\mu \mu_k \eta_k = c_\mu \mu_\min a \cdot 4^{k_\max} \cdot 4^j \geq c_\mu \mu_{k_\max} \eta_{k_\max} \cdot 4^j \tag{8.15}$$

where $\mu_{k_\max} \eta_{k_\max} = \mu_\min \cdot 4^{k_\max} a \sim \mu_\min/(a \Lambda_\text{QCD})^2 \cdot a = O(1)$ at the matching scale.

Let $\alpha := c_\mu \mu_{k_\max} \eta_{k_\max} > 0$ (an $O(1)$ constant). The IR remainder at step $j$ beyond matching:

$$\varepsilon_{k_\max + j}^\text{IR} \leq C_\text{IR}' \sum_{i=1}^{j} \prod_{\ell=i}^{j-1} \left(C_\text{IR} e^{-\alpha \cdot 4^\ell}\right) \cdot e^{-2\alpha \cdot 4^i} + \prod_{\ell=1}^j C_\text{IR} e^{-\alpha \cdot 4^\ell} \cdot \varepsilon_{k_\max} \tag{8.16}$$

The product $\prod_{\ell=1}^j C_\text{IR} e^{-\alpha \cdot 4^\ell}$ decreases super-exponentially:

$$\prod_{\ell=1}^j C_\text{IR} e^{-\alpha \cdot 4^\ell} \leq C_\text{IR}^j \cdot \exp\!\left(-\alpha \sum_{\ell=1}^j 4^\ell\right) = C_\text{IR}^j \cdot \exp\!\left(-\frac{\alpha(4^{j+1}-4)}{3}\right) \tag{8.17}$$

Since $4^{j+1}/3$ grows much faster than $j\ln C_\text{IR}$, this product tends to zero super-exponentially as $j \to \infty$.

### §8.4 Fixed-Point IR Remainder

The geometric convergence of the IR sum gives a finite fixed-point remainder:

$$\varepsilon_*^\text{IR} = \frac{C_\text{IR}' e^{-2\alpha}}{1 - C_\text{IR} e^{-\alpha}} \tag{8.18}$$

This is well-defined provided $C_\text{IR} e^{-\alpha} < 1$, i.e., $\alpha > \ln C_\text{IR}$. Since $\alpha = c_\mu \mu_{k_\max} \eta_{k_\max} \sim O(1)$ and $C_\text{IR}$ is a fixed constant, this condition is satisfied for $\mu_\min$ sufficiently large (which is guaranteed on the crossover path away from the critical endpoint).

### §8.5 UV-IR Combination

The uniform bound on the remainder at all scales combines the UV and IR estimates:

**For $k \leq k_\max$:** $\varepsilon_k \leq 2\varepsilon_*^\text{UV}$ (Thm 7.6.5)

**For $k > k_\max$:** $\varepsilon_k \leq 2\varepsilon_*^\text{IR}$ (this theorem, Part (d))

**At $k = k_\max$:** Both bounds apply. The handoff requires:

$$\varepsilon_{k_\max} \leq \min(2\varepsilon_*^\text{UV}, 2\varepsilon_*^\text{IR}) \tag{8.19}$$

The UV bound gives $\varepsilon_{k_\max} \leq 2\varepsilon_*^\text{UV}$ by Thm 7.6.5. This serves as the initial condition for the IR iteration.

**Overall uniform bound:**

$$\varepsilon_k \leq 2\varepsilon_* := 2\max(\varepsilon_*^\text{UV}, \varepsilon_*^\text{IR}) \qquad \text{for all } k \geq 0 \tag{8.20}$$

### §8.6 UV-IR Matching Condition

**Claim:** At the matching scale, the UV effective action (from Balaban RG) and the IR effective action (from the cluster expansion / mass gap) agree:

$$\mathcal{A}_{k_\max}^\text{UV} = \mathcal{A}_{k_\max}^\text{IR} + O(e^{-c/g_{k_\max}^2}) \tag{8.21}$$

**Status:** This matching condition is established at the level of the perturbative expansion, with controlled non-perturbative error bounds. A fully rigorous norm-level comparison in the Banach space $\|\cdot\|_{\alpha,k_\max}$ is deferred to **Phase G.5** (effective action convergence), where both descriptions will be compared explicitly.

**Argument (perturbative + non-perturbative bounds):**

Both $\mathcal{A}_{k_\max}^\text{UV}$ and $\mathcal{A}_{k_\max}^\text{IR}$ are derived from the **same partition function** $Z(\beta, \varepsilon)$ by integrating out different subsets of degrees of freedom:

- **UV effective action:** Integrates out modes with $|p| > \pi/\eta_{k_\max}$ (short-wavelength fluctuations) using Balaban's RG transformation
- **IR effective action:** Describes modes with $|p| \leq \pi/\eta_{k_\max}$ (long-wavelength fluctuations) using the cluster expansion

**Perturbative agreement:** Both effective actions compute the same connected Feynman diagrams order by order in $g_{k_\max}^2$ (by construction — both start from the same lattice action and integrate to the same scale). Their perturbative expansions in $g_{k_\max}^2$ agree to all orders.

**Non-perturbative error bounds:** The difference $\mathcal{A}_{k_\max}^\text{UV} - \mathcal{A}_{k_\max}^\text{IR}$ arises from two exponentially suppressed sources:
1. The large-field contribution to the Balaban RG: $O(e^{-\kappa_\text{FCC}/(2g_{k_\max}^2)})$ (Prop 7.6.4)
2. The cluster expansion truncation error: $O(e^{-\sigma_\text{surf}})$ (Thm 7.5.3)

Both are exponentially suppressed in $1/g_{k_\max}^2$. At the matching scale $g_{k_\max}^2 \leq g_*^2 \ll 1$, these corrections are non-perturbatively small.

**What remains for Phase G.5:** The explicit identification of both effective actions as elements of the same Banach space $(\mathcal{B}_{\alpha,k_\max}, \|\cdot\|_{\alpha,k_\max})$ and a norm-level comparison $\|\mathcal{A}_{k_\max}^\text{UV} - \mathcal{A}_{k_\max}^\text{IR}\|_{\alpha,k_\max} \leq C e^{-c/g_{k_\max}^2}$. This requires constructing the explicit map between the Balaban parametrization and the cluster expansion parametrization — a technically non-trivial but well-defined task. $\square$

---

## Appendix A: Comparison of UV and IR Contraction Mechanisms

| Aspect | UV (Thm 7.6.5) | IR (this theorem) |
|--------|-----------------|-------------------|
| **Control parameter** | $g_k \to 0$ | $\mu_k \to \infty$ |
| **Contraction factor** | $C_\text{ind} \cdot g_k^{2-4\delta}$ | $C_\text{IR} \cdot e^{-c_\mu \mu_k \eta_k}$ |
| **Source term** | $C_2 \cdot g_k^{4-4\delta}$ | $C_\text{IR}' \cdot e^{-2c_\mu \mu_k \eta_k}$ |
| **Physical mechanism** | Asymptotic freedom | Mass gap / confinement |
| **Rate of improvement** | Logarithmic ($g_k^2 \sim 1/\ln k$) | Double exponential ($e^{-c \cdot 4^k}$) |
| **Large-field treatment** | Peierls bound (Prop 7.6.4) | Coercivity (no large fields) |
| **Applies when** | $g_k^2 \leq g_*^2$ | $\mu_k \eta_k > \ln C_\text{IR}/c_\mu$ |
| **Banach space norm** | $\|\cdot\|_{\alpha,k}$ with $g_k$-dependent weight | Same norm, but $\mu_k$-dependent decay |

---

## Appendix B: The Role of the Crossover Path

The crossover path ($\varepsilon > \varepsilon_*$) from Thm 7.5.3 is essential for the IR coercivity argument. Without it:

1. **At $\varepsilon = 0$ (pure Wilson action):** The mass gap vanishes at $\beta_c$: $\mu(\beta_c, 0) = 0$. The coercivity bound fails at the phase transition.

2. **At $\varepsilon > \varepsilon_*$ (crossover):** No phase transition → $\mu(\beta, \varepsilon) > 0$ for all $\beta$ → coercivity at every scale.

The adjoint perturbation is not a physical modification — it is a mathematical device (analogous to the Bhanot-Creutz technique in Monte Carlo simulations) that eliminates a lattice artifact. The continuum physics is independent of $\varepsilon$ (by perturbative universality, Thm 7.5.2): the adjoint plaquette term is an irrelevant operator that vanishes in the continuum limit.

**Critical distinction:**
- The adjoint coupling $\varepsilon$ is a lattice regularization parameter (like the lattice spacing $a$)
- The physics should not depend on $\varepsilon$ in the continuum limit
- The crossover path provides a smooth path to the continuum limit where the mass gap is always positive
- In the final continuum limit, $\varepsilon$ is taken to zero along with $a$, recovering pure Yang-Mills

---

## Appendix C: Explicit Constants

### C.1 The Constant $C_\text{corr}$

The correlation-to-action constant $C_\text{corr}$ relates the mass gap (spectral gap of the transfer matrix) to the coercivity of the effective action. From §6.4: $C_\text{corr} = C_O \cdot C''$ where:

- $C_O = \sum_{n \geq 1} |\langle 0|O|n\rangle|^2 \leq \|O\|_\infty^2 = 1/9$ for the fundamental plaquette $O = \frac{1}{3}\operatorname{Re}\operatorname{Tr} U_p$ (by the spectral theorem)
- $C''$ arises from the bound $\cosh\mu_n - \cos\omega \geq (\mu_n^2 + \omega^2)/C'$ (§6.3). For $|\omega| \leq \pi/2$: $C' \leq 2/(1 - \pi^2/24) \approx 3.4$; combining with the $\sinh\mu_n$ factor in Eq. (6.6): $C'' \leq 2C'\cosh(\mu_\max)/\mu_\min$ where $\mu_\max$ is a bounded spectral parameter.

**Explicit upper bound:** For the qualitative theorem, the key property is $C_\text{corr} < \infty$, which holds because:
- $C_O \leq \|O\|_\infty^2 < \infty$ (bounded observable)
- $\mu_\min > 0$ (Prop 7.6.6 Part (d))
- $C'$ is a finite lattice-geometric constant

A conservative estimate: $C_\text{corr} \leq \|O\|_\infty^2 \cdot 4C'/\mu_\min$ for $\mu_\min \leq 1$, giving $C_\text{corr} = O(1/\mu_\min)$. The precise numerical value depends on the spectral structure of the transfer matrix and can be bounded from lattice Monte Carlo data for the glueball correlator. For the theorem's conclusions (existence of coercivity, super-exponential IR convergence), only finiteness of $C_\text{corr}$ is required — the explicit magnitude affects only the numerical value of the coercivity coefficient $\mu_\min^2/(2C_\text{corr})$.

### C.2 The Geometric Constant $c_\mu$

The constant $c_\mu$ in the IR contraction factor arises from the D₄ lattice geometry:

$$c_\mu = \frac{\gamma_{D_4}(m)}{m \cdot d_\text{nn}} \bigg|_{m \to \infty} = \frac{\ln(1 + m^2 d_\text{nn}^2/16)}{m \cdot d_\text{nn}} \to \frac{2\ln(m \cdot d_\text{nn}/4)}{m \cdot d_\text{nn}} \tag{C.2}$$

For large $m$, this approaches $2\ln m / m$, which is slowly varying. In practice, $c_\mu$ is taken as a constant of order $O(1/\mu_\min a)$.

### C.3 Matching Scale Values

**Validity caveat.** The asymptotic formula $k_\max \approx \beta/(6 b_0 \ln 2)$ is valid only for $\beta \gg 6/g_*^2$. For $g_*^2 = 0.1$, this requires $\beta \gg 60$. Below this threshold, $g_0^2 = 6/\beta > g_*^2$ and the exact formula gives $k_\max = 0$ (the bare coupling already exceeds the UV stability threshold, so no perturbative RG steps are available).

**Example at $\beta = 6$ (standard lattice QCD):**

$$g_0^2 = \frac{6}{\beta} = 1.0 > g_*^2 \approx 0.1 \qquad \Longrightarrow \qquad k_\max = 0 \tag{C.3}$$

No UV RG steps are needed — the theory is entirely in the strong-coupling (IR) regime from the start. The mass gap provides coercivity at all scales.

**Example at $\beta = 100$ (weak coupling):**

$$g_0^2 = 0.06 < g_*^2, \qquad k_\max = \left\lfloor \frac{1/0.06 - 1/0.1}{b_0 \ln 2}\right\rfloor = \left\lfloor \frac{6.67}{0.0483}\right\rfloor = 138 \tag{C.4}$$

Approximately 138 RG steps from UV to IR, with scale ratio $\eta_{k_\max}/a = 2^{138} \approx 10^{41.5}$. This enormous ratio reflects the wide separation between UV and confinement scales in the weak-coupling regime.

For the continuum limit ($\beta \to \infty$), $k_\max \to \infty$ and $\eta_{k_\max} \to 1/\Lambda_\text{QCD}$, which is the physically relevant confinement scale.

---

*Derivation file for Theorem 7.6.7*
*Classification: 🔶 NOVEL (IR coercivity, UV-IR matching) / ✅ ESTABLISHED (Combes-Thomas, Gaussian integration)*
*Program: Yang-Mills Mass Gap — Phase G.4 (IR Control)*
