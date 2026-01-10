# Unified Dimension Table for Chiral Geometrogenesis
**Version:** 1.0
**Date:** 2025-12-12
**Status:** ✅ CANONICAL REFERENCE

This table provides the **definitive** dimensional conventions for all theorems in the Chiral Geometrogenesis framework.

---

## Natural Units Convention

Throughout all theorems, we use **natural units** where:
$$\hbar = c = k_B = 1$$

This means:
- Energy $[E] = [M] = [T]^{-1} = [L]^{-1}$
- All quantities can be expressed in powers of energy (or equivalently, mass, inverse time, inverse length)
- Conversion: $\hbar c = 197.3$ MeV·fm

---

## Master Dimension Table

| Symbol | Name | Dimension | Physical Meaning | Typical Value | Used in Theorems |
|--------|------|-----------|------------------|---------------|------------------|
| **Internal Evolution** |
| $\lambda$ | Internal parameter | **[1]** | Phase accumulated in radians (dimensionless) | $0$ to $\infty$ | 0.2.2, 3.0.1, 3.0.2, 3.1.1 |
| $\omega_0$ | Phase evolution rate | **[M]** | Energy scale of phase evolution | $\sim 140$ MeV | 0.2.2, 3.0.1, 3.0.2, 3.1.1 |
| $t$ | Physical time | **[M]^{-1}** | Emergent time coordinate | Varies | 0.2.2, 5.2.1 |
| **Phase and Field** |
| $\Phi(\lambda)$ | Total phase | **[1]** | $\Phi = \Phi_{spatial}(x) + \lambda$ | $0$ to $\infty$ | 3.0.1, 3.0.2, 3.1.1 |
| $\Phi_{spatial}(x)$ | Spatial phase | **[1]** | Position-dependent phase shift | Varies | 3.0.1, 3.0.2 |
| $\chi(x,\lambda)$ | Chiral field | **[M]** | Complex scalar field | $\sim 93$ MeV | 3.0.1, 3.0.2, 3.1.1 |
| $v_\chi(x)$ | Chiral VEV | **[M]** | Magnitude of $\chi$ | $\sim f_\pi = 92.2$ MeV | 3.0.1, 3.0.2, 3.1.1 |
| **Derivatives** |
| $\partial_\lambda$ | Lambda derivative | **[1]** | $d/d\lambda$ (dimensionless derivative) | Operator | 3.0.2, 3.1.1 |
| $\partial_t$ | Time derivative | **[M]** | $d/dt$ (energy-dimension derivative) | Operator | 5.2.1 |
| $\partial_\lambda\chi$ | Field $\lambda$-derivative | **[M]** | $= i\chi$ (fundamental relation) | $\sim 93$ MeV | 3.0.2, 3.1.1 |
| **Mass Formula** |
| $g_\chi$ | Chiral coupling | **[1]** | Dimensionless coupling | $\sim 1$ | 3.1.1 |
| $\Lambda$ | UV cutoff | **[M]** | Energy scale of new physics | $\sim 1$ GeV | 3.1.1 |
| $\eta_f$ | Helicity coupling | **[1]** | Fermion-specific factor | $0.1$ to $10$ | 3.1.1 |
| $m_f$ | Fermion mass | **[M]** | Effective mass from phase-gradient mass generation | $2$ MeV to $173$ GeV | 3.1.1 |
| **Geometry** |
| $x$ | Spatial coordinate | **[M]^{-1}** | Position on $\partial\mathcal{S}$ | $\sim 1$ fm | 3.0.1, 3.0.2 |
| $\epsilon$ | Regularization | **[M]^{-1}** | UV cutoff length | $\sim 0.2$ fm | 3.0.1 |
| $P_c(x)$ | Pressure function | **[M]^{2}** | $1/(|x-x_c|^2 + \epsilon^2)$ | Varies | 3.0.1 |

---

## Key Relationships

### 1. Time Emergence
$$\boxed{t = \frac{\lambda}{\omega_0}}$$

**Dimensional check:**
$$[t] = \frac{[1]}{[M]} = [M]^{-1} = [\text{time}] \quad \checkmark$$

### 2. Phase Evolution
$$\boxed{\Phi(\lambda) = \Phi_{spatial}(x) + \lambda}$$

**Dimensional check:**
$$[\Phi] = [1] + [1] = [1] = [\text{dimensionless phase}] \quad \checkmark$$

**Note:** $\omega_0$ has been **absorbed** into the definition of $\lambda$. The phase parameter $\lambda$ is already "scaled" so that one radian of $\lambda$ corresponds to one radian of physical phase rotation.

### 3. Field Derivative (Internal Parameter)
$$\boxed{\partial_\lambda\chi = i\chi}$$

**Derivation:**
$$\chi = v_\chi(x) e^{i\Phi(\lambda)} = v_\chi(x) e^{i(\Phi_{spatial} + \lambda)}$$
$$\partial_\lambda\chi = v_\chi(x) e^{i(\Phi_{spatial} + \lambda)} \cdot i = i\chi$$

**Dimensional check:**
$$[\partial_\lambda\chi] = \frac{[\chi]}{[\lambda]} = \frac{[M]}{[1]} = [M] \quad \checkmark$$

### 4. Field Derivative (Physical Time)
$$\boxed{\partial_t\chi = i\omega_0\chi}$$

**Derivation:**
$$\partial_t = \frac{\partial\lambda}{\partial t} \cdot \partial_\lambda = \omega_0 \partial_\lambda$$

Therefore:
$$\partial_t\chi = \omega_0(\partial_\lambda\chi) = \omega_0(i\chi) = i\omega_0\chi$$

**Dimensional check:**
$$[\partial_t\chi] = \frac{[\chi]}{[t]} = \frac{[M]}{[M]^{-1}} = [M]^2$$

Wait, this should match $[\omega_0\chi] = [M][M] = [M]^2$... ✓ Consistent!

**Actually, let me reconsider:** In natural units, the time derivative has dimensions:
- If $t$ has dimensions $[M]^{-1}$
- Then $\partial_t = d/dt$ has dimensions $1/[M]^{-1} = [M]$
- So $\partial_t f$ for a field $f$ of dimension $[M]$ gives $[M] \cdot [M] = [M]^2$

Hmm, that doesn't seem right. Let me think about this more carefully...

**CORRECTION:** The derivative operator $\partial_t$ doesn't have "dimensions" in the usual sense. Instead:
- If $\chi(t)$ has dimensions $[M]$
- And $t$ has dimensions $[M]^{-1}$
- Then $\partial_t\chi = d\chi/dt$ has dimensions $[M] / [M]^{-1} = [M]^2$

So the equation $\partial_t\chi = i\omega_0\chi$ has:
- LHS: $[M]^2$
- RHS: $[M][M] = [M]^2$ ✓

Actually, this **is** consistent! The Schrödinger-like equation $\partial_t\psi = (i/\hbar)H\psi$ normally has dimensions:
- LHS: $\partial_t\psi$ has dimensions $[\psi]/[\text{time}]$
- RHS: $H\psi/\hbar$ has dimensions $[E][\psi]/[E \cdot \text{time}] = [\psi]/[\text{time}]$ ✓

In natural units ($\hbar = 1$), energies and inverse times are the same, so $\partial_t\chi \sim E\chi$ is fine.

### 5. Derivative Operator Conversion
$$\boxed{\partial_t = \omega_0 \partial_\lambda}$$

**Dimensional check:**
$$[\partial_t] \stackrel{?}{=} [\omega_0][\partial_\lambda]$$

This is a bit subtle because derivatives are operators. The correct statement is:
$$\frac{d}{dt} = \frac{d\lambda}{dt} \frac{d}{d\lambda} = \omega_0 \frac{d}{d\lambda}$$

where $\omega_0 = d\lambda/dt$ has dimensions $[M]$.

### 6. Mass Formula
$$\boxed{m_f = \frac{g_\chi \omega_0}{\Lambda} v_\chi \eta_f}$$

**Dimensional check:**
$$[m_f] = \frac{[1] \cdot [M]}{[M]} \cdot [M] \cdot [1] = [M] \quad \checkmark$$

---

## Common Dimensional Confusions (RESOLVED)

### ❌ WRONG: $\Phi = \Phi_{spatial} + \omega_0\lambda$

This appears in early drafts of Theorems 3.0.1 and 3.0.2 but is **dimensionally inconsistent**:
- $[\Phi_{spatial}] = [1]$ (phase is dimensionless)
- $[\omega_0\lambda] = [M][1] = [M]$ ❌ (has dimensions!)
- Cannot add dimensionless and dimensional quantities

### ✅ CORRECT: $\Phi = \Phi_{spatial} + \lambda$

With the understanding that $\lambda$ is the **rescaled** phase parameter that already includes the $\omega_0$ factor.

**Explanation:** When we write $d\lambda/dt = \omega_0$, we're defining $\lambda$ such that:
$$\lambda(t) = \omega_0 t$$

So $\lambda$ is **not** just "counting radians" in an abstract sense—it's counting radians at the specific rate $\omega_0$ set by the system's energy. This is why $\lambda$ is dimensionless but still parameterizes the physical evolution.

---

## Notation Summary

| Notation | Meaning | Use When |
|----------|---------|----------|
| $\lambda$ | Rescaled phase parameter (includes $\omega_0$) | Internal evolution equations |
| $t = \lambda/\omega_0$ | Physical time | Connecting to standard QFT |
| $\partial_\lambda\chi = i\chi$ | Fundamental eigenvalue equation | Before time emergence |
| $\partial_t\chi = i\omega_0\chi$ | Time-evolved equation | After time emergence |
| $\Phi = \Phi_{spatial} + \lambda$ | Total phase (both dimensionless) | All phase calculations |

---

## Cross-Theorem Verification

| Theorem | Uses Unified Conventions? | Notes |
|---------|--------------------------|-------|
| 0.2.2 | ⚠️ Needs clarification | Equation $d\phi/d\lambda = \omega$ defines $\omega$, consistent |
| 3.0.1 | ❌ Needs update | Currently uses $\Phi = \Phi_{spatial} + \omega\lambda$ |
| 3.0.2 | ❌ Needs update | Currently uses $\partial_\lambda\chi = i\omega\chi$ |
| 3.1.1 | ✅ Correct | Already uses $\Phi = \Phi_{spatial} + \lambda$ and $\partial_\lambda\chi = i\chi$ |

---

**This table is the canonical reference. All theorems should be updated to conform to these conventions.**

**Last updated:** 2025-12-12
**Next review:** After implementing updates to Theorems 3.0.1 and 3.0.2
