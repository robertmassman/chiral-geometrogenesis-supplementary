# Stella Genesis

**Can Paper 2 dynamics emerge from Paper 1 geometry alone?**

This directory contains a series of computational experiments testing whether
the stella octangula and its Z₃ field dynamics are sufficient to produce
inter-component coupling, self-organization, and mass generation — without
postulating these as separate axioms.

---

## Research Documents

| Document | Status | Description |
|----------|--------|-------------|
| [RESULTS-Phase1.md](RESULTS-Phase1.md) | Complete | Core G1 dynamics: coherence, chirality, enhanced VM, mesh scaling, Kuramoto, mass observables |
| [RESULTS-Crystallization.md](RESULTS-Crystallization.md) | Complete | Geometry selection: Z₃ interactions crystallize the stella octangula from first principles |
| [RESEARCH-Prime-Interference.md](RESEARCH-Prime-Interference.md) | Complete | Fisher information geometry applied to prime distribution (H1-H7) |
| [RESEARCH-Stella-Computation.md](RESEARCH-Stella-Computation.md) | Complete | Computational complexity of stella dynamics (C1-C7): P-class, no quantum advantage |
| [GPU-TEST-PLAN.md](GPU-TEST-PLAN.md) | **Active** | Metal GPU validation of double-buffered snapshot execution (G1-G6, GG1-GG4) |

---

## Experiment Phase Map

### RESULTS-Phase1.md — G1 Dynamics

| Section | Phases | Key Finding |
|---------|--------|-------------|
| Baseline (3 modes) | 1 | VM + coupling produces coherence (corr 0.388 vs 0.333 random) |
| Coupling sweep | 2 | Saturation at cs >= 0.7; coupling creates global coherence |
| Chirality | 3 | Right-handed pressure (chi=0.15) breaks T+/T- symmetry |
| Enhanced VM | 4 | SENSE/IF/PHASE instructions boost correlation to 0.423 |
| StellaLang comparison | 5 | Genesis matches StellaLang coherence without explicit CPY01 |
| Open items | 7-8 | Mesh scaling, per-color pressure, phase-lock, Kuramoto, mass observables |
| Long-timescale | H16 | Stationary dynamics to 50M epochs (no phase transitions) |

### RESULTS-Crystallization.md — Geometry Selection

| Phase | Question | Result |
|-------|----------|--------|
| A | Does the stella win a polyhedra competition? | Not dynamically — specialness is group-theoretic |
| B | Do 8 points crystallize into a stella? | Yes, 100% convergence at alpha/beta >= 2 |
| C | Does the system select N=8? | Yes, grand canonical + label relaxation both converge |
| D | Does a sphere emerge from repulsion alone? | Yes, from generic 3D repulsion |
| E | Does Z₃ representation structure emerge? | Yes, from information-theoretic stability |
| F1-F3 | Fisher metric, computational richness, prime irreducibility | N=3 threshold, CRT factorization, prime detection |
| G | Why complex numbers? | Hurwitz theorem selects C from {R, C, H, O} |

### RESEARCH-Prime-Interference.md — Number Theory

| Phase | Question | Result |
|-------|----------|--------|
| H1 | Do Fisher eigenvalues follow GUE statistics? | Partial match at small N |
| H2 | Spectral decomposition of irreducibility index? | Zeta-zero coefficients computed |
| H3 | Discrete operator converging to zeta zeros? | Constructed, partial convergence |
| H4 | True dimensionality of prime interference? | Fisher rank analysis complete |
| H5-H7 | Deeper connections | Structural parallel confirmed; no computational advantage (H7) |

### RESEARCH-Stella-Computation.md — Complexity Theory

| Phase | Question | Result |
|-------|----------|--------|
| C1 | P-completeness of soup dynamics? | NULL — race conditions, not P-complete |
| C1b/C1c | Parallel execution semantics? | Snapshot closest (KL=0.030); ordering gives +0.163 entropy gap |
| C3 | Z₃ as computational resource? | NULL — classical interference only |
| C4 | chi=4 topology for error correction? | NULL — no non-abelian braiding |
| C5 | Continuum limit advantage? | NULL — standard PDE iteration |
| C7 | Complexity class? | P (standard TM), Level 1 natural computation only |

### GPU-TEST-PLAN.md — GPU Validation (Active)

| Test | Question | Status |
|------|----------|--------|
| G1-G6 | CPU vs GPU parity, scaling, float32, ensembles | Complete |
| GG1 | Snapshot vs sequential on real GPU | PASS |
| GG2 | Scale advantage at high n_sub | FAIL at high resolution |
| GG4 | Statistical ensemble viability | PASS (n_sub <= 128) |

---

## Quick Start

```bash
# Build the genesis soup simulator
cc -O3 -o genesis_soup genesis_soup.c -lm

# Run Mode 0: VM + geometric coupling (primary experiment)
./genesis_soup 5000000 42 0.5 0 16 0.001 0.1 | tee results_mode0.log

# Run Mode 1: coupling only (no VM)
./genesis_soup 5000000 42 0.5 1 16 0.001 0.1 | tee results_mode1.log

# Run Mode 2: VM only (no coupling — control)
./genesis_soup 5000000 42 0.5 2 16 0.001 0.1 | tee results_mode2.log

# Analyze
python3 analyze_genesis.py --compare results_mode0.log results_mode1.log results_mode2.log
```

## Arguments

```
./genesis_soup [epochs] [seed] [coupling_strength] [mode] [n_sub] [mutation_rate] [epsilon]
```

| Arg | Default | Description |
|-----|---------|-------------|
| epochs | 5000000 | Total epochs |
| seed | 42 | RNG seed |
| coupling_strength | 0.5 | Geometric coupling rate (0.0-1.0) |
| mode | 0 | 0=VM+coupling, 1=coupling-only, 2=VM-only |
| n_sub | 16 | Mesh subdivision (sites ~ 2n^2+2 per tetrahedron) |
| mutation_rate | 0.001 | Per-trit mutation probability |
| epsilon | 0.1 | Pressure function regularization |

## Diagnostics

| Field | Random baseline | Meaning |
|-------|-----------------|---------|
| H_tp, H_tm | 1.585 | Trit entropy (lower = more ordered) |
| corr | 0.333 | T+/T- co-located trit agreement |
| auto_tp, auto_tm | 0.333 | Spatial neighbor agreement |
| local_repl | 0.333 | Local patch T+/T- match density |
| dir_bias | 0.500 | Fraction of couplings going T+ -> T- |

## Language Policy

All verification tests should be written in **C** unless Python is clearly the
best option (e.g., data analysis, plotting, or leveraging scientific libraries).
C is preferred for simulation kernels, VM implementations, and performance-critical code.

## Relationship to StellaLang

This is a **separate research direction** from `stella_lang/`.

- **StellaLang:** CPY01 is an explicit instruction (Paper 2: Thm 0.2.1)
- **Genesis:** Inter-component coupling emerges from pressure gradients (Paper 1: Def 0.1.3)

If Genesis produces self-organization, it demonstrates that Paper 2 dynamics
are derivable from Paper 1 foundations.
