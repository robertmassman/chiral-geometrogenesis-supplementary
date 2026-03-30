# Stella Genesis: G1-Only Geometric Substrate

## Purpose

Test whether Paper 2 dynamics (inter-component coupling, arrow of time,
self-replication) **emerge** from Paper 1 (G1) foundations alone, without
postulating them as instructions.

## Name

**Stella Genesis** — the emergence of dynamics from pure geometry.
Named to distinguish from StellaLang/Stella Soup, which postulate CPY01
as an explicit instruction grounded in Paper 2 (Thm 0.2.1 + Prop 0.0.17c).

## Core Hypothesis

> If the stella octangula's geometry (Def 0.1.1) and pressure functions
> (Def 0.1.3) are computationally sufficient, then directed information
> transfer between T₊ and T₋ should emerge as a geometric consequence,
> producing self-organizing patterns without an explicit copy instruction.

## G1 Foundations Used

| Foundation | Source | Role in Genesis |
|-----------|--------|-----------------|
| Two-component ∂S | Def 0.1.1 | T₊ and T₋ surfaces with separate trit arrays |
| Z₃ phase structure | Def 0.1.2 | Trit values {0, 1, 2}, identity element 0 |
| Z₃ identity test | Def 0.1.2 | Loop gates test trit == 0 |
| Z₃ rotation | Def 0.1.2 | ROT: +1 mod 3; DROT: +2 mod 3 |
| Pressure functions | Def 0.1.3 | P_c(x) = 1/(|x - x_c|² + ε²), axioms P1–P5 |
| Geometric interpenetration | Def 0.1.1 | T₊ and T₋ share ℝ³ embedding |
| Polyhedral vertices | Def 0.0.0 | T₊: (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1); T₋: negated |

## What Is NOT Used (Paper 2+)

| Removed | Was in StellaLang | Why removed |
|---------|-------------------|-------------|
| CPY01 | Thm 0.2.1 + Prop 0.0.17c | Inter-component coupling should emerge |
| CPY10 | Thm 0.2.1 | Reverse coupling should emerge |
| FWD1 | Computational (M) | Second head eliminated |
| Arrow of time | Prop 0.0.17c | Directionality should emerge from Z₃ identity asymmetry |
| λ-ordering | Def 0.2.2 | Sequential execution tested as emergent necessity |

## Architecture

### GenesisVM — Single-Head G1 Instruction Set

Programs are sequences of Z₃ trit pairs. Each pair decodes to one of 9
opcodes. Only G1-grounded operations are non-trivial:

| Trit pair | Opcode | Instruction | G1 Source | Notes |
|-----------|--------|-------------|-----------|-------|
| (0,0) | 0 | NOP | Def 0.1.2 (identity) | |
| (0,1) | 1 | ROT | Def 0.1.2 (Z₃ +1) | R→G→B chirality |
| (0,2) | 2 | DROT | Def 0.1.2 (Z₃ +2) | Inverse rotation |
| (1,0) | 3 | FWD | Computational (M) | Advance head |
| (1,1) | 4 | BCK | Computational (M) | Retreat head |
| (1,2) | 5 | OPEN | Def 0.1.2 (Z₃ test) | if tape[h]==0, skip to ] |
| (2,0) | 6 | CLOSE | Def 0.1.2 (Z₃ test) | if tape[h]!=0, jump to [ |
| (2,1) | 7 | NOP1 | Def 0.1.2 (identity) | Was CPY01 slot |
| (2,2) | 8 | NOP2 | Def 0.1.2 (identity) | Was CPY10 slot |

**Key difference from StellaLang:** No copy instruction. No second head.
Programs can only modify their own trits via ROT/DROT and navigate via FWD/BCK.

### Geometric Coupling — The Replacement for CPY01

After VM execution, **pressure-mediated trit transfer** occurs between
co-located sites on T₊ and T₋. This is the central experimental variable.

**Pressure at site x on T_a (a = ±):**

    P_a(x) = max_{v ∈ vertices(T_a)} 1/(|x - v|² + ε²)

This follows Def 0.1.3 axioms P1 (max at source vertex) and P5 (monotonic decay).

**Coupling rule at co-located site pair (x_+, x_-):**

    ΔP = P_+(x) - P_-(x)
    coupling_prob = coupling_strength × |ΔP| / (P_+(x) + P_-(x))

    if ΔP > 0: trit at x_- ← trit at x_+  (T₊ dominates, overwrites T₋)
    if ΔP < 0: trit at x_+ ← trit at x_-  (T₋ dominates, overwrites T₊)

**Physical interpretation:**
- Near T₊ vertices: P₊ >> P₋, so information flows T₊ → T₋
- Near T₋ vertices: P₋ >> P₊, so information flows T₋ → T₊
- At center (W-axis): P₊ ≈ P₋, minimal coupling
- The "arrow" is spatially varying, not globally postulated

### Interaction Model

Each epoch:
1. Pick a random site on T₊ (center_a)
2. Find co-located site on T₋ (same mesh position)
3. Extract BFS patches of prog_size trits around each
4. Execute each patch independently using GenesisVM (single-head, no CPY)
5. Apply geometric coupling to the patch overlap region
6. Apply per-trit mutation with probability μ
7. Write patches back to surfaces

## Experimental Modes

### Mode A: Pure Geometric Coupling (no VM)
- Skip step 4 (no program execution)
- Only pressure-mediated trit transfer
- Tests: does geometry alone create spatial order?

### Mode B: G1 VM + Geometric Coupling
- Full pipeline: execute then couple
- Tests: does computation + geometry produce self-replication?

### Mode C: Coupling Strength Sweep
- Scan coupling_strength from 0.0 to 1.0
- Tests: is there a critical coupling threshold for emergence?

### Mode D: Sequential vs Parallel
- Compare sequential epoch updates vs batch-parallel
- Tests: does λ-ordering emerge as a necessity?

## Success Criteria

The experiment succeeds if ANY of the following are observed:

1. **Trit entropy reduction** — entropy drops below maximum (1.585 bits),
   indicating self-organization
2. **Spatial pattern formation** — non-random spatial structure on ∂S
3. **Replicator emergence** — programs that reproduce themselves through
   geometric coupling (not through CPY01, which doesn't exist)
4. **Directional bias** — net T₊ → T₋ information flow emerging from
   pressure asymmetry (reproducing Prop 0.0.17c)

## Comparison with StellaLang

| Property | StellaLang (Soup) | Stella Genesis |
|----------|-------------------|----------------|
| Instructions | 9 (5P + 4M) | 7 (5P + 2M) + 2 NOP |
| Copy mechanism | CPY01 instruction (P) | Geometric pressure coupling |
| Arrow of time | Postulated (Prop 0.0.17c) | Emergent from Z₃ + pressure |
| Inter-surface coupling | Instruction-driven | Environment-driven |
| Second head | h1 (explicit) | None |
| Self-replication | Programs copy themselves | Geometry copies patterns |

## Parameters

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| n_sub | 16 | 8–64 | Mesh subdivision level |
| prog_size | 24 | 12–48 | Trits per program/patch |
| coupling_strength | 0.5 | 0.0–1.0 | Geometric coupling rate |
| mutation_rate | 0.001 | 0–0.05 | Per-trit mutation rate |
| max_steps | 729 | 100–2000 | Max VM steps per execution |
| epsilon | 0.1 | 0.01–1.0 | Pressure regularization |
| epochs | 30000000 | — | Total epochs |
| seed | 42 | — | RNG seed |

## Dependencies

- Def 0.0.0 (Minimal Geometric Realization) — vertex coordinates
- Def 0.1.1 (Stella Octangula Boundary Topology) — two-component ∂S
- Def 0.1.2 (Three Color Fields) — Z₃ structure
- Def 0.1.3 (Pressure Functions) — P_c(x) axioms P1–P5

No Paper 2+ dependencies.

## File Structure

```
stella_genesis/
├── spec.md              # This file
├── genesis_soup.c       # C implementation (self-contained)
├── analyze_genesis.py   # Analysis and visualization
└── README.md            # Quick-start guide
```
