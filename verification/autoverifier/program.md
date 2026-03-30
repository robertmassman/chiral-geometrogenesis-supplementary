# AutoVerifier-CG: Audit Direction

This file controls what the autoverifier focuses on and how it conducts audits.
Edit this to steer priorities. The agent reads this at the start of each module.

---

## Current Focus

Complete the three-layer audit protocol for all thematic groups, starting
with the most foundational:

1. **G2 (Gauge Theory & Confinement)** — Direct downstream of G1, many cross-group exports
2. **G6 (QCD Scale Derivation)** — Numerical chain that feeds G5, G10, G12
3. **G3 (Time & Entropy)** — Feeds G8 (Gravity); time emergence is critical
4. **G4 (Chirality & CP Violation)** — Feeds G12 predictions

## Audit Posture

### Layer 1 (Coherence) — Defensive
- Check that definitions, notation, and numerical values are IDENTICAL
  across all proofs within the group
- Cross-reference with G1 exports to ensure imports are correct
- Verify dependency chains are acyclic
- Flag any notation drift (same concept, different symbol)

### Layer 2 (Validity) — Defensive
- V1 first: inventory ALL assumptions, classify as (E)stablished / (F)ramework / (H)ypothesis
- V3 early: hunt for semantic circularity (different proofs assuming same thing under different names)
- V2: verify each derivation step against cited theorem's actual hypotheses
- Flag SMUGGLED assumptions aggressively — better to over-flag than miss one

### Layer 3 (Adversarial) — Offensive
- Try to BUILD counterexamples and alternative frameworks
- For each uniqueness claim, attempt to construct a viable alternative
- For each numerical prediction, stress-test with 10% parameter variations
- Be genuinely adversarial — the goal is to find weaknesses

## Rules for the Agent

- **Read-only**: Do NOT modify proof documents. Write only audit reports.
- **Be honest**: If a proof step is unconvincing, say so. Don't rationalize gaps.
- **Be specific**: Cite exact file, section, and line when flagging issues.
- **Use G1 as template**: Follow the established format from G1 audit reports.
- **Classify findings correctly**:
  - SOUND: Step is mathematically correct and physically justified
  - QUALIFIED: Correct under stated conditions (conditions must be explicit)
  - WEAK: Logically valid but relies on questionable assumptions
  - INVALID: Contains a logical error or unjustified step
  - SMUGGLED: An undeclared assumption entering without being flagged
- **Adversarial classifications**:
  - SURVIVED: Attack failed; conclusion is robust
  - DENTED: Attack found a sensitivity but conclusion still holds
  - CRACKED: Attack revealed a genuine weakness that needs repair
  - BROKEN: Attack succeeded; conclusion is compromised

## What NOT to Do

- Don't modify any proof files
- Don't skip modules — execute in order
- Don't give a PASS without actually reading and verifying
- Don't assume G1 results without checking the imports are correct
- Don't count re-derivations of the same result as independent support

---

*Last updated: 2026-03-14*
