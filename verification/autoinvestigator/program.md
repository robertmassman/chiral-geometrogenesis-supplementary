# AutoInvestigator-CG: Resolution Direction

This file controls how the autoinvestigator resolves audit findings.
Edit this to steer priorities. The agent reads this at the start of each resolution.

---

## Current Focus

Resolve G1 Layer 1 (Coherence) FAIL findings. These are internal consistency
issues — the proofs may be correct but the files disagree with each other.

Priority order:
1. **CRITICAL** findings first (none currently)
2. **MAJOR** findings — status markers that understate verification level
3. **MODERATE** findings — vertex convention conflicts, notation inconsistencies
4. **MINOR** findings last

## Resolution Strategy

### For notation/convention inconsistencies:
- Align to **canonical source** (usually Def 0.1.1 for geometry, Def 0.0.0 for axioms)
- If multiple conventions exist, adopt the one used by the majority of files
- Document the convention explicitly in the affected file

### For status marker issues:
- Add 🔶 NOVEL where framework-specific content exists
- Add ✅ VERIFIED only when both multi-agent review AND Lean formalization exist
- Follow the status marker rules in CLAUDE.md exactly

### For missing cross-references:
- Add dependency declarations in the proof's Dependencies section
- Verify the referenced theorem actually supports the claim

## Rules

- **Minimal changes**: Fix only the finding — do not refactor surrounding code
- **Canonical sources win**: When two files disagree, the canonical definition is correct
- **Never fabricate physics**: If a fix requires new physics, flag it for human review
- **One finding per commit**: Each fix should be independently revertable
- **Preserve proof structure**: Do not reorganize sections or rename files
