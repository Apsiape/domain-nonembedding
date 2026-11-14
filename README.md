# Group algebras that are domains but embed in no division ring

Nidhal Mghirbi and Seth Douglas. Version 1.1.0, November 2026. DOI for all versions: [10.5281/zenodo.24202768](https://doi.org/10.5281/zenodo.24202768); version 1.0.0: [10.5281/zenodo.24202769](https://doi.org/10.5281/zenodo.24202769).

**This is a preprint. It has not been peer reviewed.**

## Abstract

For every prime p, we construct a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p whose group algebra is a domain over every field and embeds in no division ring over any field of characteristic p. A marked-line complex supplies a universal finite-field rank ceiling. We glue finitely many copies of its group to a free vertex group, using every permutation of a free basis array; a noncommutative permutation-averaging lemma contradicts that ceiling. We prove concentration of the line subgroups by separate geometric cone attachments and a free-product calculation for punctured CAT(0) complexes. Acylindrical combination gives hyperbolicity, and Bowditch's graph-of-groups theorem gives diffuseness. We also give a shorter retractive construction using shear attachments with bi-orderable kernel, together with its general rank-forcing principle. These examples answer Kourovka Problem 1.5 for group algebras over fields of every positive characteristic. The integral and characteristic-zero versions, and Mal'cev's problem, remain open. The nonembedding clauses of both constructions are formally verified in Lean 4.

## What the paper proves

Theorem letters refer to `paper/main.pdf`.

- **Theorem A (hyperbolic examples).** For every prime p, there is a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p such that K[Γ_p] is a domain for every field K, and, if char K = p, there is no injective ring homomorphism from K[Γ_p] to any division ring.
- **Theorem B (retractive shear examples).** For every prime p, the base group G_p is a retract of a finitely presented diffuse group Λ_p with the same two properties. The kernel of the retraction is a free product of conjugates of Z^2; it is bi-orderable, so Λ_p is left-orderable if and only if G_p is.
- **Theorem C (general attachment principle).** A unique-product group carrying finitely many marked matrices (each reducible to a bordered matrix whose interior entries freely generate a subgroup) whose total rank under every faithful division-ring representation stays below their total order is a retract of a unique-product group whose group algebra embeds in no division ring. Diffuseness and finite presentability pass to the larger group.

Kourovka Problem 1.5, recorded by L. A. Bokut', asks for a group whose group ring has no zero divisors and does not embed in a skew field. In 2024 Fisher and Klinge noted that no torsion-free group was known whose group algebra fails to embed in a division ring; the torsion-free examples found since then have group algebras with zero divisors or that are not directly finite. Theorem A answers Problem 1.5 for group algebras over fields of every positive characteristic. The integral version, the version over fields of characteristic zero, and Mal'cev's problem (Kourovka Problem 1.6, left-orderable groups) remain open. Section 1 of the paper gives the full credits.

## Changes in 1.1.0

The nonembedding clauses of Theorems A and B are now formally verified in Lean 4 (folder `lean/`, described in the paper's new appendix). The mathematical statements and proofs in the text are unchanged.

## Lean verification

For every prime p, Lean proves that admissible marked-line data exist and that, for every admissible datum and every field K of characteristic p, no ring homomorphism from the group algebra of the permutation-glued group, or of the shear group, to a division ring is injective. The paper's datum is admissible, and for it these groups are the groups Γ_p and Λ_p of Theorems A and B (the paper's appendix gives the comparison of presentations). Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used. The checks: the default build, a full axiom audit of every declaration, a sandboxed `lake comparator` run against a Mathlib-only statement file, replay of the exported proofs by two independent kernels (`leanchecker` and `nanoda`) with a negative control, and a fresh-clone build. The shipped `lean/` folder passed the build, audit, comparator and lint again from a clean copy, with an identical declaration list, axiom record and proof export. Not formalized: hyperbolicity, diffuseness, the domain property, finite presentability, torsion-freeness, the shear retraction and its kernel, orderability, characteristic zero, and Theorem C in full. `lean/README.md` gives the commands; `lean/REPORT.md` and `lean/SCOPE.md` give the full record and scope.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (25 pages).
- `paper/`: the LaTeX source (`main.tex`, `sections/`, `references.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `lean/`: the Lean 4 package (Lean v4.35.0, Mathlib pinned by commit). From `lean/`, run `lake exe cache get` and then `lake build`; see `lean/README.md`.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's section "How this work was done" gives the full account. In short: the constructions and proofs were found with OpenAI models (GPT-6 Astra and GPT-6.1 Sol), directed by Nidhal Mghirbi. Claude Opus 5.5 checked the original construction, the extension to every prime and the hyperbolic construction refutation-first, re-deriving each load-bearing step. A semi-blind GPT-6.1 Sol replication proved the main steps of the original construction again, and an independent blind GPT-6.1 Sol replication proved the hyperbolic construction again and supplied the concentration proof. The final text was audited against the cited sources. The Lean development was written by GPT-6.1 Sol agents in Codesk sessions, directed by the authors; its statements were frozen after an independent blind fidelity read found them faithful to the paper, before the proofs were written. The written proofs remain the primary record; Lean verifies the nonembedding clauses only.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Build script (`paper/build.py`) and Lean sources (`lean/`): MIT or Apache 2.0, at your option; `lean/deps/nonsofic/` keeps its own licence files. See `RIGHTS.md`, the license files and `NOTICE`.
