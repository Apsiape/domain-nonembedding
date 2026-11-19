# Group algebras that are domains but embed in no division ring

Nidhal Mghirbi and Seth Douglas. Version 2.0.0, November 2026. DOI for all versions: [10.5281/zenodo.24202768](https://doi.org/10.5281/zenodo.24202768); version 2.0.0: [10.5281/zenodo.24381987](https://doi.org/10.5281/zenodo.24381987); version 1.1.0: [10.5281/zenodo.24211329](https://doi.org/10.5281/zenodo.24211329); version 1.0.0: [10.5281/zenodo.24202769](https://doi.org/10.5281/zenodo.24202769).

**This is a preprint. It has not been peer reviewed.**

## Abstract

We answer Problem 1.5 of the Kourovka Notebook for group algebras over fields of every positive characteristic. For each prime p we construct a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p. Its group algebra is a domain over every field. There is a nonidentity element w_p that every homomorphism from Γ_p to the units of a division ring of characteristic p sends to 1. The obstruction comes from matrices. Finite-field interpolation bounds their total rank from above, while averaging over permutations of free generators gives a contradictory lower bound if certain group elements remain distinct. A second construction gives a retraction and allows us to combine the obstructions for different primes. In one three-generated diffuse group, a single central element of infinite order dies in every division ring of positive characteristic and in every finite-dimensional linear representation over a field. Lean 4 verifies the nonembedding conclusions for the two prime-specific group algebras.

## What the paper proves

Theorem letters refer to `paper/main.pdf`.

- **Theorem A (hyperbolic examples).** For every prime p, there is a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p such that K[Γ_p] is a domain for every field K; if char K = p, there is no injective ring homomorphism from K[Γ_p] to any division ring; and a single element w_p ≠ 1 is sent to 1 by every homomorphism from Γ_p to the units of a division ring of characteristic p.
- **Theorem B (retractive examples).** For every prime p, the base group G_p is a retract of a finitely presented diffuse group Λ_p with the corresponding properties, including a common word. The kernel of the retraction is a free product of conjugates of Z^2; it is bi-orderable, so Λ_p is left-orderable if and only if G_p is.
- **Theorem C (general attachment principle).** A unique-product group carrying finitely many marked matrices (each reducible to a bordered matrix whose interior entries freely generate a subgroup) whose total rank under every faithful division-ring representation stays below their total order is a retract of a unique-product group whose group algebra embeds in no division ring. Diffuseness and finite presentability pass to the larger group.
- **Theorem D (one central element for every prime).** There is a three-generated diffuse group E with a central element z of infinite order that is sent to 1 by every homomorphism from E to the units of a division ring of positive characteristic, and by every finite-dimensional linear representation of E over any field. Consequently, for every field K of positive characteristic, the central localization K[E][(z−1)^(−1)] is a nonzero domain with no unital homomorphism to a division ring. Domains with no such homomorphism were known earlier (Leavitt; Cohn); the point here is a group algebra and its central localization, uniformly in the characteristic.

Kourovka Problem 1.5, recorded by L. A. Bokut', asks for a group whose group ring has no zero divisors and does not embed in a skew field. Theorem A answers Problem 1.5 for group algebras over fields of every positive characteristic. The integral version, the version over fields of characteristic zero (including whether a division ring of characteristic zero can detect z), and Mal'cev's problem (Kourovka Problem 1.6, left-orderable groups) remain open. Section 1 of the paper gives the full credits.

## Changes in 2.0.0

- Theorems A and B gain a common word: one nonidentity element killed by every homomorphism to the units of a division ring of characteristic p.
- New Section 8 with Theorem D and its central-localization corollary.
- New orderability test (Proposition 7.2) and Appendix B, a computable finite-prime bound for deficient shear factorizations of fixed size and support.
- The text is a single LaTeX source. The Lean development is unchanged; the `lean/` folder now carries only the sources, pins, axiom record and checking files (the full check records of version 1.1.0 stay archived with that release).

## Lean verification

For every prime p, Lean proves that admissible marked-line data exist and that, for every admissible datum and every field K of characteristic p, no ring homomorphism from the group algebra of the permutation-glued group, or of the shear group, to a division ring is injective. The paper's datum is admissible, and for it these groups are the groups Γ_p and Λ_p of Theorems A and B (Appendix A gives the comparison of presentations). Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used. For version 1.1.0 the development passed the default build, a full axiom audit of every declaration, a sandboxed `lake comparator` run against a Mathlib-only statement file, replay of the exported proofs by two independent kernels (`leanchecker` and `nanoda`) with a negative control, and a fresh-clone build. Not formalized: hyperbolicity, diffuseness, the domain property, finite presentability, torsion-freeness, the shear retraction and its kernel, orderability, characteristic zero, the common words, Theorem C in full, and Theorem D. `lean/README.md` gives the commands.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (25 pages).
- `paper/`: the LaTeX source (`main.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `lean/`: the Lean 4 package (Lean v4.35.0, Mathlib pinned by commit). From `lean/`, run `lake exe cache get` and then `lake build`; see `lean/README.md`.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The first page of the paper names the models that assisted with this work. Each headline proof was checked refutation-first by models from two developers, with every imported statement compared against its source; the nonembedding clauses of Theorems A and B are verified in Lean 4. The written proofs remain the primary record.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Build script (`paper/build.py`) and Lean sources (`lean/`): MIT or Apache 2.0, at your option; `lean/deps/nonsofic/` keeps its own licence files. See `RIGHTS.md`, the license files and `NOTICE`.
