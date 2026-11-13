# Group algebras that are domains but embed in no division ring

Nidhal Mghirbi and Seth Douglas. Version 1.0.0, November 2026.

**This is a preprint. It has not been peer reviewed.**

## Abstract

For every prime p, we construct a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p whose group algebra is a domain over every field and embeds in no division ring over any field of characteristic p. A marked-line complex supplies a universal finite-field rank ceiling. We glue finitely many copies of its group to a free vertex group, using every permutation of a free basis array; a noncommutative permutation-averaging lemma contradicts that ceiling. We prove concentration of the line subgroups by separate geometric cone attachments and a free-product calculation for punctured CAT(0) complexes. Acylindrical combination gives hyperbolicity, and Bowditch's graph-of-groups theorem gives diffuseness. We also give a shorter retractive construction using shear attachments with bi-orderable kernel, together with its general rank-forcing principle. These examples answer Kourovka Problem 1.5 for group algebras over fields of every positive characteristic. The integral and characteristic-zero versions, and Mal'cev's problem, remain open.

## What the paper proves

Theorem letters refer to `paper/main.pdf`.

- **Theorem A (hyperbolic examples).** For every prime p, there is a finitely presented, torsion-free, word-hyperbolic diffuse group Γ_p such that K[Γ_p] is a domain for every field K, and, if char K = p, there is no injective ring homomorphism from K[Γ_p] to any division ring.
- **Theorem B (retractive shear examples).** For every prime p, the base group G_p is a retract of a finitely presented diffuse group Λ_p with the same two properties. The kernel of the retraction is a free product of conjugates of Z^2; it is bi-orderable, so Λ_p is left-orderable if and only if G_p is.
- **Theorem C (general attachment principle).** A unique-product group carrying finitely many marked matrices (each reducible to a bordered matrix whose interior entries freely generate a subgroup) whose total rank under every faithful division-ring representation stays below their total order is a retract of a unique-product group whose group algebra embeds in no division ring. Diffuseness and finite presentability pass to the larger group.

Kourovka Problem 1.5, recorded by L. A. Bokut', asks for a group whose group ring has no zero divisors and does not embed in a skew field. In 2024 Fisher and Klinge noted that no torsion-free group was known whose group algebra fails to embed in a division ring; the torsion-free examples found since then have group algebras with zero divisors or that are not directly finite. Theorem A answers Problem 1.5 for group algebras over fields of every positive characteristic. The integral version, the version over fields of characteristic zero, and Mal'cev's problem (Kourovka Problem 1.6, left-orderable groups) remain open. Section 1 of the paper gives the full credits.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (23 pages).
- `paper/`: the LaTeX source (`main.tex`, `sections/`, `references.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's section "How this work was done" gives the full account. In short: the constructions and proofs were found with OpenAI models (GPT-6 Astra and GPT-6.1 Sol), directed by Nidhal Mghirbi. Claude Opus 5.5 checked the original construction, the extension to every prime and the hyperbolic construction refutation-first, re-deriving each load-bearing step. A semi-blind GPT-6.1 Sol replication proved the main steps of the original construction again, and an independent blind GPT-6.1 Sol replication proved the hyperbolic construction again and supplied the concentration proof. The final text was audited against the cited sources. The results are written proofs; they are not formalized in Lean.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Script (`paper/build.py`): MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
