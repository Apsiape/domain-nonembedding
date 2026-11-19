Group algebras that are domains but embed in no division ring
Nidhal Mghirbi and Seth Douglas
Version 2.0.0, November 2026

This version adds a common word to Theorems A and B (one nonidentity element
that every homomorphism to the units of a division ring of characteristic p
sends to 1); Section 8, "One central element in every positive characteristic"
(Theorem D and its central-localization corollary); the orderability test of
Proposition 7.2; and Appendix B (a computable finite-prime bound for deficient
shear factorizations). The text is now a single source file.

Build: python -I -B build.py --build-dir NEW_OR_EMPTY_DIRECTORY
Requires Python 3 and pdflatex with the packages loaded by main.tex. main.tex is
the complete source, bibliography included. The build runs pdflatex three times
without shell escape and rejects warnings, unresolved references and overfull or
underfull boxes. main.pdf is the compiled preprint (25 pages); abstract.txt is the
abstract as plain text.

The Lean 4 development in lean/ beside paper/ is unchanged from version 1.1.0.
Use the pinned Lean v4.35.0 toolchain and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679. From lean/, run lake exe cache get,
then lake build. Appendix A describes what it verifies.

No publication or submission is performed by the build.
