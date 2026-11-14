Group algebras that are domains but embed in no division ring
Nidhal Mghirbi and Seth Douglas
Version 1.1.0, November 2026

This release adds Appendix A, "Lean formalization", and the corresponding
abstract, introduction, account of the work and version note. It changes no
mathematical statement or proof in the text. The appendix records the Lean 4
verification of the nonembedding clauses of Theorems A and B, its precise scope,
the presentation comparison, checks and reproduction procedure.

Build: python -I -B build.py --build-dir NEW_OR_EMPTY_DIRECTORY
Requires Python 3 and pdflatex with the packages loaded by main.tex. The
bibliography is in references.tex. The build runs pdflatex three times without
shell escape and rejects warnings, unresolved references and overfull or
underfull boxes. main.pdf is the compiled preprint (25 pages); abstract.txt is the abstract
as plain text. main.tex includes the sections in sections/, then the new appendix
after the conclusion and before references.tex.

The release repository supplies the formalization as lean/ beside paper/.
Use the pinned Lean v4.35.0 toolchain and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679. From lean/, run lake exe cache get,
then lake build. Its README.md describes the separate audits, comparator and
kernel replays. The checks and their results are described in Appendix A. This
paper is released at tag v1.1.0 of its release repository.

No publication or submission is performed by the build.
