#!/bin/bash
set -eu
ROOT=/opt/domain-nonembedding-lean/project
cd "$ROOT"
export PATH="$ROOT/.build-control/toolchain/bin:$PATH"
export LEAN_SYSROOT="$ROOT/.build-control/toolchain"
export LAKE_CACHE_DIR="$ROOT/.build-control/lake-cache"
export XDG_CACHE_HOME="$ROOT/.build-control/xdg-cache"
export MATHLIB_NO_CACHE_ON_UPDATE=1
export GIT_CONFIG_GLOBAL="$ROOT/.build-control/gitconfig"
export GIT_CONFIG_NOSYSTEM=1
export GIT_ALLOW_PROTOCOL=file
case "${1:?mode}" in
  update) exec lake --keep-toolchain update ;;
  build)
    # The cache supplies mathlib. Schedule our independent modules sequentially,
    # avoiding transient inherited Lake process names in simultaneous wrappers.
    for module in DomainNonembedding.Hypotheses DomainNonembedding.Permutation \
      DomainNonembedding.DivisionRingRank DomainNonembedding.PermutationAverage \
      DomainNonembedding.PaperData DomainNonembedding.FiniteFieldData \
      FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Incidence \
      DomainNonembedding.Incidence DomainNonembedding.IncidenceBounds \
      DomainNonembedding.MarkedLines DomainNonembedding.DataConstruction \
      DomainNonembedding.Interpolation DomainNonembedding.MatrixAmplification \
      DomainNonembedding.RegularRepresentation DomainNonembedding.RankCertificate \
      DomainNonembedding.LocalRank DomainNonembedding.CollapsedLines \
      DomainNonembedding.LineFree DomainNonembedding.GraphNormalForms \
      DomainNonembedding.Headline DomainNonembedding.ShearNormalForms \
      DomainNonembedding.ShearNonembedding; do
      lake --no-cache build "$module"
    done
    exec lake --no-cache build ;;
  clean-clone) exec python3 -I scripts/clean-clone.py ;;
  release) exec python3 -I scripts/release-check.py "${2:?check}" ;;
  audit) exec lake env lean -j1 -M5000 Audit.lean ;;
  module) exec lake --no-cache build "${2:?module}" ;;
  probe) exec lake env lean -j1 -M5000 "${2:?file}" ;;
  *) exit 64 ;;
esac
