#!/bin/bash
set -eu
R=/opt/domain-public-2026-11-13
C=$R/control
args=()
while [ "$#" -gt 0 ]; do
 case "$1" in
 --share-net) shift ;;
 --dir)
  if [ "$2" = /tmp/home ]; then shift 2; else args+=("$1" "$2"); shift 2; fi ;;
 --setenv)
  if [ "$2" = HOME ] && [ "$3" = /tmp/home ]; then args+=("$1" "$2" "$C/sandbox/home"); shift 3
  else args+=("$1" "$2" "$3"); shift 3; fi ;;
 *) args+=("$1"); shift ;;
 esac
done
# Existing system masks and /dev,/proc mounts create no new host paths.
# Every added writable host mount point, temporary directory, and cache is local.
extra=(--tmpfs "$C/sandbox" --dir "$C/sandbox/home" --dir "$C/sandbox/tmp" --dir "$C/sandbox/lake-cache" --setenv TMPDIR "$C/sandbox/tmp" --setenv TMP "$C/sandbox/tmp" --setenv TEMP "$C/sandbox/tmp" --setenv LEAN_NUM_THREADS 1 --setenv MATHLIB_NO_CACHE_ON_UPDATE 1 --setenv GIT_ALLOW_PROTOCOL file --setenv LAKE_CACHE_DIR "$C/sandbox/lake-cache" --setenv LEAN_SYSROOT "$C/toolchain" --bind "$C/compile.lock" "$C/compile.lock" --bind "$C/compile-gates.txt" "$C/compile-gates.txt")
final=()
injected=0
for arg in "${args[@]}"; do
 if [ "$arg" = -- ] && [ "$injected" = 0 ]; then final+=("${extra[@]}"); injected=1; fi
 final+=("$arg")
done
printf 'NETWORK_DISABLED supplied_exports=false epoch=%s ' "$(date +%s)" >> "$C/bwrap-invocations.txt"
printf '%q ' "${final[@]}" >> "$C/bwrap-invocations.txt"
printf '\n' >> "$C/bwrap-invocations.txt"
exec /opt/forgetting-arxiv-2026-11-10/bubblewrap/usr/bin/bwrap "${final[@]}"
