#!/bin/bash
set -eu
R=/opt/domain-public-2026-11-13
C=$R/control
P=$R/project
cd "$P"
export PATH="$C/toolchain/bin:$PATH"
export LEAN_SYSROOT="$C/toolchain" LEAN_NUM_THREADS=1 MATHLIB_NO_CACHE_ON_UPDATE=1
export LAKE_CACHE_DIR="$C/lake-cache" MATHLIB_CACHE_DIR="$C/mathlib-cache" XDG_CACHE_HOME="$C/xdg-cache"
export TMPDIR="$C/tmp" TMP="$C/tmp" TEMP="$C/tmp"
export GIT_CONFIG_GLOBAL="$C/gitconfig" GIT_CONFIG_NOSYSTEM=1 GIT_ALLOW_PROTOCOL=https:file
export COMPARATOR_BWRAP="$C/bwrap-record.sh"
unset LEAN_PATH LEAN_SRC_PATH || true
preflight() {
 local start now mem epoch hostmem disk wl wk
 start=$(date +%s)
 while :; do
  read epoch hostmem disk wl wk < "$C/host-state.txt"
  now=$(date +%s); mem=$(awk '/MemAvailable:/{printf "%.0f",$2*1024}' /proc/meminfo)
  if ! pgrep -a -x lean && ! pgrep -a -x lake && [ "$mem" -ge 8589934592 ] && [ "$hostmem" -ge 8589934592 ] && [ "$disk" -ge 50000000000 ] && [ "$wl" = 0 ] && [ "$wk" = 0 ] && [ "$((now-epoch))" -lt 15 ]; then
   printf 'PASS %s host=%s wsl=%s disk=%s; pgrep lean/lake empty; Windows tasklist empty\n' "$now" "$hostmem" "$mem" "$disk" >> "$C/preflight.txt"; return
  fi
  [ "$((now-start))" -lt 55 ] || return 75
  sleep 1
 done
}
run() {
 local label=$1;shift
 preflight
 printf '%s\tSTART\t%s\t' "$label" "$(date +%s)" >> "$C/commands.tsv"
 printf '%q ' "$@" >> "$C/commands.tsv"; printf '\n' >> "$C/commands.tsv"
 set +e
 "$@" > "$C/$label.txt" 2>&1
 local code=$?
 set -e
 printf '%s\tEND\t%s\t%s\n' "$label" "$(date +%s)" "$code" >> "$C/commands.tsv"
 printf '%s exit=%s\n' "$label" "$code"
 return "$code"
}
ulimit -c 0
find / -mindepth 1 -maxdepth 1 -printf '%f\t%y\n' | LC_ALL=C sort > "$C/root-before-sandbox.txt"
run comparator lake comparator --config comparator.json
find / -mindepth 1 -maxdepth 1 -printf '%f\t%y\n' | LC_ALL=C sort > "$C/root-after-sandbox.txt"
cmp "$C/root-after-cleanup.txt" "$C/root-before-sandbox.txt"
cmp "$C/root-before-sandbox.txt" "$C/root-after-sandbox.txt"
printf 'PASS: no new filesystem-root entries after sandbox\n' > "$C/root-inventory-comparison.txt"
preflight
mapfile -t roots < <(sed -n 's/^    "\(DomainNonembedding\..*\)"[,]\{0,1\}$/\1/p' evidence/session6-release/export-receipt.json | tail -16)
test "${#roots[@]}" = 16
primitives=(Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam)
printf 'export\tSTART\t%s\tlake env leanexport Solution -- [same roots and primitives as session6]\n' "$(date +%s)" >> "$C/commands.tsv"
set +e
lake env "$C/toolchain/bin/leanexport" Solution -- Quot Quot.mk Quot.lift Quot.ind "${roots[@]}" propext Classical.choice Quot.sound "${primitives[@]}" > "$C/Solution.ndjson" 2> "$C/export.txt"
code=$?
set -e
printf 'export\tEND\t%s\t%s\n' "$(date +%s)" "$code" >> "$C/commands.tsv"
[ "$code" = 0 ] || exit "$code"
sha256sum "$C/Solution.ndjson" > "$C/export-sha256.txt"
wc -c "$C/Solution.ndjson" >> "$C/export-sha256.txt"
if [ "$(cut -d' ' -f1 "$C/export-sha256.txt" | head -1)" != 4a5a95d170a5aa6314f1f74635e827275a0ca52cda7ba497e8ea8ae6d366681b ]; then
 run leanchecker "$C/toolchain/bin/leanchecker" --silent --from-export "$C/Solution.ndjson"
 for mode in nanoda negative; do
  axioms='"propext", "Classical.choice", "Quot.sound"'
  [ "$mode" != negative ] || axioms='"propext", "Quot.sound"'
  printf '{"use_stdin":false,"export_file_path":"%s/Solution.ndjson","num_threads":1,"nat_extension":true,"string_extension":true,"permitted_axioms":[%s],"unpermitted_axiom_hard_error":true}\n' "$C" "$axioms" > "$C/$mode.json"
  if [ "$mode" = nanoda ]; then run nanoda "$C/toolchain/bin/nanoda_bin" "$C/$mode.json"; else
   if run negative "$C/toolchain/bin/nanoda_bin" "$C/$mode.json"; then exit 1; else grep -q 'unpermitted axiom' "$C/negative.txt"; fi
  fi
 done
else
 printf 'PASS: byte-identical proof closure; session-6 leanchecker, nanoda, and negative-control receipts carry over.\n' > "$C/kernel-carryover.txt"
fi
find . -type f -not -path '*/.lake/*' -print0 | sort -z | xargs -0 sha256sum > "$C/output-sha256.txt"
cmp "$C/input-sha256.txt" "$C/output-sha256.txt"
printf 'PASS: source tree and manifest unchanged\n' > "$C/source-unchanged.txt"
printf 'ALL-GATES-FINISHED\n'
