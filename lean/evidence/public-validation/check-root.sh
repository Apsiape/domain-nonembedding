#!/bin/bash
set -eu
C=/opt/domain-public-2026-11-13/control
find / -mindepth 1 -maxdepth 1 -printf '%f\t%y\n' | LC_ALL=C sort > "$C/root-after-sandbox-attempt1.txt"
cmp "$C/root-before-sandbox.txt" "$C/root-after-sandbox-attempt1.txt"
printf 'PASS: no new filesystem-root entries after the first sandboxed comparator attempt (exit 1).\n' > "$C/root-inventory-attempt1.txt"
pgrep -a lean || true
pgrep -a lake || true
