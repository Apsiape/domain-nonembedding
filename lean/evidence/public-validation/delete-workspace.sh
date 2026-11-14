#!/bin/bash
set -eu
R=/opt/domain-public-2026-11-13
[ "$(readlink -f "$R")" = /opt/domain-public-2026-11-13 ]
[ -d "$R" ] && [ ! -L "$R" ]
if pgrep -a -x lean; then exit 75; fi
if pgrep -a -x lake; then exit 75; fi
printf 'PASS: no Lean or Lake processes before workspace deletion.\n'
root_before=$(cat "$R/control/root-after-sandbox.txt")
printf 'Verified exact absolute deletion target: %s (not a symlink).\n' "$R"
printf 'Deleting only that owned tree with find -P -depth -delete; no recursive rm.\n'
find -P "$R" -depth -delete
[ ! -e "$R" ]
printf 'PASS: authorized WSL workspace deleted.\n'
root_after=$(find / -mindepth 1 -maxdepth 1 -printf '%f\t%y\n' | LC_ALL=C sort)
[ "$root_before" = "$root_after" ]
printf 'PASS: filesystem-root inventory still unchanged.\n'
if pgrep -a -x lean; then exit 75; fi
if pgrep -a -x lake; then exit 75; fi
printf 'PASS: no Lean or Lake processes remain.\n'
