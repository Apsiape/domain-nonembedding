#!/bin/bash
set -eu
C=/opt/domain-public-2026-11-13/control
exec > "$C/authorized-cleanup.txt" 2>&1
for dir in /toolchain/bin /toolchain /lake-cache /mathlib-cache /xdg-cache; do
 test -d "$dir" && test ! -L "$dir"
 printf 'Checking %s: ' "$dir"
 if [ -n "$(find "$dir" -mindepth 1 -maxdepth 1 -print -quit)" ]; then printf 'NOT EMPTY; stopped\n'; exit 1; fi
 printf 'empty; '
 rmdir -- "$dir"
 printf 'rmdir exit=0\n'
done
for file in /gitconfig /compile.lock /compile-gates.txt; do
 test -f "$file" && test ! -L "$file"
 size=$(stat -c %s "$file")
 printf 'Checking %s: %s bytes; ' "$file" "$size"
 test "$size" = 0
 unlink -- "$file"
 printf 'unlink exit=0\n'
done
find / -mindepth 1 -maxdepth 1 -printf '%f\t%y\n' | LC_ALL=C sort > "$C/root-after-cleanup.txt"
printf 'All explicitly authorized empty paths removed. No recursive deletion used.\n'
