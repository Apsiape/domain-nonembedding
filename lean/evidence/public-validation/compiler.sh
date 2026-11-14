#!/bin/bash
set -eu
R=/opt/domain-public-2026-11-13
C=$R/control
exec 9>>"$C/compile.lock"
flock -x 9
start=$(date +%s)
while :; do
 read epoch hostmem disk winlean winlake < "$C/host-state.txt"
 mem=$(awk '/MemAvailable:/{printf "%.0f",$2*1024}' /proc/meminfo)
 now=$(date +%s)
 lean=$(pgrep -a -x lean || true)
 lake=$(pgrep -a -x lake || true)
 ancestors=" "
 pid=$$
 while [ "$pid" -gt 1 ]; do ancestors="$ancestors$pid "; pid=$(awk '/PPid:/{print $2}' /proc/$pid/status); done
 foreign=0
 for pid in $(pgrep -x lake || true); do case "$ancestors" in *" $pid "*) ;; *) foreign=1;; esac; done
 if [ "$((now-epoch))" -lt 15 ] && [ "$hostmem" -ge 8589934592 ] && [ "$mem" -ge 8589934592 ] && [ "$disk" -ge 50000000000 ] && [ "$winlean" = 0 ] && [ "$winlake" = 0 ] && [ -z "$lean" ] && [ "$foreign" = 0 ]; then break; fi
 if [ "$((now-start))" -ge 55 ]; then printf 'GATE CLOSED epoch=%s host=%s wsl=%s disk=%s lean=%s lake=%s\n' "$epoch" "$hostmem" "$mem" "$disk" "$lean" "$lake" >> "$C/compile-gates.txt"; exit 75; fi
 sleep 1
done
printf 'ALLOW epoch=%s host=%s wsl=%s disk=%s WindowsLean=%s WindowsLake=%s pgrep-lean=%q pgrep-lake=%q args=' "$now" "$hostmem" "$mem" "$disk" "$winlean" "$winlake" "$lean" "$lake" >> "$C/compile-gates.txt"
printf '%q ' "$@" >> "$C/compile-gates.txt"
printf '\n' >> "$C/compile-gates.txt"
/opt/forgetting-arxiv-2026-11-10/toolchain/bin/lean -j1 -M5000 "$@" &
child=$!
set +e
wait "$child"
code=$?
set -e
printf 'END epoch=%s pid=%s exit=%s\n' "$(date +%s)" "$child" "$code" >> "$C/compile-gates.txt"
exit "$code"
