#!/bin/bash
set -eu
C=/opt/domain-public-2026-11-13/control
REAL=/opt/forgetting-arxiv-2026-11-10/toolchain
mkdir -p "$C/toolchain/bin" "$C/lake-cache" "$C/mathlib-cache" "$C/xdg-cache" "$C/tmp"
touch "$C/gitconfig" "$C/compile.lock" "$C/compile-gates.txt"
for part in lib src include share; do test ! -e "$REAL/$part" || ln -s "$REAL/$part" "$C/toolchain/$part"; done
for bin in "$REAL"/bin/*; do
 case "${bin##*/}" in
 lean) ;;
 lake|leanexport|leanchecker|nanoda_bin) cp "$bin" "$C/toolchain/bin/" ;;
 *) ln -s "$bin" "$C/toolchain/bin/" ;;
 esac
done
cat > "$C/toolchain/bin/lean" <<'EOF'
#!/bin/sh
exec /bin/bash /opt/domain-public-2026-11-13/control/compiler.sh "$@"
EOF
chmod +x "$C/toolchain/bin/lean" "$C/bwrap-record.sh"
sha256sum "$C/toolchain/bin/lake" "$C/toolchain/bin/leanexport" "$C/toolchain/bin/leanchecker" "$C/toolchain/bin/nanoda_bin" > "$C/tool-binaries-sha256.txt"
bash -n "$C/compiler.sh" "$C/bwrap-record.sh" "$C/run.sh"
