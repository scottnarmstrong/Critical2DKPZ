#!/usr/bin/env bash
# Run leanprover/comparator on Critical2DKPZAudit/comparator.json, including NanoDa.
# Verification script, released under Apache-2.0.
# Usage: scripts/verify_comparator.sh
#
# Environment:
#   COMPARATOR_BIN, COMPARATOR_LEAN4EXPORT  existing toolchain-compatible binaries (otherwise the
#                                           pinned commits below are cloned and built in the cache)
#   COMPARATOR_LANDRUN, COMPARATOR_NANODA   landrun and nanoda_bin (default: found in PATH)
#   KPZ_COMPARATOR_CACHE                    tool cache (default: ~/.cache/critical2dkpz-comparator)
#   COMPARATOR_BUILD_LOCK                   optional lock file; the prebuild then runs under flock
#   LEAN_NUM_THREADS                        threads for the prebuild and the comparator (default 2)
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/verify_comparator.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/.." && pwd)
config=Critical2DKPZAudit/comparator.json
cache=${KPZ_COMPARATOR_CACHE:-"$HOME/.cache/critical2dkpz-comparator"}
comparator_commit=32bd61da1d68fbaa310234964e9b820b03a0f82f
lean4export_commit=6cea97789dc088ea47fcea15692db85685aedac5

cd "$root"
[ -f "$config" ] || { echo "error: $config not found" >&2; exit 1; }
landrun=${COMPARATOR_LANDRUN:-$(command -v landrun || true)}
nanoda=${COMPARATOR_NANODA:-$(command -v nanoda_bin || true)}
[ -n "$landrun" ] && [ -x "$landrun" ] || {
  echo "error: landrun is missing; put landrun on PATH or set COMPARATOR_LANDRUN" >&2; exit 1;
}
[ -n "$nanoda" ] && [ -x "$nanoda" ] || {
  echo "error: nanoda_bin is missing; put nanoda_bin on PATH or set COMPARATOR_NANODA" >&2; exit 1;
}
python3 -I -c '
import json,sys
c=json.load(open(sys.argv[1]))
if c.get("enable_nanoda") is not True:
    sys.exit("error: comparator.json must set enable_nanoda to true")
' "$config"

# Use pinned builds: globally installed exporters may use another .olean format.
# Explicit overrides may point to existing toolchain-compatible binaries.
comparator=${COMPARATOR_BIN:-"$cache/comparator/.lake/build/bin/comparator"}
lean4export=${COMPARATOR_LEAN4EXPORT:-"$cache/lean4export/.lake/build/bin/lean4export"}
checkout_tool() {
  local name=$1 commit=$2
  mkdir -p "$cache"
  [ -d "$cache/$name/.git" ] || git clone -q --filter=blob:none \
    "https://github.com/leanprover/$name.git" "$cache/$name"
  if [ "$(git -C "$cache/$name" rev-parse HEAD)" != "$commit" ]; then
    git -C "$cache/$name" fetch -q --depth 1 origin "$commit"
    git -C "$cache/$name" checkout -q --detach "$commit"
  fi
  [ "$(tr -d '[:space:]' < "$cache/$name/lean-toolchain")" = \
    "$(tr -d '[:space:]' < "$root/lean-toolchain")" ] || {
    echo "error: $name toolchain differs from the project's" >&2; exit 1;
  }
  [ -x "$cache/$name/.lake/build/bin/$name" ] || \
    (cd "$cache/$name" && LEAN_NUM_THREADS=2 nice -n 10 lake build "$name")
}
if [ -z "${COMPARATOR_BIN:-}" ]; then
  checkout_tool comparator "$comparator_commit"
  comparator="$cache/comparator/.lake/build/bin/comparator"
fi
if [ -z "${COMPARATOR_LEAN4EXPORT:-}" ]; then
  checkout_tool lean4export "$lean4export_commit"
  lean4export="$cache/lean4export/.lake/build/bin/lean4export"
fi
for tool in "$comparator" "$lean4export" "$landrun" "$nanoda"; do
  [ -n "$tool" ] && [ -x "$tool" ] || {
    echo "error: verification tool is not executable: $tool" >&2
    exit 1
  }
done

cd "$root"
[ -f "$config" ] || { echo "error: $config not found" >&2; exit 1; }

mapfile -t modules < <(python3 -I -c \
  'import json,sys; c=json.load(open(sys.argv[1])); print(c["challenge_module"]); print(c["solution_module"])' \
  "$config")
[ ${#modules[@]} -eq 2 ] || { echo "error: invalid comparator config" >&2; exit 1; }
# Discard only this audit library's artifacts so both environments are freshly built.
rm -rf "$root/.lake/build/lib/lean/Critical2DKPZAudit" "$root/.lake/build/ir/Critical2DKPZAudit"
rm -f "$root"/.lake/build/lib/lean/Critical2DKPZAudit.* "$root"/.lake/build/ir/Critical2DKPZAudit.*
echo "=== comparator: Critical2DKPZAudit"
# Prebuild with bounded parallelism (this also builds the library if it is not yet built);
# comparator's sandboxed builds then find warm artifacts.
prebuild=(lake build "${modules[@]}")
if [ -n "${COMPARATOR_BUILD_LOCK:-}" ]; then
  prebuild=(flock "$COMPARATOR_BUILD_LOCK" "${prebuild[@]}")
fi
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} nice -n 10 "${prebuild[@]}" < /dev/null || {
  echo "=== Critical2DKPZAudit: FAIL (build)"; exit 1;
}
if COMPARATOR_LEAN4EXPORT="$lean4export" COMPARATOR_NANODA="$nanoda" \
  COMPARATOR_LANDRUN="$landrun" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} \
  nice -n 10 lake env "$comparator" "$config"; then
  echo "=== Critical2DKPZAudit: PASS"
else
  echo "=== Critical2DKPZAudit: FAIL"; exit 1
fi
