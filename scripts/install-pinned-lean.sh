#!/usr/bin/env bash
# Install the repository-pinned Lean toolchain without requiring a Lake project.

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 INSTALL_ROOT" >&2
    exit 2
fi

install_root=$1
if [[ -z "$install_root" || "$install_root" == "/" ]]; then
    echo "refusing unsafe install root: ${install_root:-<empty>}" >&2
    exit 2
fi

case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)
        elan_asset=elan-x86_64-unknown-linux-gnu.tar.gz
        elan_sha256=df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2
        ;;
    *)
        echo "unsupported installer platform: $(uname -s)-$(uname -m)" >&2
        exit 2
        ;;
esac

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
toolchain=$(tr -d '[:space:]' < "$repo_root/lean-toolchain")
if [[ ! "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "unexpected lean-toolchain value: $toolchain" >&2
    exit 2
fi

mkdir -p "$install_root"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/axeyum-elan.XXXXXX")
archive=$scratch/$elan_asset
initializer=$scratch/elan-init
cleanup() {
    rm -f -- "$archive" "$initializer"
    rmdir -- "$scratch"
}
trap cleanup EXIT

elan_version=v4.2.3
elan_url="https://github.com/leanprover/elan/releases/download/$elan_version/$elan_asset"
curl --fail --location --silent --show-error --retry 3 \
    "$elan_url" --output "$archive"
printf '%s  %s\n' "$elan_sha256" "$archive" | sha256sum --check --status
tar -xzf "$archive" -C "$scratch" elan-init

export ELAN_HOME="$install_root/elan-home"
"$initializer" -y --default-toolchain none --no-modify-path
if ! "$ELAN_HOME/bin/elan" toolchain list | grep -Fxq "$toolchain"; then
    "$ELAN_HOME/bin/elan" toolchain install "$toolchain"
fi

lean_version=$("$ELAN_HOME/bin/lean" --version)
printf 'LEAN_INSTALL|elan=%s|elan_sha256=%s|toolchain=%s|lean=%s\n' \
    "$elan_version" "$elan_sha256" "$toolchain" "$lean_version"
