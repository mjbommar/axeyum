#!/usr/bin/env bash
export LEAN_CC=/usr/bin/cc STAGE=1 SRC_DIR='/home/mjbommar/.cache/axeyum-tl063-m0-r1-1a2e7d3a/source' TEST_DIR='/home/mjbommar/.cache/axeyum-tl063-m0-r1-1a2e7d3a/source/tests' BUILD_DIR='/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0' SCRIPT_DIR='/home/mjbommar/.cache/axeyum-tl063-m0-r1-1a2e7d3a/source/script' PATH='/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/bin':"$PATH" LEANC_OPTS='-I/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/include' CXX='/usr/bin/c++ -I/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/include'
TEST_LEAN_ARGS=(-j1)
TEST_LEANI_ARGS=(-j1)
source "$TEST_DIR/util.sh"

TEST_SCRIPT="$1"; shift
cd "$(dirname "$TEST_SCRIPT")"
source "$(basename "$TEST_SCRIPT")"
