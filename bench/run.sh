#!/bin/sh
set -eu

bench_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
export LEAN_ABORT_ON_PANIC=1
(cd "$bench_dir" && lake build characteristic_bench)
exec "$bench_dir/.lake/build/bin/characteristic_bench" "$@"
