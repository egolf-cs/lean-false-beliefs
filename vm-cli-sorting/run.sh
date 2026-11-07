#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
exec ./build/qemu-cli/run.sh "$@"
