#!/usr/bin/env bash
#
# Usage: $0 $path_to_exe $path_to_mule_file

set -euo pipefail
exe=$1
src_file=$2

cd $(dirname $0)/..
export MULE_ROOT="$PWD/stdlib"
echo "CHECK STDLIB: $src_file"
$exe eval $src_file > /dev/null
