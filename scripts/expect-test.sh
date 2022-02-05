#!/usr/bin/env bash
#
# Usage: $0 $path_to_exe $path_to_mule_file

set -euo pipefail

exe=$1
src_file=$2
out_file=${src_file%.*}.actual
expect_file=${src_file%.*}.expected

cd $(dirname $0)/..
export MULE_ROOT="$PWD/stdlib"
echo "EXPECT TEST: $src_file"

topline="$(head -n 1 < $src_file)"

run_test() (
	$exe eval --debug-steps $src_file > $out_file || true
	diff -u $expect_file $out_file
)

case "$topline" in
	\#SKIP*)
		echo SKIPPED
		exit 0
		;;
	\#XFAIL*)
		if run_test >/dev/null 2>/dev/null; then
			echo "ERROR: Expected test to fail, but it succeded."
			exit 1
		else
			exit 0
		fi
		;;
	*)
		run_test
		;;
esac
