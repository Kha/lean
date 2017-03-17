#!/usr/bin/env bash
if [ $# -ne 1 ]; then
    echo "Usage: test_all.sh [lean-executable-path]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../../library:.
if "$LEAN" *.lean; then
    touch all
fi
