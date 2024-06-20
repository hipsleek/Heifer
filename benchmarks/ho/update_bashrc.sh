#!/usr/bin/env bash

cat << EOF >> ~/.bashrc
echo "[Artifact of FM #28: Heifer]"
echo "To reproduce the paper's experiments, run benchmarks/ho/experiments.py"
echo "Further details may be found in README.md (vim and nano are pre-installed)."
EOF
