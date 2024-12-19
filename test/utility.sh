
check() {
  TEST=1 hip "$1" 2>&1
}

sanitize() {
  grep Time
}

output() {
  hip "$1" 2>&1 | sanitize
}

check_why3_only() {
  if [ "$PROVER" = "WHY3" ]; then
    check "$1"
  else
    echo "ALL OK!"
  fi
}