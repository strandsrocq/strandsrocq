#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 CPSA_REPOSITORY [OUTPUT.csv]" >&2
  exit 2
fi

cpsa_root="$(cd "$1" && pwd)"
test_dir="$cpsa_root/tst"
output="${2:-/dev/stdout}"

if [[ ! -d "$test_dir" ]]; then
  echo "CPSA test directory not found: $test_dir" >&2
  exit 1
fi

count_lines() {
  local pattern="$1"
  local file="$2"
  local count
  count="$(rg -c "$pattern" "$file" || true)"
  printf '%s' "${count:-0}"
}

has_pattern() {
  local pattern="$1"
  local file="$2"
  if rg -q "$pattern" "$file"; then
    printf 'true'
  else
    printf 'false'
  fi
}

{
  printf '%s\n' \
    'file,suite_expectation,algebras,protocols,skeletons,listeners,opaque_mesg_vars,hash,channels,state,logical_extensions,lexical_class'

  find "$test_dir" -maxdepth 1 -type f \( -name '*.scm' -o -name '*.lsp' \) \
    -print0 | sort -z | while IFS= read -r -d '' file; do
      name="$(basename "$file")"
      extension="${name##*.}"
      if [[ "$extension" == "scm" ]]; then
        expectation='success'
      else
        expectation='failure'
      fi

      algebras="$(sed -n 's/^(defprotocol [^ ]* \([^ )]*\).*/\1/p' "$file" \
        | sort -u | paste -sd+ -)"
      algebras="${algebras:-none}"
      protocols="$(count_lines '\(defprotocol ' "$file")"
      skeletons="$(count_lines '\(defskeleton ' "$file")"
      listeners="$(count_lines '\(deflistener ' "$file")"
      opaque="$(has_pattern '\([^()]*(mesg)\)' "$file")"
      hash="$(has_pattern '\(hash\b' "$file")"
      channels="$(has_pattern '\([^()]*(chan)\)|\((auth|conf)\b' "$file")"
      state="$(has_pattern '\((load|stor|sync)\b' "$file")"
      logic="$(has_pattern '\((defrule|defgenrule|defgoal|facts?)\b' "$file")"

      if [[ "$algebras" == *diffie-hellman* ]]; then
        class='excluded-dh'
      elif [[ "$channels" == true ]]; then
        class='excluded-channel'
      elif [[ "$state" == true ]]; then
        class='excluded-state'
      elif [[ "$opaque" == true ]]; then
        class='needs-opaque-review'
      else
        class='core-candidate'
      fi

      printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
        "tst/$name" "$expectation" "$algebras" "$protocols" "$skeletons" \
        "$listeners" "$opaque" "$hash" "$channels" "$state" "$logic" "$class"
    done
} > "$output"
