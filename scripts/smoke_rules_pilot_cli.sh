#!/usr/bin/env bash
set -euo pipefail

# CLI-based smoke for pilot rules, does not require REST or service.
# Requires dune build of validators_cli.

GOLDEN=specs/rules/pilot_v1_golden.yaml
CLI=_build/default/latex-parse/src/validators_cli.exe

if [[ ! -x "$CLI" ]]; then
  echo "[cli-smoke] Building validators_cli..." >&2
  OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build latex-parse/src/validators_cli.exe
fi

export L0_VALIDATORS=${L0_VALIDATORS:-pilot}

pass=0; fail=0

# Parse YAML cases into records: file|expect_ids|forbid_ids|expect_msgs
while IFS='|' read -r file expect forbid emsgs; do
  [[ -z "$file" ]] && continue
  if [[ ! -f "$file" ]]; then
    echo "[cli-smoke] MISSING: $file"; fail=$((fail+1)); continue
  fi

  out=$("$CLI" "$file")
  ids=$(echo "$out" | awk '$1!~"^#"{print $1}')
  id_msg_pairs=$(echo "$out" | awk '$1!~"^#"{id=$1; $1=""; $2=""; $3=""; sub(/^  */,"",$0); print id"\t"$0}')

  ok=1
  for id in $expect; do
    if ! echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done
  for id in $forbid; do
    if echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done

  if [[ -n "${emsgs:-}" ]]; then
    while IFS= read -r pair; do
      [[ -z "$pair" ]] && continue
      idexp=${pair%%:*}
      msgexp=${pair#*:}
      if ! echo "$id_msg_pairs" | awk -F '\t' -v id="$idexp" -v msg="$msgexp" '($1==id && $2==msg){found=1} END{exit(found?0:1)}'; then
        ok=0
      fi
    done <<< "$(printf "%s" "$emsgs" | tr '\\;' '\n')"
  fi

  if [[ $ok -eq 1 ]]; then
    echo "[cli-smoke] PASS: $file -> expect:[$expect] forbid:[$forbid] messages:[$(echo "$emsgs" | tr '\n' ';')]"
    pass=$((pass+1))
  else
    echo "[cli-smoke] FAIL: $file expected:[$expect] forbid:[$forbid] messages:[$(echo "$emsgs" | tr '\n' ';')] got: $(echo "$ids" | tr '\n' ' ')" >&2
    fail=$((fail+1))
  fi
done < <(
  awk '
    BEGIN { file=""; expect=""; forbid=""; emsgs="" }
    /^[[:space:]]*-[[:space:]]*file:/ {
      if (file!="") { print file "|" expect "|" forbid "|" emsgs; expect=""; forbid=""; emsgs="" }
      sub(/^[[:space:]]*-[[:space:]]*file:[[:space:]]*/,""); file=$0
    }
    /^[[:space:]]*expect:/ {
      s=$0; sub(/^[[:space:]]*expect:[[:space:]]*\[/, "", s); sub(/\][[:space:]]*$/, "", s);
      gsub(/"|,/, "", s); gsub(/^[[:space:]]+|[[:space:]]+$/, "", s);
      expect=s
    }
    /^[[:space:]]*forbid:/ {
      s=$0; sub(/^[[:space:]]*forbid:[[:space:]]*\[/, "", s); sub(/\][[:space:]]*$/, "", s);
      gsub(/"|,/, "", s); gsub(/^[[:space:]]+|[[:space:]]+$/, "", s);
      forbid=s
    }
    /^[[:space:]]*expect_msgs:/, /^[[:space:]]*[^ ]/ {
      if ($0 ~ /^[[:space:]]*expect_msgs:/) { inmsgs=1; next }
      if (inmsgs==1) {
        if ($0 ~ /^[[:space:]]*-/) {
          line=$0; sub(/^[[:space:]]*-[[:space:]]*/, "", line); gsub(/^\"|\"$/, "", line);
          if (emsgs!="") emsgs=emsgs ";" line; else emsgs=line
          next
        } else if ($0 ~ /^[[:space:]]*$/) { next } else { inmsgs=0 }
      }
    }
    END { if (file!="") print file "|" expect "|" forbid "|" emsgs }
  ' "$GOLDEN"
)

echo "[cli-smoke] Summary: pass=$pass fail=$fail"
[[ $fail -eq 0 ]]
