#!/usr/bin/env bash
set -euo pipefail

# Validate that runtime messages match catalogue descriptions exactly.
# Extracts all rule IDs from validators.ml and checks against rules_v3.yaml.

CATALOG=specs/rules/rules_v3.yaml
# Pre-v26.0 the rule definitions all lived in latex-parse/src/validators.ml.
# v26.0 split them across validators_l0.ml, validators_l1.ml, ...; the
# top-level validators.ml is now a dispatcher with `include Validators_*`
# clauses, so a script that only reads validators.ml sees ~8 rules
# instead of the 600+ that ship at runtime. Scan the full glob.
RUNTIME_GLOB=(latex-parse/src/validators*.ml)

if [[ ! -f "$CATALOG" ]]; then
  echo "[msg] ERROR: missing catalogue: $CATALOG" >&2
  exit 2
fi
if [[ ${#RUNTIME_GLOB[@]} -eq 0 || ! -f "${RUNTIME_GLOB[0]}" ]]; then
  echo "[msg] ERROR: no runtime sources matched latex-parse/src/validators*.ml" >&2
  exit 2
fi

# Build a mapping of id -> expected runtime message.
# v26.3.1+: prefer the optional [runtime_message] field over
# [description] when both are present. The two-field design keeps
# [description] as abstract human-readable docs while letting
# [runtime_message] carry the exact runtime template (including %s
# placeholders) for strict validation. See
# scripts/tools/sync_runtime_messages.py.
declare -A catalog_descs
cur_id=""
while IFS= read -r line; do
  # Match: - id: "XXX"
  if [[ "$line" =~ ^-[[:space:]]+id:[[:space:]]*\"([^\"]+)\" ]]; then
    cur_id="${BASH_REMATCH[1]}"
  fi
  # Match:   description: "..." or '...' — only used as fallback
  # when [runtime_message] is absent.
  if [[ -n "$cur_id" && "$line" =~ ^[[:space:]]+description:[[:space:]]*\"(.*)\"$ ]]; then
    desc="${BASH_REMATCH[1]}"
    # YAML double-quoted scalar escapes: decode \\ \xHH \NNN \n \t \r
    # via printf %b. \" must be decoded explicitly (printf %b doesn't
    # touch it).
    desc=$(printf '%b' "$desc")
    desc="${desc//\\\"/\"}"
    if [[ -z "${catalog_descs[$cur_id]:-}" ]]; then
      catalog_descs["$cur_id"]="$desc"
    fi
  fi
  if [[ -n "$cur_id" && "$line" =~ ^[[:space:]]+description:[[:space:]]*\'(.*)\'$ ]]; then
    desc="${BASH_REMATCH[1]}"
    # YAML single-quoted: '' = literal '
    desc="${desc//\'\'/\'}"
    if [[ -z "${catalog_descs[$cur_id]:-}" ]]; then
      catalog_descs["$cur_id"]="$desc"
    fi
  fi
  # Match:   runtime_message: "..." — overrides description
  if [[ -n "$cur_id" && "$line" =~ ^[[:space:]]+runtime_message:[[:space:]]*\"(.*)\"$ ]]; then
    rmsg="${BASH_REMATCH[1]}"
    rmsg=$(printf '%b' "$rmsg")
    rmsg="${rmsg//\\\"/\"}"
    catalog_descs["$cur_id"]="$rmsg"
  fi
  # Reset cur_id only when we hit the start of the next entry.
  # (The previous code reset on description; with the two-field
  # design we may see runtime_message AFTER description, so we
  # keep cur_id alive until the next [- id:] line.)
done < "$CATALOG"

# Extract all (id, message) pairs from validators.ml
# Handles both: message = "..." and message = {|...|} forms
# Uses perl for reliable multi-pattern extraction
tmp_rt=$(mktemp)
trap 'rm -f "$tmp_rt"' EXIT

perl -0777 -ne '
  # Slurp entire file; extract (id, message) pairs supporting:
  #   message = {|...|};          (raw string, single or multi-line value)
  #   message = "...";            (double-quoted, possibly with \ line continuation)
  #   message =\n  {|...|};      (value on next line)
  #   message =\n  "...";        (value on next line)

  # First pass: collapse OCaml \ line continuations in double-quoted strings
  # OCaml: trailing \ before newline + leading whitespace = nothing
  my $src = $_;
  # We do NOT modify the file; we handle continuations during extraction.

  # Track current id
  my $cur_id = "";
  my @lines = split /\n/, $src;
  my $i = 0;
  while ($i < scalar @lines) {
    my $line = $lines[$i];

    # Track id — supports both legacy record-literal syntax
    #   { id = "XXX"; ... }
    # and v26.2.1+ labeled-argument helper-call syntax
    #   mk_result ~id:"XXX" ~severity:... ~message:...
    if ($line =~ /(?:\bid\s*=|~id\s*:)\s*"([^"]+)"/) {
      $cur_id = $1;
    }

    if ($cur_id) {
      # Case 1: message = {|...|} or ~message:{|...|} on same line
      if ($line =~ /(?:\bmessage\s*=|~message\s*:)\s*\{(\w*)\|(.+?)\|\1\}/) {
        print "$cur_id\t$2\n";
        $cur_id = "";
      }
      # Case 2: message = "..." or ~message:"..." on same line
      elsif ($line =~ /(?:\bmessage\s*=|~message\s*:)\s*"((?:[^"\\]|\\.)*)"/) {
        my $msg = $1;
        # Decode OCaml escapes so source-form variants converge:
        #  \\  -> \  (escaped backslash)  *  \"  -> "  (escaped quote)
        #  \xHH -> byte  *  \DDD -> byte  *  \n / \t / \r -> control char
        # Strategy: protect literal backslashes via a placeholder that
        # cant occur in any source string, then decode the remaining
        # escapes, then restore. Order matters because \xHH and \DDD
        # need to NOT consume bytes that came from a literal \\.
        $msg =~ s/\\\\/\x{E000}/g;
        $msg =~ s/\\"/"/g;
        $msg =~ s/\\x([0-9a-fA-F]{2})/chr(hex($1))/ge;
        $msg =~ s/\\(\d{3})/chr(oct($1))/ge;
        $msg =~ s/\\n/\n/g;
        $msg =~ s/\\t/\t/g;
        $msg =~ s/\\r/\r/g;
        $msg =~ s/\x{E000}/\\/g;
        print "$cur_id\t$msg\n";
        $cur_id = "";
      }
      # Case 3: message = "...\ or ~message:"...\ (line continuation)
      elsif ($line =~ /(?:\bmessage\s*=|~message\s*:)\s*"(.*)\\\s*$/) {
        my $msg = $1;
        # Collect continuation lines until closing "
        while (++$i < scalar @lines) {
          my $cont = $lines[$i];
          $cont =~ s/^\s+//;  # strip leading whitespace
          if ($cont =~ /^(.*)"/) {
            $msg .= $1;
            last;
          } else {
            $cont =~ s/\\\s*$//;  # strip trailing \
            $msg .= $cont;
          }
        }
        # Decode OCaml escapes so source-form variants converge:
        #  \\  -> \  (escaped backslash)  *  \"  -> "  (escaped quote)
        #  \xHH -> byte  *  \DDD -> byte  *  \n / \t / \r -> control char
        # Strategy: protect literal backslashes via a placeholder that
        # cant occur in any source string, then decode the remaining
        # escapes, then restore. Order matters because \xHH and \DDD
        # need to NOT consume bytes that came from a literal \\.
        $msg =~ s/\\\\/\x{E000}/g;
        $msg =~ s/\\"/"/g;
        $msg =~ s/\\x([0-9a-fA-F]{2})/chr(hex($1))/ge;
        $msg =~ s/\\(\d{3})/chr(oct($1))/ge;
        $msg =~ s/\\n/\n/g;
        $msg =~ s/\\t/\t/g;
        $msg =~ s/\\r/\r/g;
        $msg =~ s/\x{E000}/\\/g;
        print "$cur_id\t$msg\n";
        $cur_id = "";
      }
      # Case 4: message = (newline, value on next line) OR
      # ~message:(newline, value on next line)
      elsif ($line =~ /(?:\bmessage\s*=|~message\s*:)\s*$/) {
        $i++;
        if ($i < scalar @lines) {
          my $next = $lines[$i];
          # Raw string on next line (standard or alternate delimiter)
          if ($next =~ /\{(\w*)\|(.+?)\|\1\}/) {
            print "$cur_id\t$2\n";
            $cur_id = "";
          }
          # Double-quoted on next line (no continuation)
          elsif ($next =~ /"((?:[^"\\]|\\.)*)"/) {
            my $msg = $1;
            $msg =~ s/\\\\/\x{E000}/g;
            $msg =~ s/\\"/"/g;
            $msg =~ s/\\x([0-9a-fA-F]{2})/chr(hex($1))/ge;
            $msg =~ s/\\(\d{3})/chr(oct($1))/ge;
            $msg =~ s/\\n/\n/g;
            $msg =~ s/\\t/\t/g;
            $msg =~ s/\\r/\r/g;
            $msg =~ s/\x{E000}/\\/g;
            print "$cur_id\t$msg\n";
            $cur_id = "";
          }
          # Double-quoted with line continuation
          elsif ($next =~ /"(.*)\\\s*$/) {
            my $msg = $1;
            while (++$i < scalar @lines) {
              my $cont = $lines[$i];
              $cont =~ s/^\s+//;
              if ($cont =~ /^(.*)"/) {
                $msg .= $1;
                last;
              } else {
                $cont =~ s/\\\s*$//;
                $msg .= $cont;
              }
            }
            $msg =~ s/\\\\/\x{E000}/g;
            $msg =~ s/\\"/"/g;
            $msg =~ s/\\x([0-9a-fA-F]{2})/chr(hex($1))/ge;
            $msg =~ s/\\(\d{3})/chr(oct($1))/ge;
            $msg =~ s/\\n/\n/g;
            $msg =~ s/\\t/\t/g;
            $msg =~ s/\\r/\r/g;
            $msg =~ s/\x{E000}/\\/g;
            print "$cur_id\t$msg\n";
            $cur_id = "";
          }
        }
      }
    }
    $i++;
  }
' "${RUNTIME_GLOB[@]}" > "$tmp_rt"

warn=0
checked=0
# Deduplicate: each rule has two id = lines (one in result record, one in outer rule).
# We only want the one paired with a message, which is what our extraction gives.
declare -A seen
while IFS=$'\t' read -r id msg; do
  [[ -z "$msg" ]] && continue
  # Skip if we've already checked this ID (takes first occurrence)
  [[ -n "${seen[$id]:-}" ]] && continue
  seen["$id"]=1

  # Look up catalogue description
  catalog_desc="${catalog_descs[$id]:-}"
  if [[ -z "$catalog_desc" ]]; then
    # Rule exists in runtime but not in catalogue — skip
    continue
  fi

  checked=$((checked + 1))
  if [[ "$catalog_desc" != "$msg" ]]; then
    echo "[msg] WARN: message mismatch for $id" >&2
    echo "  catalog : $catalog_desc" >&2
    echo "  runtime : $msg" >&2
    warn=$((warn + 1))
  fi
done < "$tmp_rt"

if [[ ${FAIL_ON_MISMATCH:-0} -eq 1 && $warn -gt 0 ]]; then
  echo "[msg] FAIL: $warn mismatches out of $checked checked" >&2
  exit 3
fi

echo "[msg] Completed: $checked rules checked, $warn mismatches"
