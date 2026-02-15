#!/usr/bin/env bash
set -euo pipefail

# Validate that runtime messages match catalogue descriptions exactly.
# Extracts all rule IDs from validators.ml and checks against rules_v3.yaml.

CATALOG=specs/rules/rules_v3.yaml
RUNTIME=latex-parse/src/validators.ml

if [[ ! -f "$CATALOG" || ! -f "$RUNTIME" ]]; then
  echo "[msg] ERROR: missing inputs" >&2
  exit 2
fi

# Build a mapping of id -> description from the YAML catalogue
# Uses simple grep+sed since the YAML is well-structured
declare -A catalog_descs
cur_id=""
while IFS= read -r line; do
  # Match: - id: "XXX"
  if [[ "$line" =~ ^-[[:space:]]+id:[[:space:]]*\"([^\"]+)\" ]]; then
    cur_id="${BASH_REMATCH[1]}"
  fi
  # Match:   description: "..."
  if [[ -n "$cur_id" && "$line" =~ ^[[:space:]]+description:[[:space:]]*\"(.*)\"$ ]]; then
    # Unescape YAML double-quoted string: \\ -> \, \" -> "
    desc="${BASH_REMATCH[1]}"
    desc="${desc//\\\\/\\}"
    desc="${desc//\\\"/\"}"
    catalog_descs["$cur_id"]="$desc"
    cur_id=""
  fi
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

    # Track id = "XXX"
    if ($line =~ /id\s*=\s*"([^"]+)"/) {
      $cur_id = $1;
    }

    if ($cur_id) {
      # Case 1: message = {|...|} on same line
      if ($line =~ /message\s*=\s*\{\|(.+?)\|\}/) {
        print "$cur_id\t$1\n";
        $cur_id = "";
      }
      # Case 2: message = "..." on same line (no line continuation)
      elsif ($line =~ /message\s*=\s*"((?:[^"\\]|\\.)*)"/) {
        my $msg = $1;
        $msg =~ s/\\\\/\\/g;
        $msg =~ s/\\"/"/g;
        print "$cur_id\t$msg\n";
        $cur_id = "";
      }
      # Case 3: message = "...\ (line continuation)
      elsif ($line =~ /message\s*=\s*"(.*)\\\s*$/) {
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
        $msg =~ s/\\\\/\\/g;
        $msg =~ s/\\"/"/g;
        print "$cur_id\t$msg\n";
        $cur_id = "";
      }
      # Case 4: message = (newline, value on next line)
      elsif ($line =~ /message\s*=\s*$/) {
        $i++;
        if ($i < scalar @lines) {
          my $next = $lines[$i];
          # Raw string on next line
          if ($next =~ /\{\|(.+?)\|\}/) {
            print "$cur_id\t$1\n";
            $cur_id = "";
          }
          # Double-quoted on next line (no continuation)
          elsif ($next =~ /"((?:[^"\\]|\\.)*)"/) {
            my $msg = $1;
            $msg =~ s/\\\\/\\/g;
            $msg =~ s/\\"/"/g;
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
            $msg =~ s/\\\\/\\/g;
            $msg =~ s/\\"/"/g;
            print "$cur_id\t$msg\n";
            $cur_id = "";
          }
        }
      }
    }
    $i++;
  }
' "$RUNTIME" > "$tmp_rt"

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
