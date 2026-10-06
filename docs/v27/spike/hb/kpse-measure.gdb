set pagination off
set print elements 0
break mainbody
run
printf "ARGV0 %s\n", kpse_def->invocation_name
printf "PROGNAME %s\n", kpse_def->program_name
set $vars = 0
define pv
  set $v = (char*) kpathsea_var_value(kpse_def, $arg0)
  if $v != 0
    printf "VAR %s=%s\n", $arg0, $v
  else
    printf "VARNULL %s\n", $arg0
  end
end
pv "texmf_casefold_search"
pv "try_std_extension_first"
pv "TEXMFLOG"
pv "TEXMFOUTPUT"
pv "openout_any"
pv "openin_any"
pv "log_openout"
pv "texmf_nlink_for_leaf"
pv "shell_escape"
define pf
  set $f = $arg0
  call (char*) kpathsea_init_format(kpse_def, $f)
  printf "KFMT %d sso=%d enabled=%d program=%s\n", $f, kpse_def->format_info[$f].suffix_search_only, kpse_def->format_info[$f].program_enabled_p, kpse_def->format_info[$f].program ? kpse_def->format_info[$f].program : "(null)"
  printf "  PATH %s\n", kpse_def->format_info[$f].path
  set $j = 0
  while kpse_def->format_info[$f].suffix != 0 && kpse_def->format_info[$f].suffix[$j] != 0
    printf "  SUFFIX %s\n", kpse_def->format_info[$f].suffix[$j]
    set $j = $j + 1
  end
  set $j = 0
  while kpse_def->format_info[$f].alt_suffix != 0 && kpse_def->format_info[$f].alt_suffix[$j] != 0
    printf "  ALTSUFFIX %s\n", kpse_def->format_info[$f].alt_suffix[$j]
    set $j = $j + 1
  end
end
pf 3
pf 9
pf 10
pf 11
pf 26
pf 33
printf "DBDIRS %d\n", kpse_def->db_dir_list.length
set $i = 0
while $i < kpse_def->db_dir_list.length
  printf "  DBDIR %s\n", kpse_def->db_dir_list.list[$i]
  set $i = $i + 1
end
printf "ALIASDB %p\n", kpse_def->alias_db.buckets
printf "FOLLOWUP %d\n", kpse_def->followup_search
kill
