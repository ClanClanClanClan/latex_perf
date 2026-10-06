set pagination off
set breakpoint pending on
break kpathsea_find_file_generic
commands
silent
printf "FIND name=%s format=%d must_exist=%d all=%d\n", const_name, format, must_exist, all
continue
end
break kpathsea_path_search_list_generic
commands
silent
printf "SEARCH must_exist=%d all=%d path=%s\n", must_exist, all, path
set $i = 0
while names[$i] != 0
printf "  NAME %s\n", names[$i]
set $i = $i + 1
end
continue
end
break kpathsea_readable_file
commands
silent
printf "READABLE %s\n", name
continue
end
break kpathsea_dir_p
commands
silent
printf "DIR_P %s\n", fn
continue
end
break opendir
commands
silent
printf "OPENDIR %s\n", (char*)$x0
continue
end
break kpathsea_db_search_list
commands
silent
printf "DBSEARCH elt=%s\n", path_elt
continue
end
break mainbody
commands
silent
printf "MAINBODY\n"
printf "DBDIRS %d\n", kpse_def->db_dir_list.length
set $i = 0
while $i < kpse_def->db_dir_list.length
printf "  DBDIR %s\n", kpse_def->db_dir_list.list[$i]
set $i = $i + 1
end
printf "ALIASDB %p\n", kpse_def->alias_db.buckets
printf "DBBUCKETS %p size %d\n", kpse_def->db.buckets, kpse_def->db.size
continue
end
break uexit
commands
silent
printf "UEXIT\n"
end
run
set $f = 0
while $f < 58
if kpse_def->format_info[$f].path != 0
printf "FMT %d type=%s path=%s\n", $f, kpse_def->format_info[$f].type, kpse_def->format_info[$f].path
printf "  source=%s sso=%d enabled=%d binmode=%d program=%s\n", kpse_def->format_info[$f].path_source, kpse_def->format_info[$f].suffix_search_only, kpse_def->format_info[$f].program_enabled_p, kpse_def->format_info[$f].binmode, kpse_def->format_info[$f].program
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
set $f = $f + 1
end
printf "MAPSIZE %d\n", kpse_def->map.size
