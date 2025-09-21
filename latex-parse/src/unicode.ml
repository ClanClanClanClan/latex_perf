let has_curly_quote s =
  let dec = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop () =
    match Uutf.decode dec with
    | `Uchar u ->
        let cp = Uchar.to_int u in
        if cp = 0x2018 || cp = 0x2019 || cp = 0x201C || cp = 0x201D then true else loop ()
    | `End -> false
    | `Malformed _ -> loop ()
    | `Await -> false
  in loop ()

let has_en_dash s =
  let dec = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop () =
    match Uutf.decode dec with
    | `Uchar u when Uchar.to_int u = 0x2013 -> true
    | `Uchar _ -> loop ()
    | `End -> false
    | `Malformed _ -> loop ()
    | `Await -> false
  in loop ()

let has_em_dash s =
  let dec = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop () =
    match Uutf.decode dec with
    | `Uchar u when Uchar.to_int u = 0x2014 -> true
    | `Uchar _ -> loop ()
    | `End -> false
    | `Malformed _ -> loop ()
    | `Await -> false
  in loop ()

let has_ellipsis_char s =
  let dec = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop () =
    match Uutf.decode dec with
    | `Uchar u when Uchar.to_int u = 0x2026 -> true
    | `Uchar _ -> loop ()
    | `End -> false
    | `Malformed _ -> loop ()
    | `Await -> false
  in loop ()

let count_utf8_seq s a b c =
  (* Not strictly needed with Uutf; keep minimal counters for dashes *)
  let n = String.length s in
  let rec loop i acc =
    if i+2 >= n then acc
    else
      let x = Char.code (String.unsafe_get s i) in
      let y = Char.code (String.unsafe_get s (i+1)) in
      let z = Char.code (String.unsafe_get s (i+2)) in
      if x=a && y=b && z=c then loop (i+3) (acc+1) else loop (i+1) acc
  in loop 0 0

let count_en_dash s = count_utf8_seq s 0xE2 0x80 0x93
let count_em_dash s = count_utf8_seq s 0xE2 0x80 0x94
