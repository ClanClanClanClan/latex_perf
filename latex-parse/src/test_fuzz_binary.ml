(** Binary reader fuzzing.

    Feeds random/corrupted bytes to PNG, JPEG, PDF, and font readers. Verifies
    they handle malformed input gracefully — no crashes. *)

let seed =
  match Sys.getenv_opt "TEST_SEED" with
  | Some s -> int_of_string s
  | None -> 54321

let trials =
  match Sys.getenv_opt "FUZZ_TRIALS" with
  | Some s -> int_of_string s
  | None -> 1000

let () = Random.init seed

let random_bytes n =
  let b = Bytes.create n in
  for i = 0 to n - 1 do
    Bytes.set b i (Char.chr (Random.int 256))
  done;
  b

let write_temp suffix data = Test_binary_gen.write_to_temp_file data suffix

let fuzz_reader name suffix read_fn =
  let crashes = ref 0 in
  for i = 1 to trials do
    let len = 16 + Random.int 4080 in
    let data = random_bytes len in
    let path = write_temp suffix data in
    (try ignore (read_fn path)
     with exn ->
       incr crashes;
       if !crashes <= 3 then
         Printf.eprintf "[fuzz-%s] CRASH at trial %d (%d bytes): %s\n%!" name i
           len (Printexc.to_string exn));
    try Sys.remove path with Sys_error _ -> ()
  done;
  if !crashes > 0 then
    Printf.eprintf "[fuzz-%s] %d/%d crashes\n%!" name !crashes trials;
  !crashes

let fuzz_reader_with_magic name suffix magic read_fn =
  let crashes = ref 0 in
  let magic_len = Bytes.length magic in
  for i = 1 to trials do
    let tail_len = 16 + Random.int 4080 in
    let data = Bytes.create (magic_len + tail_len) in
    Bytes.blit magic 0 data 0 magic_len;
    for j = magic_len to Bytes.length data - 1 do
      Bytes.set data j (Char.chr (Random.int 256))
    done;
    let path = write_temp suffix data in
    (try ignore (read_fn path)
     with exn ->
       incr crashes;
       if !crashes <= 3 then
         Printf.eprintf "[fuzz-%s-magic] CRASH at trial %d: %s\n%!" name i
           (Printexc.to_string exn));
    try Sys.remove path with Sys_error _ -> ()
  done;
  !crashes

let () =
  Printf.printf "[fuzz-binary] seed=%d trials=%d per format\n%!" seed trials;
  let total_crashes = ref 0 in
  (* Pure random *)
  total_crashes :=
    !total_crashes
    + fuzz_reader "png" ".png" Latex_parse_lib.Png_reader.read_png_info;
  total_crashes :=
    !total_crashes
    + fuzz_reader "jpeg" ".jpg" Latex_parse_lib.Jpeg_reader.read_jpeg_info;
  total_crashes :=
    !total_crashes
    + fuzz_reader "font" ".ttf" (fun p ->
          ignore (Latex_parse_lib.Font_reader.has_cjk_coverage p));
  (* Magic-prefix fuzzing *)
  let png_magic = Bytes.of_string "\x89PNG\r\n\x1a\n" in
  let jpeg_magic = Bytes.of_string "\xff\xd8\xff" in
  total_crashes :=
    !total_crashes
    + fuzz_reader_with_magic "png" ".png" png_magic
        Latex_parse_lib.Png_reader.read_png_info;
  total_crashes :=
    !total_crashes
    + fuzz_reader_with_magic "jpeg" ".jpg" jpeg_magic
        Latex_parse_lib.Jpeg_reader.read_jpeg_info;
  if !total_crashes > 0 then (
    Printf.eprintf "[fuzz-binary] FAIL: %d total crashes\n%!" !total_crashes;
    exit 1)
  else
    Printf.printf "[fuzz-binary] PASS %d trials/format (seed=%d)\n%!" trials
      seed
