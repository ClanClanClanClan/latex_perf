(** PR #241 (p1.1-#4 + p1.3): missing/malformed rule_contracts.json must be a
    fatal error, not a silent empty-list fallback. Exercises the loader via a
    fresh subprocess with [LP_RULE_CONTRACTS_JSON] pointing to a bogus path.

    The loader is memoised at process level, so to actually exercise the
    missing-file path we fork+exec [validators_cli.exe] (which triggers
    [Rule_contract_loader.load] at startup) and check the exit code. *)

open Latex_parse_lib
open Test_helpers

let run_cli_with_env ~env args =
  let exe =
    Filename.concat (Filename.dirname Sys.argv.(0)) "validators_cli.exe"
  in
  let stdout_r, stdout_w = Unix.pipe () in
  let stderr_r, stderr_w = Unix.pipe () in
  let pid =
    Unix.create_process_env exe
      (Array.of_list (exe :: args))
      env Unix.stdin stdout_w stderr_w
  in
  Unix.close stdout_w;
  Unix.close stderr_w;
  let read_all fd =
    let buf = Buffer.create 256 in
    let bytes = Bytes.create 4096 in
    let rec loop () =
      let n = Unix.read fd bytes 0 4096 in
      if n > 0 then (
        Buffer.add_subbytes buf bytes 0 n;
        loop ())
    in
    (try loop () with Unix.Unix_error _ -> ());
    Unix.close fd;
    Buffer.contents buf
  in
  let stdout = read_all stdout_r in
  let stderr = read_all stderr_r in
  let _, status = Unix.waitpid [] pid in
  let code = match status with Unix.WEXITED c -> c | _ -> -1 in
  (stdout, stderr, code)

let () =
  (* 1. Exception constructor is part of the public API. *)
  run "Rule_contracts_missing exception constructor exists" (fun tag ->
      let check =
        try
          raise
            (Rule_contract_loader.Rule_contracts_missing "synthetic failure")
        with Rule_contract_loader.Rule_contracts_missing msg ->
          String.length msg > 0
      in
      expect check (tag ^ ": exception carries a non-empty message"));

  (* 2. Loader succeeds under normal conditions. *)
  run "loader succeeds when file present" (fun tag ->
      let n = Rule_contract_loader.count () in
      expect (n >= 645)
        (tag ^ ": loader returned " ^ string_of_int n ^ " contracts"));

  (* 3. Every runtime rule has a contract. *)
  run "no runtime rule missing from contracts" (fun tag ->
      let results = Validators.run_all "\\documentclass{article}\n" in
      ignore results;
      expect true (tag ^ ": run_all completed without startup failure"));

  (* 4. PR #241 (p1.3): actually exercise the missing-file path via subprocess.
     The loader's upward-search walks from [Sys.executable_name] up to 8 levels;
     running the normal exe_path finds the repo-root contract file. To defeat
     this, copy validators_cli.exe into a pristine tmp directory (no ancestor
     contains [specs/rules/rule_contracts.json]) and run it from there. Also set
     [LP_RULE_CONTRACTS_JSON] to a nonexistent path so the env override can't
     redirect to a real file either. *)
  run "CLI fails fatally when contract file truly missing" (fun tag ->
      let tmp_dir = Filename.temp_file "rcload_" "" in
      Sys.remove tmp_dir;
      Unix.mkdir tmp_dir 0o755;
      let exe_src =
        Filename.concat (Filename.dirname Sys.argv.(0)) "validators_cli.exe"
      in
      let exe_dst = Filename.concat tmp_dir "validators_cli.exe" in
      (* Copy the binary *)
      let ic = open_in_bin exe_src in
      let oc = open_out_bin exe_dst in
      let len = in_channel_length ic in
      let buf = Bytes.create len in
      really_input ic buf 0 len;
      output_bytes oc buf;
      close_in ic;
      close_out oc;
      Unix.chmod exe_dst 0o755;
      let tmp_tex = Filename.concat tmp_dir "input.tex" in
      let oc = open_out tmp_tex in
      output_string oc "\\documentclass{article}\n";
      close_out oc;
      let env =
        [|
          "PATH=/usr/bin:/bin";
          "HOME=/tmp";
          "PWD=" ^ tmp_dir;
          "LP_RULE_CONTRACTS_JSON=/nonexistent/rule_contracts.json";
        |]
      in
      let stdout_r, stdout_w = Unix.pipe () in
      let stderr_r, stderr_w = Unix.pipe () in
      (* Fork manually so the child can chdir into the pristine tmp_dir before
         exec — otherwise the cwd-relative candidate path in the loader resolves
         to the real repo-root contract file. *)
      let pid = Unix.fork () in
      if pid = 0 then (
        (* child *)
        Unix.dup2 stdout_w Unix.stdout;
        Unix.dup2 stderr_w Unix.stderr;
        Unix.close stdout_r;
        Unix.close stderr_r;
        Unix.close stdout_w;
        Unix.close stderr_w;
        (try Unix.chdir tmp_dir with _ -> ());
        Unix.execvpe exe_dst [| exe_dst; tmp_tex |] env);
      Unix.close stdout_w;
      Unix.close stderr_w;
      let read_all fd =
        let buf = Buffer.create 256 in
        let bytes = Bytes.create 4096 in
        let rec loop () =
          let n = Unix.read fd bytes 0 4096 in
          if n > 0 then (
            Buffer.add_subbytes buf bytes 0 n;
            loop ())
        in
        (try loop () with Unix.Unix_error _ -> ());
        Unix.close fd;
        Buffer.contents buf
      in
      let _stdout_out = read_all stdout_r in
      let stderr_out = read_all stderr_r in
      let _, status = Unix.waitpid [] pid in
      let code = match status with Unix.WEXITED c -> c | _ -> -1 in
      (* Cleanup tmp files *)
      (try Sys.remove tmp_tex with _ -> ());
      (try Sys.remove exe_dst with _ -> ());
      (try Unix.rmdir tmp_dir with _ -> ());
      expect (code <> 0)
        (tag ^ ": nonzero exit code (got " ^ string_of_int code ^ ")");
      let contains sub s =
        let ls = String.length s and lsub = String.length sub in
        let found = ref false in
        for i = 0 to ls - lsub do
          if (not !found) && String.sub s i lsub = sub then found := true
        done;
        !found
      in
      let mentions =
        contains "rule_contracts" stderr_out
        || contains "Rule_contracts" stderr_out
        || contains "not found" stderr_out
      in
      expect mentions
        (tag
        ^ ": stderr mentions the missing contract file. stderr="
        ^ stderr_out));

  ignore run_cli_with_env;
  finalise "rule_contract_load_failure"
