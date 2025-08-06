(lang dune 3.10)
(using coq 0.8)
(name latex-perfectionist)
(generate_opam_files true)
(implicit_transitive_deps true)

(package
 (name latex-perfectionist)
 (synopsis "LaTeX Perfectionist v25 bootstrap")
 (depends
  (ocaml         (>= 5.1.1))
  (dune          (>= 3.10))
  (coq           (= 8.18.0))
  (coq-core      (= 8.18.0))
  (yojson        (>= 2.1))
  (ppx_deriving  (>= 5.2))
  (angstrom      (>= 0.16))
  (uutf          (>= 1.0.3))))

