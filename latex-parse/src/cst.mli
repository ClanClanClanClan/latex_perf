(** Lossless Concrete Syntax Tree (v26.2, PR B1).

    The CST preserves source bytes 1:1 for arbitrary input via the [Unparsed]
    variant, and preserves structure for the declared LP-Core subset. Built
    post-process from [Parser_l2]'s AST — see [Cst_of_ast] and ADR-008.

    Invariants (checked by [serialize_roundtrip]):
    - [serialize (of_source src) = src] for every source [src] — byte-lossless.
    - For sources in the declared structural-lossless subset,
      [parse (serialize (of_source src))] yields the same AST as [parse src] —
      structure-lossless. See [docs/CST_ROUNDTRIP_SCOPE.md] (to be added in PR
      B2). *)

type span = Stable_spans.t

type trivia_kind =
  | Whitespace  (** Spaces, tabs, newlines — semantically insignificant. *)
  | Comment  (** [%...] to end of line. *)

type token_kind =
  | Word  (** Plain text run. *)
  | Command  (** [\\name] plus optional stars, WITHOUT its arg groups. *)
  | GroupOpen  (** [{] *)
  | GroupClose  (** [}] *)
  | MathDelim  (** Math-mode delimiter token. *)

type t =
  | CToken of { kind : token_kind; text : string; span : span }
  | CTrivia of { kind : trivia_kind; text : string; span : span }
  | CGroup of { children : t list; span : span }
      (** Matched [{ ... }]. [span] covers the full range including delimiters.
          [children] does not include the [{]/[}] tokens themselves — they are
          reproduced from [span] on [serialize]. *)
  | CEnvironment of {
      env_name : string;
      body_text : string;
          (** Raw body bytes between the begin/end tags. Kept unstructured in
              v26.2; PR B3 rewrite engine may structure this per-environment. *)
      span : span;
    }
  | CMathInline of { text : string; span : span }
      (** Inline math (dollar or backslash-paren delimiters). [text] is the raw
          source including delimiters. *)
  | CMathDisplay of { text : string; span : span }
      (** Display math (double-dollar, bracket, or a math environment). [text]
          is the raw source including delimiters. *)
  | CVerbatim of { env_name : string; text : string; span : span }
      (** A verbatim-like environment (verbatim, lstlisting, minted, ...).
          [text] is the full source including the begin/end tags. *)
  | CUnparsed of { text : string; span : span }
      (** Byte-lossless fallback for any range the builder cannot classify.
          Round-trip lossless by construction. *)

val span_of : t -> span
(** Returns the span covering this CST node. *)

val serialize : t list -> string
(** [serialize nodes] concatenates the source bytes of each node in order. For a
    well-formed CST of source [src], returns [src]. *)

val byte_length : t list -> int
(** [byte_length nodes = String.length (serialize nodes)]. *)
