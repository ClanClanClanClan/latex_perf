(** Fix policy (OPEN-105, OPEN-110, OPEN-112) — which rules the DEFAULT fixer
    may apply.

    The default [--apply-fixes] run used to apply every rule's auto-fix.
    Measured on real compiling arXiv papers, that broke roughly one paper in
    eight or nine (12.2% on frame ranks 400-719, OPEN-110), and some papers that
    still compiled had their mathematics silently changed, which the break rate
    cannot see at all. Three rounds of per-rule guards and a class-level region
    guard did not move the out-of-sample break rate (OPEN-109). The owner
    therefore turned the default into an ALLOW-LIST: a rule's fix is applied by
    default only if that rule was measured not to change what the paper says or
    how it is laid out. Every other rule keeps its detection and keeps its fix,
    but the fix is explicit opt-in, either one rule at a time with
    [--apply-fixes-for] or all at once with [--apply-fixes-all].

    Membership of {!default_allowlist} is a CLAIM about the world, not a
    preference. It is checked by a gate, and {!implicated} is the tripwire: a
    rule that was ever measured in a break repair set may never enter the
    default set. *)

val default_allowlist : string list
(** The rule ids whose fixes the default [--apply-fixes] applies. Each entry is
    a claim that the rule's fix passed the OPEN-112 meaning review: it was
    applied alone to real compiling papers, no measured case changed the words,
    symbols or mathematics of the typeset output or was wrong for its context,
    and an independent attempt to refute that found no damage. The gate
    scripts/tools/check_fix_allowlist.py enforces it against the committed
    evidence, so an id cannot be added without that measurement. *)

val in_default_set : string -> bool
(** [in_default_set id] is true exactly when [id] is in {!default_allowlist}. *)

val implicated : string list
(** The 24 rules measured in at least one break repair set (OPEN-109 and
    OPEN-110). None of them may ever be in {!default_allowlist}; the unit test
    asserts the two lists are disjoint. Removing an id from this list requires a
    new out-of-sample measurement, not a producer fix on a tuned window. *)
