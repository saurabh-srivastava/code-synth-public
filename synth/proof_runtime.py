"""Runtime proof check library for the Python emitter.

When the Python emitter (Phase 5.C) is called with
`runtime_check=True`, it lowers the proof annotations
(pre/post/invariants/decrease/lower-bound/coverage) into runtime
calls against this module instead of leaving them as static
comments.  Each call raises `ProofViolation` (an `AssertionError`
subclass) with a structured diagnostic when the check fails.

This turns synthesized proof annotations from documentation into
executable safety nets — a useful affordance when an LLM driver is
iterating on a `Problem` and wants a quick "does this actually run
correctly on sample inputs?" check before falling through to clang
+ the full C runtime test.

The library is intentionally minimal and behavior-fixed (raise on
failure).  Configurable behaviors (collect-violations mode, telemetry
hooks, log-only mode) are future extensions when an actual use case
surfaces.

Functions
---------

  proof_check(cond, message)            generic; prefer specialized variants below
  proof_pre(cond, message)              precondition at procedure entry
  proof_post(cond, message)             postcondition at procedure exit
  proof_invariant(cond, message)        loop invariant
  proof_decrease(curr, prev, message)   ranking-function strict decrease
  proof_lower_bound(value, message,     ranking-function lower bound
                    bound=0)
  proof_coverage(*guards, message)      SB(n>1) branch coverage

All functions take a `message` (typically the textual form of the
proof obligation, e.g., `"L0: i <= n"`) used in the diagnostic if
the check fails.

Failure behavior
----------------

Each function raises `ProofViolation(kind, message, *details)`
where:
  - `kind` is the constraint category (`"pre"`, `"post"`,
    `"invariant"`, `"decrease"`, `"ranking-lb"`, `"coverage"`,
    `"check"` for the generic variant).
  - `message` is the user-supplied textual obligation.
  - `details` are the actual offending values, where applicable
    (e.g., `("prev=5", "curr=5")` for a decrease that didn't strictly
    decrease).

`ProofViolation` extends `AssertionError`, so it's caught by code
that catches `AssertionError`, and `pytest --assert=rewrite` can
introspect it like a normal assertion.
"""
from __future__ import annotations


# ─────────────────────────────────────────────────────────────────────
# Exception type.
# ─────────────────────────────────────────────────────────────────────
class ProofViolation(AssertionError):
    """A runtime proof check failed.

    Subclasses `AssertionError` so that:
      - existing `try: ... except AssertionError:` blocks catch it.
      - pytest's rich assertion reporting treats it like a normal
        failed assertion.
    """

    def __init__(self, kind: str, message: str, *details: object) -> None:
        self.kind = kind
        self.message = message
        self.details = details
        header = f"{kind}: {message}" if message else kind
        if details:
            tail = " (" + ", ".join(str(d) for d in details) + ")"
        else:
            tail = ""
        super().__init__(header + tail)


# ─────────────────────────────────────────────────────────────────────
# Check functions — one per proof obligation kind.
# ─────────────────────────────────────────────────────────────────────
def proof_check(cond: object, message: str = "") -> None:
    """Generic proof check.  Prefer the specialized variants
    (`proof_pre`, `proof_post`, etc.) when the obligation has a
    specific kind — the specialized error messages are more
    informative."""
    if not cond:
        raise ProofViolation("check", message)


def proof_pre(cond: object, message: str = "") -> None:
    """Precondition at procedure entry.

    Raises immediately on a violation — fail-fast for invalid
    inputs.  By the time the synthesized body runs, the spec's
    `Pre` is assumed to hold; if it doesn't, the proof's
    correctness guarantee is void.
    """
    if not cond:
        raise ProofViolation("pre", message)


def proof_post(cond: object, message: str = "") -> None:
    """Postcondition at procedure exit.

    A violation here means the synthesized program didn't actually
    compute what the spec promised — either the synthesizer's
    proof is unsound (unlikely, but possible — see CLAUDE.md
    Lessons #26 / #27 / #30) or the emitted code diverges from
    the verified IR (an emitter bug).
    """
    if not cond:
        raise ProofViolation("post", message)


def proof_invariant(cond: object, message: str = "") -> None:
    """Loop invariant.  Must hold at the top of every iteration of
    the loop body, AND at the loop's exit (when `¬g` is true)."""
    if not cond:
        raise ProofViolation("invariant", message)


def proof_decrease(curr: int, prev: int, message: str = "") -> None:
    """Ranking-function strict decrease: `curr < prev` must hold
    each iteration.  Combined with `proof_lower_bound`, this proves
    termination.

    `prev` is the ranking expression evaluated at the loop body's
    *entry*; `curr` at the body's *exit*.  The emitter captures
    `prev` into a local at body entry and emits this call at body
    exit.
    """
    if not (curr < prev):
        raise ProofViolation("decrease", message,
                             f"prev={prev}", f"curr={curr}")


def proof_lower_bound(value: int, message: str = "",
                      bound: int = 0) -> None:
    """Ranking-function lower bound: `value >= bound`.

    Default `bound=0` matches the standard pattern (POPL'10
    §3.5).  Combined with `proof_decrease`, this proves the
    ranking function can't continue decreasing indefinitely — the
    loop terminates.
    """
    if not (value >= bound):
        raise ProofViolation("ranking-lb", message,
                             f"value={value}", f"bound={bound}")


def proof_coverage(*guards: object, message: str = "") -> None:
    """SB(n>1) branch coverage: at least one branch guard must be
    True when control reaches a multi-branch SB.

    Runtime counterpart of the synthesizer's `⋁ g_i ≡ true`
    well-formedness constraint.  A violation here would mean the
    synthesizer's coverage check missed the actual reachable state
    space — a soundness bug worth filing.
    """
    if not any(guards):
        raise ProofViolation("coverage", message)
