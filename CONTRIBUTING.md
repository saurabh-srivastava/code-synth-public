# Contributing

This is a research-stage project.  Most "contributions" today
look like phase-completion routines run by the project owner;
external contributions are welcome but informal.

## Phase-completion routine

When a phase finishes — i.e., a new `**Phase 3.X — … : DONE**`
entry has been added to `CHANGELOG.md` (or the recent-phases
section in `CLAUDE.md`) and any encoding lesson banked — spawn
a `general-purpose` subagent to refresh files that need to
stay in sync with the implementation:

| File          | Cadence            | Subagent's job                                            |
| ---           | ---                | ---                                                       |
| `problem.skill` | every phase      | Update REC entries, atom-shape reference, tractability table, verified-benchmark cheat sheet, "not yet supported" list. |
| `debug.skill`   | every phase      | Update triage table, soundness signals, inspection commands, lessons-banked tracebacks. |
| `README.md`     | every phase      | Update the **Status** paragraph (current phase, what's verified, what isn't) and the quick-start example if the API surface changed. |
| `BENCHMARKS.STATUS.md` | every phase / when a benchmark lands or moves | Per-benchmark catalog: path, verifies-via, V/S, time, helpers tier, discoveries, caveats. |
| `CHANGELOG.md`  | every phase      | Append the phase entry (or update an in-flight one).  Per-phase entries follow the same shape as historic `CLAUDE.md` `§Current phase` entries. |
| `SOUNDNESS.md`  | when verifier pipeline changes | Update the validity-check section, the constraint-kind/translator table, and the safety nets.  Examples of triggers: new translator landing, lenient policy change, new constraint kind. |
| `RESEARCH.md`   | infrequent       | Only when a phase yields a new research insight — a sub-thread splits, an open question resolves, a thread becomes more or less tractable.  Usually "no edits needed". |
| `RESEARCH.LEAN.md` | when the Lean backend's capability surface changes | Update the translator table, Ring status, and "what's covered" list.  Triggered by new translators, kind splits, cache mechanism changes. |
| `lean/README.md`   | when Lean project layout / setup changes | Translator surface, project layout diagram, setup instructions.  Don't edit just for status. |
| `EXPERIENCE_REPORT.md` | when a case study surfaces | New case-study entries.  See "Experience-report rule" section below for criteria. |
| `PRINCIPLES.md` | when a new always-on reminder is banked | Always-on reminders + governing principles + north-star expansions. |
| `DESIGN.md`     | when a hurdle resolves or a new hurdle surfaces | Annotate `§7 Biggest hurdles, ranked` with RESOLVED / PARTIALLY RESOLVED / DEFERRED markers + the resolving phase reference (e.g., "**RESOLVED** (Phase 3.X.2 / PLDI'09 reduction); see CHANGELOG"). Do NOT rewrite §3-§6 algorithm prose or design rationale — those are the original design document. §2 / §4.2 (API surface) are kept in sync when the `Problem` dataclass changes. |

The audiences:
- `problem.skill` and `debug.skill` — a future LLM driving the
  synthesizer.
- `README.md` — public / human readers.
- `CLAUDE.md` — the implementer (Claude during a session).
  Recent phases + always-on reminders pointer + repo layout.
- `RESEARCH.md` — forward-looking design conversations.
- `CHANGELOG.md` — phase history (everything older than the
  most recent few in CLAUDE.md).

### The subagent's job

1. Read CLAUDE.md (especially the new phase entry and any new
   encoding lesson) plus all relevant target files.
2. Distill any new content implied by the phase:
   - **problem.skill**: new atom shapes, template features,
     supported nestings, spec-authoring traps, tractability data
     points, verified-benchmark cheat-sheet entries.
   - **debug.skill**: new soundness signals, lessons banked whose
     pattern matters when debugging (not pure internal refactors),
     new inspection techniques surfaced by bug-hunting, new
     triage-table entries.
   - **README.md**: bump the Status paragraph (current phase,
     benchmark count, what's now verified); update the quick-start
     example if the public API changed.  No need to edit if just
     an internal refactor.
   - **CHANGELOG.md**: append the phase entry in the same shape
     as the existing entries (DONE marker + body + lessons
     banked).
   - **RESEARCH.md**: only edit if the phase shifts something about
     the research threads (e.g., a foundation it was gated on is
     now solid, a sub-thread splits off, an open question gets
     answered).  Default: no edits.
3. Edit files in place while preserving their existing structure.
   Avoid implementation details in the .skill files / README that
   don't change what the LLM should TRY, AVOID, or INVESTIGATE.

Use a self-contained prompt that includes the new phase title,
the lesson number/text, and the key takeaway — the subagent has
no memory of the conversation.  The subagent returns a short
summary of what changed in each file (or "no edits needed" for
files where nothing applies).

**A phase often touches only 1–2 of these files.**  Don't force
edits where there's nothing to say — "no edits needed" is the
right answer when the phase is an internal refactor that doesn't
change LLM-facing surface, doesn't move the status forward
visibly, and doesn't affect the research direction.

## Experience-report rule

`EXPERIENCE_REPORT.md` is a long-form writeup targeted at "Is
Claude a good research assistant?"  When a phase or sub-phase
surfaces something genuinely interesting about the
human-Claude partnership, add a case study.  Concretely, add
an entry whenever:

  - **A decision point branched on evidence Claude didn't have
    until results came in** (e.g., the cache+Lean architecture
    branched after seeing Z3 unsoundness on factorial's post-
    bundle).
  - **The user pushed back on a Claude proposal in a way that
    revealed a soundness/rigor gradient** (e.g., prose
    `.invalid.lean` → mechanically-checked `.invalid.lean`).
  - **Claude independently surfaced an issue or proposed an idea**
    that turned out to be load-bearing (e.g., signature-hash
    filename for content-addressable corpus).
  - **A "success" turned out to be misleading** — Claude
    declared completion before checking the soundness condition.

Each entry: decision point, evidence that surfaced it,
resolution, what Claude did well, what Claude missed.  Be
concrete and specific.  Avoid platitudes.

**The doc is verbose by design** — comprehensiveness over
brevity.  Earlier guidance targeted "5-8 pages total"; that
target was retired (2026-06-07) in favor of preserving the
full case-study record.  Don't pad: if a phase was uneventful,
no case study is needed.

## Session-transcript rotation

Every so often (rough heuristic: when the working session has
grown long enough that scrolling back is painful, OR roughly
every 5-10 substantive commits), the project owner runs
`/export` and stashes the file under
`dev-transcripts/<short-sha>.md`.  Transcripts are
committed alongside other work — they're part of the
project's history and decision trail.

## Code style

Pure Python + `z3-solver` for the synthesizer; Lean 4 for
the proof backend.  No specific style guide; follow existing
conventions in adjacent files.  Type hints throughout the
synth package.

## Reporting issues

GitHub issues: bug reports, capability questions, benchmark
proposals all welcome.  For benchmark proposals that would
require new framework primitives, please describe the
mathematical content + the IR shape you imagine; framework
extensions are evaluated by the "framework improvements over
single-case fixes" principle (see `PRINCIPLES.md`).
