"""Dump all 164 HumanEval+ problems to a structured file.

Reads from HuggingFace evalplus/humanevalplus; writes a compact
one-record-per-line digest to all_problems.txt + a JSON manifest.
The digest format is optimized for an LLM to read sequentially
and triage each problem in turn.
"""
from datasets import load_dataset
import json
import re
import pathlib

OUT_DIR = pathlib.Path(__file__).parent
DIGEST = OUT_DIR / "all_problems.txt"
JSON_OUT = OUT_DIR / "all_problems.json"

ds = load_dataset("evalplus/humanevalplus", split="test")

records = []
with DIGEST.open("w") as f:
    for ex in ds:
        task_id = ex["task_id"]
        prompt = ex["prompt"].rstrip()
        canonical = (ex.get("canonical_solution") or "").rstrip()
        entry = ex.get("entry_point", "?")

        # Extract the signature line.
        sig_match = re.search(r"^def\s+\w+[^\n]*", prompt, re.MULTILINE)
        sig = sig_match.group(0) if sig_match else "(no signature)"

        # Approximate canonical-solution length.
        canon_lines = len([l for l in canonical.split("\n") if l.strip()])

        records.append({
            "task_id": task_id,
            "entry_point": entry,
            "signature": sig,
            "prompt": prompt,
            "canonical": canonical,
            "canonical_lines": canon_lines,
        })

        f.write(f"╔══ {task_id}  ({canon_lines} canonical lines)\n")
        f.write(f"║ signature: {sig}\n")
        f.write(f"║ ── prompt ──\n")
        for line in prompt.split("\n"):
            f.write(f"║ {line}\n")
        f.write(f"║ ── canonical ──\n")
        for line in canonical.split("\n"):
            f.write(f"║ {line}\n")
        f.write(f"╚══\n\n")

with JSON_OUT.open("w") as f:
    json.dump(records, f, indent=2)

print(f"Wrote {DIGEST} ({DIGEST.stat().st_size} bytes)")
print(f"Wrote {JSON_OUT}")
print(f"Total problems: {len(records)}")
print(f"Avg canonical lines: {sum(r['canonical_lines'] for r in records) / len(records):.1f}")
