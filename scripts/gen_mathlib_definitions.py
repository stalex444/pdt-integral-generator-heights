#!/usr/bin/env python3
"""Generate MATHLIB_DEFINITIONS.md: verbatim excerpts of the pinned Mathlib definitions the
compared statements rest on, each with path, line range and permalink, byte-compared against
raw.githubusercontent.com at the pinned SHA.

Usage (from the repository root):
  python3 scripts/gen_mathlib_definitions.py scripts/mathlib_definitions_spec.json > MATHLIB_DEFINITIONS.md
spec.json: {"intro": "...", "sections": [{"title": "...", "path": "Mathlib/…/X.lean",
            "start": 12, "end": 20, "comment": "what the Challenge uses it for; kernel-checked
            consequence in DefinitionAudit"}, ...]}
Lines are 1-based inclusive. Exit 1 if any excerpt differs from GitHub at the SHA.
"""
import json, os, sys, urllib.request

SHA = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
LOCAL = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                     ".lake", "packages", "mathlib")


def excerpt_local(path, start, end):
    with open(os.path.join(LOCAL, path), encoding="utf-8") as f:
        lines = f.read().split("\n")
    return "\n".join(lines[start - 1:end])


def excerpt_remote(path, start, end):
    url = "https://raw.githubusercontent.com/leanprover-community/mathlib4/%s/%s" % (SHA, path)
    with urllib.request.urlopen(url, timeout=60) as r:
        lines = r.read().decode("utf-8").split("\n")
    return "\n".join(lines[start - 1:end])


def main():
    spec = json.load(open(sys.argv[1], encoding="utf-8"))
    out = ["# Imported Mathlib definitions", "", spec["intro"].strip(), ""]
    bad = 0
    for n, s in enumerate(spec["sections"], 1):
        loc = excerpt_local(s["path"], s["start"], s["end"])
        rem = excerpt_remote(s["path"], s["start"], s["end"])
        if loc != rem:
            bad += 1
            sys.stderr.write("MISMATCH %s:%d-%d (local vs GitHub @%s)\n" % (s["path"], s["start"], s["end"], SHA[:12]))
        link = "https://github.com/leanprover-community/mathlib4/blob/%s/%s#L%d-L%d" % (SHA, s["path"], s["start"], s["end"])
        out += ["## %d. %s" % (n, s["title"]), "",
                "`%s`, lines %d–%d: <%s>" % (s["path"], s["start"], s["end"], link), "",
                "```lean", loc, "```", ""]
        if s.get("comment"):
            out += [s["comment"].strip(), ""]
    sys.stdout.write("\n".join(out).rstrip("\n") + "\n")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
