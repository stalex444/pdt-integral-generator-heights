#!/usr/bin/env python3
"""Generate Solution.lean from Challenge.lean.

Run from the repository root:  python3 scripts/make_solution.py

Solution.lean = a fixed header (imports of the proof modules) + the text of Challenge.lean from the
line `set_option autoImplicit false` on, with each of the three placeholders `  sorry` replaced by
one `exact` of a theorem of the `HeightT2` modules. The definitions that the statements use are not
repeated: in Solution.lean they come from the imported modules `HermiteCompositum.Defs` and
`HeightT2.Defs`, whose declarations have the same text as the two blocks of Challenge.lean (the
registry's comparator checks that they are the same declarations). The script asserts that
restoring the placeholders gives back the Challenge text, that the field block of Challenge.lean
equals the same block of `HermiteCompositum/Defs.lean`, and that the height block declares exactly
the definitions in HEIGHT_DEFS, each with the same text as in `HeightT2/Defs.lean`.
"""
import re
import sys

HEADER = '''module
public import Mathlib
public import HeightT2.Instance.SmallHeight
public import HeightT2.Instance.Generators
public import HeightT2.Instance.Perron

@[expose] public section
/-!
# Solution

The three statements of `Challenge.lean`, stated identically, each proved by one `exact` of a theorem
of the proof modules: `HeightT2.Instance.SmallHeight` (1), `HeightT2.Instance.Generators` (2) and
`HeightT2.Instance.Perron` (3). The definitions the statements use are those of the imported
modules `HermiteCompositum.Defs` and `HeightT2.Defs`, whose text `Challenge.lean` carries.
This file is generated from `Challenge.lean` by `scripts/make_solution.py`.
-/

'''

# the definitions carried between the HEIGHT DEFINITIONS markers (namespace HeightT2)
HEIGHT_DEFS = ["IsPerronNumber"]

PROOFS = [
    "exact HeightT2.mulHeight₁_le_mulHeight₁_ρQ_iff x hx",
    "exact HeightT2.mahlerMeasure_generator_min x hx",
    "exact HeightT2.perronNumber_generator_selection x hx hmin hP",
]


def block(text, begin, end):
    # the markers as whole lines (the Challenge's docstring also names them, inside backquotes)
    a = text.index("\n" + begin + "\n") + 1
    b = text.index("\n" + end + "\n", a) + 1 + len(end)
    return text[a:b]


def main():
    ch = open("Challenge.lean", encoding="utf-8").read()
    # the carried blocks match the modules the proofs are built on
    hc = open("HermiteCompositum/Defs.lean", encoding="utf-8").read()
    b1 = "-- BEGIN SHARED DEFINITIONS"
    e1 = "-- END SHARED DEFINITIONS"
    assert block(ch, b1, e1) == block(hc, b1, e1), "field block differs from HermiteCompositum/Defs.lean"
    hd = open("HeightT2/Defs.lean", encoding="utf-8").read()
    hb = block(ch, "-- BEGIN HEIGHT DEFINITIONS", "-- END HEIGHT DEFINITIONS")
    # the height block declares exactly HEIGHT_DEFS, inside `namespace HeightT2`
    names = re.findall(r"^(?:noncomputable )?def (\S+)", hb, re.M)
    assert names == HEIGHT_DEFS, names
    assert "\nnamespace HeightT2\n" in hb and "\nend HeightT2\n" in hb
    # every non-comment piece of the block (each definition with its docstring, and the
    # `open` line) occurs verbatim in HeightT2/Defs.lean
    checked = 0
    for piece in re.split(r"\n\n+", hb):
        lines = [l for l in piece.split("\n") if not l.startswith("--")]
        piece = "\n".join(lines).strip("\n")
        if not piece or piece in ("namespace HeightT2", "end HeightT2", "section HeightDefinitions",
                                     "end HeightDefinitions"):
            continue
        assert piece in hd, "height block piece not found verbatim in HeightT2/Defs.lean:\n" + piece
        checked += sum(1 for n in HEIGHT_DEFS if ("def " + n + " ") in piece)
    assert checked == len(HEIGHT_DEFS), checked
    start = ch.index("set_option autoImplicit false\n")
    body = ch[start:]
    holes = body.count("  sorry\n")
    assert holes == len(PROOFS) == 3, holes
    out = body
    for p in PROOFS:
        out = out.replace("  sorry\n", "  " + p + "\n", 1)
    back = out
    for p in PROOFS:
        back = back.replace("  " + p + "\n", "  sorry\n", 1)
    assert back == body
    assert "sorry" not in out
    open("Solution.lean", "w", encoding="utf-8").write(HEADER + out)
    print("Solution.lean written; 3 placeholders replaced; blocks checked")


if __name__ == "__main__":
    sys.exit(main())
