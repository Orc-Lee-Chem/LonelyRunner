"""Trusted negative controls and fail-closed result classification.

Constructing/compiling these controls is not an official rejection result.
"""
import re

TARGETS = ["LonelyRunnerAcceptance.explicit_gap", "LonelyRunnerAcceptance.uniform_gap"]
NEGATIVES = ["weak_target", "changed_definition", "sorry_dependency", "extra_condition"]

def negative_source(kind, challenge):
    first = challenge.index("theorem explicit_gap")
    second = challenge.index("theorem uniform_gap")
    end = challenge.rindex("end LonelyRunnerAcceptance")
    header = challenge[:first]
    explicit = challenge[first:second].split(":= by", 1)[0].rstrip()
    uniform = challenge[second:end].split(":= by", 1)[0].rstrip()
    tail = "\nend LonelyRunnerAcceptance\n"
    if kind == "weak_target":
        return header + """theorem explicit_gap (V : Finset ℕ)
    (hpos : ∀ v ∈ V, 0 < v) (hn : 2 ≤ V.card) : True := by
  trivial

theorem uniform_gap : True := by
  trivial
""" + tail
    if kind == "changed_definition":
        return header + """local instance acceptanceBadLT : LT ℝ where
  lt := fun _ _ => True

""" + explicit + """ := by
  refine ⟨(0 : ℝ), le_rfl, ?_, ?_⟩
  · change True
    trivial
  · intro v hv k
    change True
    trivial

""" + uniform + """ := by
  refine ⟨(0 : ℝ), ?_, ?_⟩
  · change True
    trivial
  · intro V hpos hn
    exact explicit_gap V hpos hn
""" + tail
    if kind == "sorry_dependency":
        return challenge
    if kind == "extra_condition":
        explicit = explicit.replace("theorem explicit_gap", "theorem explicit_gap (h : False)", 1)
        uniform = uniform.replace("theorem uniform_gap", "theorem uniform_gap (h : False)", 1)
        return header + explicit + " := by\n  exact False.elim h\n\n" + uniform + " := by\n  exact False.elim h\n" + tail
    raise ValueError("Unknown negative control: " + kind)

def progress_reached_comparison(output):
    lines = output.splitlines()
    searches = [
        lambda s: s.strip() == "Building Challenge",
        lambda s: s.startswith("Exporting ") and s.rstrip().endswith(" from Challenge"),
        lambda s: s.strip() == "Building Solution",
        lambda s: s.startswith("Exporting ") and s.rstrip().endswith(" from Solution"),
    ]
    cursor = 0
    for predicate in searches:
        found = next((i for i in range(cursor, len(lines)) if predicate(lines[i])), None)
        if found is None:
            return False
        cursor = found + 1
    return True

def classify(kind, exit_code, output, termination=None):
    if termination:
        return {"status": "INCOMPLETE", "reason": termination}
    if not progress_reached_comparison(output):
        return {"status": "ERROR", "reason": "Comparison was not reached after both builds and exports"}
    if kind == "positive":
        required = ["Your solution is okay!", "Lean default kernel accepts the solution",
                    "nanoda kernel accepts the solution", *TARGETS]
        success = re.search(r"(?m)^Checked (\d+) declarations with no errors\s*$", output)
        if exit_code == 0 and all(s in output for s in required) and success:
            return {"status": "PASS", "checked_declarations": int(success[1]),
                    "targets": {t: "PASS" for t in TARGETS}}
        return {"status": "ERROR", "reason": "Positive comparison or one kernel did not complete successfully"}
    if kind not in NEGATIVES:
        raise ValueError(kind)
    if exit_code == 0 or "Your solution is okay!" in output:
        return {"status": "ERROR", "reason": "A negative control was accepted"}
    mismatch = any("Challenge and solution theorem statement do not match: '" + t + "'" in output
                   for t in TARGETS)
    if kind in {"weak_target", "extra_condition"}:
        expected = mismatch
    elif kind == "changed_definition":
        expected = mismatch or ("acceptanceBadLT" in output and
                   any(s in output for s in ["Const does not match between challenge and target",
                                             "Const not found in challenge"]))
    else:
        expected = "Illegal axiom detected: 'sorryAx'" in output
    if expected:
        return {"status": "EXPECTED_REJECTION", "reason": kind}
    return {"status": "ERROR", "reason": "No required semantic rejection diagnostic"}
