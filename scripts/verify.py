#!/usr/bin/env python3
"""Rebuild the delivered library and audit all owned declarations."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "verification/source-manifest.json").read_text())
mandatory = {"verification/AllAxioms.lean", "AlternatingAnalytic.lean", "lean-toolchain",
             "lakefile.toml", "lake-manifest.json", "scripts/verify.py",
             "challenge.lean", "solution.lean", "ChallengeDefinitions.lean",
             "verification/ChallengeEquivalence.lean", "comparator.json", "formalization.yaml"}
if not mandatory <= manifest.keys():
    raise SystemExit("Required proof, probe, or build files are missing from the authenticated inventory.")
for name, expected in manifest.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Source hash mismatch: {name}")
auxiliary_sources = {"solution.lean", "ChallengeDefinitions.lean", "verification/ChallengeEquivalence.lean"}
source_files = sorted((root / "AlternatingAnalytic").rglob("*.lean")) + [root / name for name in sorted(auxiliary_sources)]
expected_sources = {name for name in manifest if name.startswith("AlternatingAnalytic/") and name.endswith(".lean")} | auxiliary_sources
actual_sources = {str(path.relative_to(root)) for path in source_files}
if actual_sources != expected_sources:
    raise SystemExit("The delivered library source inventory has changed.")
expected_modules = {name.removesuffix(".lean").replace("/", ".")
                    for name in expected_sources | {"AlternatingAnalytic.lean"}}
probe = (root / "verification/AllAxioms.lean").read_text()
module_lists = re.findall(r"let mods : List Name := \[(.*?)\]", probe, re.S)
if len(module_lists) != 1:
    raise SystemExit("The probe has no unique owned-module inventory.")
probe_modules = [name.strip().removeprefix("`")
                 for name in module_lists[0].split(",") if name.strip()]
probe_imports = set(re.findall(r"^import ([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)$", probe, re.M)) - {"Lean"}
if (set(probe_modules) != expected_modules or len(probe_modules) != len(expected_modules)
        or probe_imports != expected_modules):
    raise SystemExit("The axiom probe does not cover every delivered library module.")
for path in source_files + [root / "AlternatingAnalytic.lean"]:
    if re.search(r"\b(sorry|admit|native_decide|axiom)\b", path.read_text()):
        raise SystemExit(f"Disallowed proof shortcut found: {path.relative_to(root)}")
logs = root / "work" / "verification"
logs.mkdir(parents=True, exist_ok=True)
for label, command in [("build", ["lake", "build"]),
                       ("axioms", ["lake", "env", "lean", "verification/AllAxioms.lean"])]:
    with (logs / f"{label}.log").open("w") as stream:
        result = subprocess.run(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"{label} failed; inspect {logs / (label + '.log')}")
text = (logs / "axioms.log").read_text()
counts = re.findall(r"ALL_DECLARATIONS_PROBE_OK decls=(\d+)", text)
if len(counts) != 1 or int(counts[0]) == 0:
    raise SystemExit("The exhaustive axiom probe did not complete.")
records = re.findall(r"^AUDITED_DECL ([^\r\n]+)$", text, re.M)
if len(records) != int(counts[0]) or len(set(records)) != len(records):
    raise SystemExit("The declaration records do not match the exhaustive probe count.")
groups = re.findall(r"AXIOMS_OF_ALL_DECLARATIONS\s*\[([^]]*)\]", text, re.S)
if len(groups) != 1:
    raise SystemExit("The complete transitive axiom set was not reported.")
axioms = {x.strip() for x in groups[0].split(",") if x.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if not axioms <= allowed:
    raise SystemExit(f"Unexpected axioms: {sorted(axioms - allowed)}")
print(f"Verified {len(expected_modules)} modules and {counts[0]} owned declarations; standard axioms only.")
