#!/usr/bin/env python3
"""Check this submission's configuration, statement surface, and vendor hashes.

Run before the Lean build and Comparator. This complements, rather than replaces,
Palomar's current verifier and metadata-schema validation.
"""
import argparse
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_files(base, records, hash_key):
    paths = set()
    for row in records:
        path = base / row["path"]
        require(path.is_file() and not path.is_symlink(), f"Missing regular source: {path}")
        require(digest(path) == row[hash_key], f"Source hash mismatch: {path}")
        paths.add(path.relative_to(base).as_posix())
    actual = {p.relative_to(base).as_posix() for p in base.rglob("*.lean")}
    require(paths == actual, f"Source inventory mismatch: {base}")
    return len(paths)


def check_dependency(manifest, specs, package, namespace, record_file, check_sources):
    provenance = json.loads((ROOT / "paper" / record_file).read_text())
    spec = next(p for p in specs if p["name"] == package)
    locked = next(p for p in manifest["packages"] if p["name"] == package)
    require(spec["rev"] == locked["rev"] == provenance["revision"] and
            spec["git"] == locked["url"] == provenance["source"],
            f"{package} pin differs between configuration, manifest, and provenance")
    expected = {row["path"].removesuffix(".lean").replace("/", ".")
                for row in provenance["files"]}
    audit = (ROOT / "scripts/CheckAxioms.lean").read_text()
    require(set(re.findall(r"^import all (" + re.escape(namespace) + r"\.\S+)$", audit, re.M))
            == expected, f"Axiom audit must import every recorded {package} dependency module")
    if check_sources:
        base = ROOT / manifest["packagesDir"] / package
        revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=base,
                                  capture_output=True, text=True, check=True).stdout.strip()
        require(revision == provenance["revision"], f"Fetched {package} revision differs from pin")
        for row in provenance["files"]:
            path = base / row["path"]
            require(path.is_file() and not path.is_symlink() and digest(path) == row["sha256"],
                    f"{package} dependency hash mismatch: {path}")
        # Every imported module in this namespace must belong to the audited inventory.
        # Include local consumers so a new direct dependency cannot escape the audit.
        sources = [base / row["path"] for row in provenance["files"]]
        sources.extend((ROOT / "BretecheTenenbaumMean").rglob("*.lean"))
        for source in sources:
            imports = re.findall(r"^(?:public )?import (?:all )?(" +
                                 re.escape(namespace) + r"\.\S+)", source.read_text(), re.M)
            require(set(imports) <= expected, f"Unaudited {package} import in {source}")
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-dependencies", action="store_true",
                        help="also verify fetched dependency sources after lake build/update")
    args = parser.parse_args()
    config = json.loads((ROOT / "comparator.json").read_text())
    require(set(config) == {"challenge_module", "solution_module", "theorem_names",
                            "definition_names", "permitted_axioms"}, "Unexpected Comparator fields")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "Unexpected statement/solution modules")
    require(config["definition_names"] == [], "This submission must have no definition holes")
    require(set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
            "Unexpected permitted axioms")
    challenge = (ROOT / "Challenge.lean").read_text()
    require(len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000,
            "Challenge exceeds Palomar's hard size limit")
    require(re.findall(r"^(?:public )?import (.+)$", challenge, re.M) == ["Mathlib"],
            "Challenge must import only Mathlib")
    names = re.findall(r"^theorem (\w+)", challenge, re.M)
    require(config["theorem_names"] == ["BretecheTenenbaumMean." + n for n in names],
            "Comparator must compare every Challenge theorem")
    require(len(names) == 10 and challenge.count("by sorry") == 10,
            "Expected exactly ten deliberate theorem-proof holes")
    definitions = (ROOT / "BretecheTenenbaumMean/Definitions.lean").read_text()
    # This ordinary, fully specified block is duplicated intentionally for Comparator.
    statement_block = challenge.split("namespace BretecheTenenbaumMean\n", 1)[1].split(
        "/-- Theorem 1.1: ordinary mean", 1)[0]
    proof_block = definitions.split("namespace BretecheTenenbaumMean\n", 1)[1].split(
        "end BretecheTenenbaumMean", 1)[0]
    require(statement_block == proof_block, "Challenge and Definitions blocks diverged")
    require("import Challenge" not in (ROOT / "Solution.lean").read_text(),
            "Solution must not import the deliberate Challenge holes")
    counts = []
    snapshot = json.loads((ROOT / "vendor/strong-pnt/SNAPSHOT.json").read_text())
    counts.append(check_files(ROOT / "vendor/strong-pnt",
        [{"path": p, "sha256": h} for p, h in snapshot["files"].items()], "sha256"))
    for row in json.loads((ROOT / "paper/SIEVE_SOURCES.json").read_text())["files"]:
        require(digest(ROOT / row["destination"]) == row["destination_sha256"],
                f"Adapted sieve source changed: {row['destination']}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    require(all(p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
                for p in manifest["packages"]), "Dependencies must have immutable Git revisions")
    specs = tomllib.loads((ROOT / "lakefile.toml").read_text())["require"]
    nair_count = check_dependency(manifest, specs, "nair_tenenbaum", "NairTenenbaum",
                                  "NAIR_TENENBAUM_SOURCES.json", args.check_dependencies)
    tau_count = check_dependency(manifest, specs, "TauCeti", "TauCeti",
                                 "TAU_CETI_SOURCES.json", args.check_dependencies)
    require(not (ROOT / "vendor/nair-tenenbaum").exists(), "Obsolete Nair–Tenenbaum vendor copy remains")
    require(not (ROOT / "vendor/tau-ceti").exists(), "Obsolete Tau Ceti vendor copy remains")
    # Ensure a normal git add will retain every required submission/provenance file.
    required = ["Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml",
                "LICENSE", "lake-manifest.json", "lean-toolchain"] + [
                    str(p.relative_to(ROOT)) for p in (ROOT / "paper").glob("*.json")]
    ignored = subprocess.run(["git", "check-ignore", "--", *required], cwd=ROOT,
                             capture_output=True, text=True)
    require(ignored.returncode in (0, 1), ignored.stderr)
    require(not ignored.stdout, "Required files are ignored:\n" + ignored.stdout)
    print(f"Palomar preflight: {len(names)} theorems, Mathlib-only Challenge, "
          f"{sum(counts)} vendor modules and 6 adapted sieve files verified; "
          f"dependency pins and audit inventories verified "
          f"({nair_count} Nair–Tenenbaum, {tau_count} Tau Ceti modules)")
    if args.check_dependencies:
        print(f"Fetched dependencies: {nair_count + tau_count} source hashes verified")


if __name__ == "__main__":
    main()
