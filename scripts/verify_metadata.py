#!/usr/bin/env python3
"""Validate release metadata and agreement of the 22 published theorem lists.

Install PyYAML and jsonschema, then run from the checkout root:
    python3 scripts/verify_metadata.py --root .
    python3 scripts/verify_metadata.py --root . --axiom-log axioms.log
The official schema is fetched at the immutable revision below; failure to
retrieve or validate it fails the check rather than skipping validation.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import json
from pathlib import Path
import re
import sys
from urllib.request import urlopen

import jsonschema
import yaml

from verify_modules import declarations

SCHEMA_REVISION = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
SCHEMA_BASE = ("https://raw.githubusercontent.com/mathlib-initiative/"
               f"formalization.yaml/{SCHEMA_REVISION}/schema/")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREM_COUNT = 22


def require(condition, message):
    if not condition:
        raise ValueError(message)


def schema_for(version):
    def fetch(name):
        with urlopen(SCHEMA_BASE + name, timeout=30) as response:
            return json.load(response)

    dispatcher = fetch("formalization.schema.json")
    require(version in dispatcher["properties"]["version"]["enum"],
            f"Unsupported formalization schema version: {version!r}")
    require(isinstance(version, str) and re.fullmatch(r"v\d+\.\d+", version),
            "Invalid schema version")
    schema = fetch(version + ".schema.json")
    # The reviewed version schemas use only fragment references. Refuse a
    # future external reference instead of fetching an unpinned resource.
    def check_refs(value):
        if isinstance(value, dict):
            if "$ref" in value:
                require(value["$ref"].startswith("#"), "Unpinned external schema reference")
            for child in value.values():
                check_refs(child)
        elif isinstance(value, list):
            for child in value:
                check_refs(child)
    check_refs(schema)
    return schema


def unique(values, label):
    require(len(values) == THEOREM_COUNT, f"{label}: expected {THEOREM_COUNT} entries")
    require(len(set(values)) == len(values), f"{label}: duplicate entry")
    return set(values)


def published_theorems(root, metadata):
    text = (root / "docs/main-results.md").read_text()
    files = re.findall(
        r"(?m)^\d+\. .*?\]\(\.\./(Critical2DKPZStatements/[A-Za-z0-9_]+\.lean)\)", text)
    unique(files, "docs/main-results.md")
    expected = []
    modules = []
    for file in files:
        source = (root / file).read_text()
        names = [name for kind, name, public in declarations(source)
                 if public and kind in ("theorem", "lemma")]
        require(len(names) == 1, f"{file}: expected one written public theorem")
        expected.extend(names)
        modules.append(file[:-5].replace("/", "."))
    expected_set = unique(expected, "published theorem exports")
    module_set = unique(modules, "published statement modules")
    aligned = metadata["alignment"]["statements"]
    require(unique([s["lean"] for s in aligned], "metadata exports") == expected_set,
            "Metadata theorem exports differ from docs/main-results.md")
    require(unique([s["module"] for s in aligned], "metadata modules") == module_set,
            "Metadata modules differ from docs/main-results.md")
    require({(s["module"], s["lean"]) for s in aligned} == set(zip(modules, expected)),
            "Metadata module/export pairs differ from the written statements")
    require(all(s["status"] == "proved" for s in aligned), "Published theorem status is not proved")
    prints = re.findall(r"(?m)^#print axioms (\S+)",
                        (root / "scripts/PrintAxioms.lean").read_text())
    require(unique(prints, "PrintAxioms exports") == expected_set,
            "PrintAxioms exports differ from the published theorems")
    program = ast.parse((root / "scripts/print_axioms").read_text())
    constants = {}
    for node in program.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1 and
                isinstance(node.targets[0], ast.Name) and
                node.targets[0].id in ("MODULES", "EXPORTS")):
            require(node.targets[0].id not in constants, "Duplicate axiom-runner constant")
            constants[node.targets[0].id] = ast.literal_eval(node.value)
    require(unique(constants["MODULES"], "axiom-runner modules") == module_set,
            "Axiom runner modules differ from the published statements")
    require(unique(constants["EXPORTS"], "axiom-runner exports") == expected_set,
            "Axiom runner exports differ from the published theorems")
    return expected_set


def check_axiom_log(text, expected):
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    reports += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    counts = Counter(name for name, _ in reports)
    require(set(counts) == expected and all(n == 1 for n in counts.values()),
            "Incomplete, duplicated or unexpected theorem axiom report")
    for name, axioms in reports:
        unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED_AXIOMS
        require(not unexpected, f"{name}: unexpected axioms {sorted(unexpected)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--axiom-log", type=Path)
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        metadata = yaml.safe_load((root / "formalization.yaml").read_text())
        require(isinstance(metadata, dict), "Metadata must be a YAML mapping")
        schema = schema_for(metadata.get("version"))
        validator = jsonschema.validators.validator_for(schema)
        validator.check_schema(schema)
        validator(schema).validate(metadata)
        expected = published_theorems(root, metadata)
        if args.axiom_log:
            check_axiom_log(args.axiom_log.read_text(), expected)
            print(f"AXIOM REPORT OK ({len(expected)} published theorems)")
        print(f"RELEASE METADATA OK ({len(expected)} theorems; schema {SCHEMA_REVISION})")
    except (OSError, ValueError, KeyError, TypeError, jsonschema.exceptions.ValidationError,
            jsonschema.exceptions.SchemaError) as error:
        print(f"RELEASE METADATA FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
