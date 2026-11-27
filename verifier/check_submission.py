#!/usr/bin/env python3
"""Validate a frozen submission tree before any candidate Lean is compiled."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from artifact import load_artifact, unique_object, reject_constant

MAX_FILES = 1000
MAX_FILE_BYTES = 8 * 1024 * 1024
MAX_TOTAL_BYTES = 32 * 1024 * 1024
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
INTEGER = re.compile(r"0|[1-9][0-9]*")
from scoring import score_claim, depth_objectives
from depth_profiles import DEPTH_PROFILES, depth_profile
ALLOWED_LIBRARIES = ("Mathlib", "ToMathlib", "VCVio", "Batteries", "Lean", "Init", "Std", "RiscvZkvm", "ArkLib", "CompPoly")
ALLOWED_CONTRACT = {"CommitGolf", "CommitGolf.Parameters", "CommitGolf.Oracle", "CommitGolf.Scheme",
                    "CommitGolf.Honest", "CommitGolf.Binding", "CommitGolf.Hiding", "CommitGolf.Statements",
                    "CommitGolf.Riscv", "CommitGolf.Programs", "CommitGolf.Artifact",
                    "CommitGolf.ArtifactEncoding"}


def strip_comments(source: str) -> str:
    """Remove nested block and line comments while retaining newlines and token gaps."""
    out = []
    i = depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)


def imports(source: str) -> list[str]:
    found = []
    for line in strip_comments(source).lstrip("\ufeff").splitlines():
        line = line.strip()
        if not line:
            continue
        if re.match(r"(prelude|module|public|private|meta)\b", line):
            raise ValueError("alternate module headers are not allowed")
        if line.startswith("import"):
            parts = line.split()
            if len(parts) != 2 or not MODULE.fullmatch(parts[1]):
                raise ValueError("each import must name one ordinary ASCII module")
            found.append(parts[1])
            continue
        break
    return found


def claim(path: Path, *, resource_model: str | None = None) -> dict[str, int]:
    raw = path.read_bytes()
    if len(raw) > 512:
        raise ValueError("claim.json exceeds 512 bytes")
    value = (json.loads(raw) if resource_model is None else
             json.loads(raw, object_pairs_hook=unique_object, parse_constant=reject_constant))
    if resource_model is None:
        score_claim(value)
    else:
        depth_objectives(value, resource_model)
    return value


def check(root: Path, *, resource_model: str | None = None) -> dict:
    profile = depth_profile(resource_model) if resource_model is not None else None
    errors = []
    if root.is_symlink() or not root.is_dir():
        return {"ok": False, "errors": ["submission root is not a directory"]}
    files = sorted(root.rglob("*"))
    if len(files) > MAX_FILES:
        errors.append(f"more than {MAX_FILES} entries")
    total = 0
    for path in files:
        rel = path.relative_to(root)
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            errors.append(f"{rel}: symlinks and special files are forbidden")
            continue
        if path.is_dir():
            if rel.parts[0] != "CommitGolfCandidate":
                errors.append(f"{rel}: only CommitGolfCandidate/ may contain modules")
            continue
        if rel.as_posix() not in {"Solution.lean", "claim.json", "programs.json", "README.md"} and not (
            rel.parts[0] == "CommitGolfCandidate" and path.suffix == ".lean" and
            all(MODULE.fullmatch(part) for part in rel.with_suffix("").parts)):
            errors.append(f"{rel}: only Solution.lean, claim.json, programs.json, README.md, and CommitGolfCandidate modules are admitted")
            continue
        size = path.stat().st_size
        total += size
        if size > MAX_FILE_BYTES:
            errors.append(f"{rel}: file exceeds 8 MiB")
    if total > MAX_TOTAL_BYTES:
        errors.append("submission exceeds 32 MiB")
    if not (root / "Solution.lean").is_file():
        errors.append("Solution.lean is required")
    try:
        values = claim(root / "claim.json", resource_model=resource_model)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        values = None
        errors.append(f"invalid claim.json: {exc}")
    try:
        artifact_digest = load_artifact(root / 'programs.json', resource_model=resource_model).digest
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        artifact_digest = None
        errors.append(f"invalid programs.json: {exc}")
    modules = {".".join(path.relative_to(root).with_suffix("").parts)
               for path in files if path.is_file() and path.suffix == ".lean"}
    for path in files:
        if not path.is_file() or path.suffix != ".lean":
            continue
        try:
            source = path.read_text(encoding="utf-8")
            for module in imports(source):
                depth_import = profile is not None and (
                    module == profile.namespace or module.startswith(profile.namespace + "."))
                if module in ALLOWED_CONTRACT or depth_import or module in modules or any(
                    module == library or module.startswith(library + ".") for library in ALLOWED_LIBRARIES):
                    continue
                errors.append(f"{path.relative_to(root)}: import {module} is outside the allowed modules")
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"{path.relative_to(root)}: invalid Lean source: {exc}")
    result = {"ok": not errors, "claim": values, "artifactDigest": artifact_digest,
              "score": score_claim(values) if values is not None and profile is None else None,
              "files": len(files), "bytes": total, "errors": errors}
    if profile is not None:
        result.update(resource_model=profile.version,
                      scores=depth_objectives(values, resource_model) if values is not None else None)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--resource-model", choices=tuple(DEPTH_PROFILES))
    args = parser.parse_args()
    result = check(args.root, resource_model=args.resource_model)
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)
