"""Trusted track configuration; candidates cannot choose oracle widths or prices."""
from dataclasses import dataclass
from pathlib import Path
import shutil


@dataclass(frozen=True)
class Track:
    submission: str
    score_path: str
    pareto: bool
    permutation_cycles: int
    compression_input_bytes: int = 64


TRACKS = {
    "product": Track("submission", "scripts/score.json", False, 8),
    "pareto": Track("submission-pareto", "scripts/pareto/score.json", True, 8),
    "commit-golf-64-32-product": Track(
        "submission-commit-golf-64-32-product",
        "scripts/commit-golf-64-32-product/score.json", False, 30,
    ),
    "commit-golf-64-32-pareto": Track(
        "submission-commit-golf-64-32-pareto",
        "scripts/commit-golf-64-32-pareto/score.json", True, 30,
    ),
    "commit-golf-96-32-product": Track(
        "submission-commit-golf-96-32-product",
        "scripts/commit-golf-96-32-product/score.json", False, 30, 96,
    ),
    "commit-golf-96-32-pareto": Track(
        "submission-commit-golf-96-32-pareto",
        "scripts/commit-golf-96-32-pareto/score.json", True, 30, 96,
    ),
}


def prepare_contract(project: Path, track: Track) -> None:
    """Select width and price in the isolated trusted source, invalidating old builds.

    The repository contract retains 64-byte compression and eight-cycle permutation.
    Dependency package caches do not depend on CommitGolf and can be reused; the
    project's own build cannot. Compression output stays 32 bytes and costs eight.
    """
    parameters = project / "CommitGolf/Parameters.lean"
    source = parameters.read_text()
    original = "def PERMUTATION_CYCLES : Nat := 8"
    if source.splitlines().count(original) != 1:
        raise ValueError("expected the canonical eight-cycle permutation definition")
    width = "def COMPRESSION_INPUT_LENGTH : Nat := 512"
    if source.splitlines().count(width) != 1:
        raise ValueError("expected the canonical 512-bit compression input definition")
    selected = source.replace(original, f"def PERMUTATION_CYCLES : Nat := {track.permutation_cycles}")
    selected = selected.replace(width, f"def COMPRESSION_INPUT_LENGTH : Nat := {8 * track.compression_input_bytes}")
    if selected != source:
        parameters.write_text(selected)
        build = project / ".lake/build"
        if build.exists():
            shutil.rmtree(build)
