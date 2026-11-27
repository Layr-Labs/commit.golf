"""Trusted track configuration; candidates cannot choose oracle widths or prices."""
from dataclasses import dataclass
from pathlib import Path
import shutil

from depth_profiles import depth_profile


@dataclass(frozen=True)
class Track:
    submission: str
    score_path: str
    pareto: bool
    permutation_cycles: int
    compression_input_bytes: int = 64
    depth_model: str | None = None

    def __post_init__(self):
        if self.depth_model is not None:
            depth_profile(self.depth_model)
            if not self.pareto:
                raise ValueError("depth resource contracts currently require Pareto scoring")


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
    "commit-golf-oracle-rounds-pareto": Track(
        "submission-commit-golf-oracle-rounds-pareto",
        "scripts/commit-golf-oracle-rounds-pareto/score.json", True, 8,
        depth_model="oracle-rounds",
    ),
    "commit-golf-work-span-pareto": Track(
        "submission-commit-golf-work-span-pareto",
        "scripts/commit-golf-work-span-pareto/score.json", True, 8,
        depth_model="work-span",
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
