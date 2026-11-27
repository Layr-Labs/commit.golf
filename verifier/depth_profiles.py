"""Fixed resource contracts for depth tracks; never selected by candidate data."""
from dataclasses import dataclass


@dataclass(frozen=True)
class DepthProfile:
    namespace: str
    execution_modes: tuple[str, ...]
    work_fields: tuple[str, str]
    depth_fields: tuple[str, str]
    work_metric: str
    depth_metric: str
    version: str
    template: str

    @property
    def claim_keys(self) -> tuple[str, ...]:
        return ("proofBytes", *self.work_fields, *self.depth_fields)

    @property
    def objectives(self) -> tuple[str, ...]:
        return (self.work_metric, "proofBytes", self.depth_metric)


DEPTH_PROFILES = {
    "oracle-rounds": DepthProfile(
        "CommitGolfDepth.Rounds", ("legacy", "batched"),
        ("commitCycles", "openingCycles"), ("commitRounds", "openingRounds"),
        "proverCycles", "oracleRounds", "oracle-rounds-v1", "RoundsChallenge.lean.in",
    ),
    "work-span": DepthProfile(
        "CommitGolfDepth.Span", ("legacy", "forkJoin"),
        ("commitWork", "openingWork"), ("commitSpan", "openingSpan"),
        "proverWork", "proverSpan", "fork-join-span-v1", "SpanChallenge.lean.in",
    ),
}


def depth_profile(name: str) -> DepthProfile:
    if type(name) is not str or name not in DEPTH_PROFILES:
        raise ValueError("unknown depth resource model")
    return DEPTH_PROFILES[name]
