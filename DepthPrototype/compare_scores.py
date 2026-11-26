"""Synthetic scoring comparisons, not a verifier or measurements of live entries."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations


@dataclass(frozen=True)
class Example:
    """Assumed exact costs of a hypothetical example, not submission bounds.

    This helper does not validate a DAG witness for these synthetic numbers.
    """
    name: str
    work: int
    proof_bytes: int
    oracle_rounds: int
    span: int

    def __post_init__(self):
        if any(type(x) is not int or x < 0 for x in
               (self.work, self.proof_bytes, self.oracle_rounds, self.span)):
            raise ValueError("example metrics must be nonnegative integers")
        if self.span > self.work:
            raise ValueError("span cannot exceed work in this example DAG model")

    def point(self, depth_model: str):
        if depth_model not in ("oracle_rounds", "span"):
            raise ValueError("unknown depth model")
        return (self.work, self.proof_bytes, getattr(self, depth_model))


def dominates(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    if len(left) != len(right):
        raise ValueError("objective dimensions differ")
    return all(a <= b for a, b in zip(left, right)) and any(
        a < b for a, b in zip(left, right))


def weighted_round_preference(example: Example, cycles_per_round: int):
    """Explicit preference; this expression is NOT a parallel-runtime bound."""
    if type(cycles_per_round) is not int or cycles_per_round < 0:
        raise ValueError("weight must be a nonnegative integer")
    return example.proof_bytes * (
        example.work + cycles_per_round * example.oracle_rounds)


def ideal_span_envelope(example: Example, workers: int):
    """Conditional ideal unit-DAG bounds for assumed EXACT example costs.

    The upper expression is intentionally loose. Its scheduler/DAG assumptions
    must be established before using it as a certified challenge metric.
    Independently certified work/span UPPER bounds cannot be used to establish
    the lower expression (or their ratio as certified parallelism).
    """
    if type(workers) is not int or workers <= 0:
        raise ValueError("worker count must be a positive integer")
    lower = max(Fraction(example.work, workers), example.span)
    upper = Fraction(example.work, workers) + example.span
    return lower, upper


EXAMPLES = (
    Example("parallel-friendly", 1_000_000, 1024, 1000, 100_000),
    Example("few-rounds-serial-cpu", 1_250_000, 1100, 10, 900_000),
    Example("low-span-high-work", 100_000_000, 1024, 10, 10_000),
)


def unit_dag_metrics(predecessors: tuple[frozenset[int], ...]):
    """Exact small-example DAG work/span; labels must be topologically ordered."""
    finish = []
    for node, before in enumerate(predecessors):
        if any(type(p) is not int or p < 0 or p >= node for p in before):
            raise ValueError("expected a topologically ordered DAG")
        finish.append(1 + max((finish[p] for p in before), default=0))
    return len(predecessors), max(finish, default=0)


def minimum_unit_schedule(predecessors: tuple[frozenset[int], ...], workers: int):
    """Exhaustive toy reference; not a scalable scheduler or a verified backend."""
    unit_dag_metrics(predecessors)
    if type(workers) is not int or workers <= 0:
        raise ValueError("worker count must be a positive integer")
    if len(predecessors) > 12:
        raise ValueError("toy reference is capped at twelve tasks")
    states = {frozenset()}
    target = frozenset(range(len(predecessors)))
    ticks = 0
    while target not in states:
        next_states = set()
        for done in states:
            ready = [i for i, deps in enumerate(predecessors)
                     if i not in done and deps <= done]
            for count in range(1, min(workers, len(ready)) + 1):
                for selected in combinations(ready, count):
                    next_states.add(done | frozenset(selected))
        if not next_states:
            raise ValueError("DAG makes no progress")
        states = next_states
        ticks += 1
    return ticks


if __name__ == "__main__":
    import json
    print(json.dumps({
        "scope": "Synthetic examples only; no live-entry measurements or acceptance",
        "objective_order": ["work", "proofBytes", "depth"],
        "examples": [dict(name=e.name, round_point=e.point("oracle_rounds"),
                          span_point=e.point("span"),
                          weighted_round_preferences={str(w): weighted_round_preference(e, w)
                                                      for w in (0, 100, 10_000)},
                          ideal_64_worker_envelope=[str(x) for x in ideal_span_envelope(e, 64)])
                     for e in EXAMPLES],
        "runtime_claim": "None: oracle rounds do not measure serial local work, and the ideal DAG envelope still needs an executable/scheduler bridge.",
    }, indent=2))
