"""Trusted score arithmetic; prices and cycle proofs are enforced by the Lean certificate."""

from depth_profiles import depth_profile

CLAIM_KEYS = ("proofBytes", "commitCycles", "openingCycles")
MAX_SCORE = 2**53 - 1


def score_claim(value: dict) -> int:
    if not isinstance(value, dict) or set(value) != set(CLAIM_KEYS):
        raise ValueError("claim.json must contain exactly proofBytes, commitCycles and openingCycles")
    if any(type(value[key]) is not int or value[key] < 0 for key in CLAIM_KEYS):
        raise ValueError("score claims must be nonnegative decimal integers")
    if any(value[key] > MAX_SCORE for key in CLAIM_KEYS):
        raise ValueError("score claim exceeds 2^53 - 1")
    size = value["proofBytes"]
    cycles = value["commitCycles"] + value["openingCycles"]
    score = size * cycles
    if max(size, cycles, score) > MAX_SCORE:
        raise ValueError("combined score or metric exceeds 2^53 - 1")
    return score


def depth_objectives(value: dict, model: str) -> list[int]:
    """Validate the exact selected certificate bounds and ordered Pareto point.

    The six existing tracks retain score_claim's product admission cap. Depth
    tracks bound each integer and each objective; an unranked triple product is
    neither computed nor used as a hidden admission condition.
    """
    profile = depth_profile(model)
    if type(value) is not dict or set(value) != set(profile.claim_keys):
        raise ValueError("depth claim must contain exactly " + ", ".join(profile.claim_keys))
    if any(type(value[key]) is not int or not 0 <= value[key] <= MAX_SCORE
           for key in profile.claim_keys):
        raise ValueError("depth claims must be nonnegative integers at most 2^53 - 1")
    work = sum(value[key] for key in profile.work_fields)
    depth = sum(value[key] for key in profile.depth_fields)
    point = [work, value["proofBytes"], depth]
    if max(point) > MAX_SCORE:
        raise ValueError("combined depth objective exceeds 2^53 - 1")
    return point
