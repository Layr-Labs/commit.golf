"""Trusted score arithmetic; prices and cycle proofs are enforced by the Lean certificate."""

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
