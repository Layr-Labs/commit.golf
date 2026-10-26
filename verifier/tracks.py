"""Trusted track identifiers used by the runner, fetcher, and challenge generator."""
TRACKS = {
    "ideal-permutation": "idealPermutation",
    "ideal-compression": "idealCompression",
    "random-oracle": "randomOracle",
}


def track_constructor(track: str) -> str:
    if track not in TRACKS:
        raise ValueError(f"unknown track: {track!r}")
    return TRACKS[track]


def submission_path(track: str) -> str:
    track_constructor(track)
    return f"submissions/{track}"
