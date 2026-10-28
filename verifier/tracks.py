"""Trusted track identifiers used by the runner, fetcher, and challenge generator."""
TRACKS = {
    "ideal-permutation": "idealPermutation",
    "ideal-compression": "idealCompression",
    "random-oracle-fixed-output": "randomOracleFixedOutput",
    "ideal-xof": "idealXof",
}

# Each hiding variant requires its own certificate and submission surface.
HIDING_TRACKS = {f"{name}-hiding": constructor for name, constructor in TRACKS.items()}
TRACKS.update(HIDING_TRACKS)
CERTIFICATES = {
    name: constructor[0].upper() + constructor[1:] +
    ("HidingCertificate" if name in HIDING_TRACKS else "Certificate")
    for name, constructor in TRACKS.items()
}


def certificate_name(track: str) -> str:
    track_constructor(track)
    return CERTIFICATES[track]


def track_constructor(track: str) -> str:
    if track not in TRACKS:
        raise ValueError(f"unknown track: {track!r}")
    return TRACKS[track]


def submission_path(track: str) -> str:
    track_constructor(track)
    return f"submissions/{track}"
