"""Decode delivered machine bytes and generate their trusted Lean submission value."""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import stat

MAX_MANIFEST_BYTES = 8 * 1024 * 1024
MAX_PROGRAM_BYTES = 2**20
MEMORY_BYTES = 2**36
STEP_LIMIT = 2**48
PROGRAMS = ('commit', 'opening', 'check')
SIZE_FIELDS = ('trapdoor', 'proof')
LAYOUT_FIELDS = ('message', 'commitment', 'trapdoor', 'indices', 'values', 'proof')
HEX_BYTES = re.compile(r'(?:[0-9a-f]{2})*')


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f'duplicate manifest key: {key}')
        value[key] = item
    return value


def reject_constant(value):
    raise ValueError(f'invalid JSON constant: {value}')


def exact_object(value, keys, label):
    if type(value) is not dict or set(value) != set(keys):
        raise ValueError(f'{label} must contain exactly {", ".join(keys)}')
    return value


def natural(value, maximum, label, minimum=0):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f'{label} must be an integer in [{minimum}, {maximum}]')
    return value


def decode_hex(value, label):
    if type(value) is not str or not HEX_BYTES.fullmatch(value):
        raise ValueError(f'{label} must be lowercase hexadecimal whole bytes')
    return bytes.fromhex(value)


@dataclass(frozen=True)
class Image:
    code: tuple[int, ...]
    data: bytes


@dataclass(frozen=True)
class Artifact:
    raw: bytes
    sizes: tuple[int, ...]
    layout: tuple[int, ...]
    steps: tuple[int, ...]
    images: tuple[Image, ...]

    @property
    def digest(self):
        """SHA-256 of the exact delivered manifest, including its formatting."""
        return hashlib.sha256(self.raw).hexdigest()

    def lean_source(self):
        """Only validated integers enter generated code; solver source is never interpolated."""
        lines = ['import CommitGolf.Programs', '', 'namespace CommitGolf.Artifact', '',
                 '/-- Exact machine bytes and ABI decoded from submission/programs.json. -/',
                 'def submission : CommitGolf.Submission where',
                 '  sizes := ⟨' + ', '.join(map(str, self.sizes)) + '⟩',
                 '  layout := ⟨' + ', '.join(map(str, self.layout)) + '⟩',
                 '  image']
        for name, image in zip(PROGRAMS, self.images):
            code = '[' + ', '.join(map(str, image.code)) + ']'
            data = '[' + ', '.join(map(str, image.data)) + ']'
            lines.append(f'    | .{name} => ⟨{code}, {data}⟩')
        lines.append('  steps')
        lines.extend(f'    | .{name} => {steps}' for name, steps in zip(PROGRAMS, self.steps))
        lines.extend(['', 'end CommitGolf.Artifact', ''])
        return '\n'.join(lines)


def parse_artifact(raw: bytes) -> Artifact:
    if len(raw) > MAX_MANIFEST_BYTES:
        raise ValueError('programs.json exceeds 8 MiB')
    try:
        value = json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                           parse_constant=reject_constant)
    except RecursionError as exc:
        raise ValueError('manifest nesting is too deep') from exc
    exact_object(value, ('schemaVersion', 'sizes', 'layout', 'steps', 'images'), 'manifest')
    if type(value['schemaVersion']) is not int or value['schemaVersion'] != 1:
        raise ValueError('schemaVersion must be the integer 1')
    sizes = exact_object(value['sizes'], SIZE_FIELDS, 'sizes')
    layout = exact_object(value['layout'], LAYOUT_FIELDS, 'layout')
    steps = exact_object(value['steps'], PROGRAMS, 'steps')
    images = exact_object(value['images'], PROGRAMS, 'images')
    parsed_images = []
    for name in PROGRAMS:
        image = exact_object(images[name], ('code', 'data'), f'images.{name}')
        code = decode_hex(image['code'], f'images.{name}.code')
        data = decode_hex(image['data'], f'images.{name}.data')
        if len(code) % 4:
            raise ValueError(f'images.{name}.code must contain complete 32-bit instructions')
        if len(code) + len(data) >= MAX_PROGRAM_BYTES:
            raise ValueError(f'images.{name} must be smaller than 1 MiB')
        words = tuple(int.from_bytes(code[i:i+4], 'little') for i in range(0, len(code), 4))
        parsed_images.append(Image(words, data))
    return Artifact(raw,
        tuple(natural(sizes[key], MEMORY_BYTES, f'sizes.{key}') for key in SIZE_FIELDS),
        tuple(natural(layout[key], MEMORY_BYTES, f'layout.{key}') for key in LAYOUT_FIELDS),
        tuple(natural(steps[key], STEP_LIMIT, f'steps.{key}', minimum=1) for key in PROGRAMS),
        tuple(parsed_images))


def load_artifact(path: Path) -> Artifact:
    # A rejected symlink or FIFO must not be followed or block policy validation.
    flags = os.O_RDONLY | os.O_NONBLOCK | getattr(os, 'O_NOFOLLOW', 0)
    with os.fdopen(os.open(path, flags), 'rb') as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise ValueError('programs.json must be a regular file')
        raw = source.read(MAX_MANIFEST_BYTES + 1)
    return parse_artifact(raw)


def write_artifact_module(artifact: Artifact, project: Path):
    """Create before candidate execution; Linux isolation mounts the source tree read-only."""
    destination = project / 'CommitGolf' / 'Artifact.lean'
    destination.write_text(artifact.lean_source(), encoding='utf-8')
    destination.chmod(0o444)


def purge_artifact_cache(project: Path):
    """Never reuse an Artifact module compiled from a different delivered manifest."""
    for folder in (project / '.lake/build/lib/lean/CommitGolf',
                   project / '.lake/build/ir/CommitGolf'):
        for cached in folder.glob('Artifact.*'):
            cached.unlink()
