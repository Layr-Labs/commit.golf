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
PACKED_CHUNK_BYTES = 256
PACKED_DECLARATION_FANOUT = 8


def packed_declarations(name: str, raw: bytes, bits: int) -> list[str]:
    """Bound both literal size and work per Lean declaration; balance joins within each block."""
    width = bits // 8
    if bits not in (8, 32) or len(raw) % width:
        raise ValueError('internal packed element width mismatch')
    chunks = [(len(raw[i:i + PACKED_CHUNK_BYTES]) // width,
               int.from_bytes(raw[i:i + PACKED_CHUNK_BYTES], 'little'))
              for i in range(0, len(raw), PACKED_CHUNK_BYTES)]
    if not chunks:
        chunks = [(0, 0)]

    def render(entries, start, stop, indent):
        if stop - start == 1:
            return entries[start]
        middle = (start + stop) // 2
        left_count, left = render(entries, start, middle, indent + '  ')
        right_count, right = render(entries, middle, stop, indent + '  ')
        return (left_count + right_count,
                f'(@ArtifactEncoding.Packed.join {left_count} {right_count}\n'
                f'{indent}  {left}\n{indent}  {right})')

    entries = [(count, f'(ArtifactEncoding.Packed.chunk {count} {payload})')
               for count, payload in chunks]
    declarations = []
    level = 0
    while len(entries) > PACKED_DECLARATION_FANOUT:
        next_entries = []
        for start in range(0, len(entries), PACKED_DECLARATION_FANOUT):
            count, body = render(entries, start, min(start + PACKED_DECLARATION_FANOUT,
                                                    len(entries)), '  ')
            part = f'{name}_{level}_{len(next_entries)}'
            declarations.extend([f'def {part} : ArtifactEncoding.Packed {count} :=',
                                 '  ' + body, ''])
            next_entries.append((count, part))
        entries = next_entries
        level += 1
    count, body = render(entries, 0, len(entries), '  ')
    declarations.extend([f'def {name} : ArtifactEncoding.Packed {count} :=', '  ' + body, ''])
    return declarations


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
        lines = ['import CommitGolf.Programs', 'import CommitGolf.ArtifactEncoding', '',
                 'namespace CommitGolf.Artifact', '']
        for name, image in zip(PROGRAMS, self.images):
            raw_code = b''.join(word.to_bytes(4, 'little') for word in image.code)
            for suffix, raw, bits in (('Code', raw_code, 32), ('Data', image.data, 8)):
                lines.extend(packed_declarations(name + suffix, raw, bits))
        lines.extend([
                 '/-- Exact machine bytes and ABI decoded from submission/programs.json. -/',
                 'def submission : CommitGolf.Submission where',
                 '  sizes := ⟨' + ', '.join(map(str, self.sizes)) + '⟩',
                 '  layout := ⟨' + ', '.join(map(str, self.layout)) + '⟩',
                 '  image'])
        lines.extend(f'    | .{name} => ⟨ArtifactEncoding.decode 32 {name}Code, '
                     f'ArtifactEncoding.decode 8 {name}Data⟩' for name in PROGRAMS)
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
