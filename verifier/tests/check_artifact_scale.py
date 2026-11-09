#!/usr/bin/env python3
"""Kernel-link a maximum-sized delivered artifact in the supported Linux sandbox.

This scale-only contract requests admission, exact lengths and selected endian-sensitive reads;
it is not a security certificate and never produces a benchmark score. Three distinct SHAKE
payloads exercise code-heavy, data-only and mixed images simultaneously at the strict size limit.
Whole-image native folds supplement the mandatory kernel checks; they carry no proof authority.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from types import SimpleNamespace
import uuid

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from artifact import MAX_PROGRAM_BYTES, parse_artifact
from artifact_fixture import manifest
from check_artifact_linkage import linkage_config, prepare_trusted, remove_owned
from check_submission import check
import verify

PREFIX = 'CommitGolf.Challenge.'
NATIVE_MARKER = 'COMMIT_GOLF_SCALE_NATIVE'


def scale_manifest():
    """Use unique chunks, little-endian markers and explicit final zero elements."""
    result = manifest()
    shapes = {'commit': (262143 * 4, 3), 'opening': (0, MAX_PROGRAM_BYTES - 1),
              'check': (131072 * 4, 524287)}
    for program, lengths in shapes.items():
        for kind, size in zip(('code', 'data'), lengths):
            data = bytearray(hashlib.shake_256(
                f'commit.golf/packed-scale/v1/{program}/{kind}'.encode()).digest(size))
            width = 4 if kind == 'code' else 1
            if size:
                data[-width:] = bytes(width)
                for index, value in ((0, 0x01234567 if width == 4 else 0x12),
                                     (63 if width == 4 else 255,
                                      0x89abcdef if width == 4 else 0x25),
                                     (64 if width == 4 else 256,
                                      0xfedcba98 if width == 4 else 0xd3)):
                    if (index + 1) * width < size:
                        data[index * width:(index + 1) * width] = value.to_bytes(width, 'little')
            result['images'][program][kind] = data.hex()
    return result


def expected_native_markers(value):
    """Compute supplementary whole-image folds directly from manifest bytes, not the renderer."""
    markers = []
    for program, image in value['images'].items():
        for kind, width in (('code', 4), ('data', 1)):
            raw = bytes.fromhex(image[kind])
            checksum = 14695981039346656037
            for index in range(0, len(raw), width):
                checksum = ((checksum ^ int.from_bytes(raw[index:index + width], 'little')) *
                            1099511628211) & ((1 << 64) - 1)
            markers.append(f'{NATIVE_MARKER} {program}_{kind} {len(raw) // width} {checksum}')
    return markers


def native_markers_match(value, full_log):
    """Every expected marker must occur once; malformed, duplicate or extra markers fail."""
    observed = []
    for line in full_log.splitlines():
        if NATIVE_MARKER not in line:
            continue
        # Lake may attach Lean's informational location to the captured #eval output.
        line = re.sub(r'^info: Solution\.lean:[0-9]+:[0-9]+: ', '', line)
        if not re.fullmatch(NATIVE_MARKER + r' [a-z_]+ [0-9]+ [0-9]+', line):
            return False
        observed.append(line)
    return sorted(observed) == sorted(expected_native_markers(value))


def scale_contract(value):
    """Build both exact trusted statements and ordinary kernel proofs from frozen raw bytes."""
    declarations = [('submission_matches_artifact',
                     'submission = CommitGolf.Artifact.submission', 'rfl')]
    for program, image in value['images'].items():
        for kind, bits in (('code', 32), ('data', 8)):
            raw = bytes.fromhex(image[kind])
            width = bits // 8
            count = len(raw) // width
            root = 'Artifact.' + program + kind.title()
            field = f'(submission.image .{program}).{kind}'
            declarations.append((f'{program}_{kind}_length', f'{field}.length = {count}',
                'by\n  simpa only [submission, Artifact.submission] using '
                f'(ArtifactEncoding.length_decode {bits} {root})'))
            # Include both sides of chunk and declaration joins, middle, endpoints and zero.
            indices = sorted({i for i in (0, 1, 63, 64, 255, 256, 511, 512, 2047, 2048,
                                          4095, 4096, 16383, 16384, count // 2, count - 2, count - 1)
                              if 0 <= i < count})
            for index in indices:
                expected = int.from_bytes(raw[index * width:(index + 1) * width], 'little')
                declarations.append((f'{program}_{kind}_at_{index}',
                    f'({field}.getD {index} 0).toNat = {expected}',
                    'by\n  simp only [submission, Artifact.submission]\n'
                    f'  rw [ArtifactEncoding.getD_decode {bits} {root} {index} (by decide)]\n  rfl'))
    admission = 'by\n  intro program\n  cases program\n'
    for program, image in value['images'].items():
        code_count = len(bytes.fromhex(image['code'])) // 4
        data_count = len(bytes.fromhex(image['data']))
        admission += f'''
  case {program} =>
    refine ⟨image_valid_of_lengths (submission.image .{program})
      (submission.layout.buffers submission.sizes) {code_count} {data_count}
      {program}_code_length {program}_data_length ?_ ?_, ?_, ?_⟩
    · decide
    · norm_num [submission, Artifact.submission, Layout.buffers, Riscv.DisjointBuffers,
        Riscv.MEMORY_BYTES, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    · decide
    · decide
'''
    declarations.append(('artifact_admission', 'submission.Admission', admission))
    header = ('import CommitGolf\nimport CommitGolf.Artifact\n\n'
              'namespace CommitGolf.Challenge\n\n')
    source = header + 'def submission : CommitGolf.Submission := CommitGolf.Artifact.submission\n\n'
    # Keep rewriting abstract image lengths separate from closed arithmetic. Reducing the
    # materialized maximum lists while proving admission would exhaust elaboration recursion.
    source += '''private theorem image_valid_of_lengths (image : Riscv.Image)
    (buffers : List (Nat × Nat)) (codeCount dataCount : Nat)
    (codeLength : image.code.length = codeCount) (dataLength : image.data.length = dataCount)
    (small : 4 * codeCount + dataCount < Riscv.MAX_PROGRAM_BYTES)
    (layout : (∀ buffer ∈ buffers,
      buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ 16 * ((Riscv.MEMORY_BYTES - dataCount) / 16)) ∧
      buffers.Pairwise Riscv.DisjointBuffers) : image.Valid buffers := by
  change (4 * image.code.length + image.data.length < Riscv.MAX_PROGRAM_BYTES) ∧
    ((∀ buffer ∈ buffers,
      buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ 16 * ((Riscv.MEMORY_BYTES - image.data.length) / 16)) ∧
      buffers.Pairwise Riscv.DisjointBuffers)
  rw [codeLength, dataLength]
  exact ⟨small, layout⟩

'''
    trusted = header + 'noncomputable def submission : CommitGolf.Submission := sorry\n\n'
    for name, statement, proof in declarations:
        source += f'theorem {name} : {statement} := {proof}\n\n'
        trusted += f'theorem {name} : {statement} := sorry\n\n'
    # Supplemental engineering check only: these native folds are never theorem authorities.
    source += '''private def scaleChecksum {bits : Nat} (values : List (BitVec bits)) : UInt64 :=
  values.foldl (fun state value => (state ^^^ UInt64.ofNat value.toNat) * 1099511628211)
    14695981039346656037

'''
    for program in value['images']:
        for kind in ('code', 'data'):
            source += f'''#eval do
  let values := (submission.image .{program}).{kind}
  IO.println s!"{NATIVE_MARKER} {program}_{kind} {{values.length}} {{(scaleChecksum values).toNat}}"

'''
    tail = 'end CommitGolf.Challenge\n'
    return source + tail, trusted + tail, [PREFIX + name for name, _, _ in declarations]


def run(root=ROOT):
    if sys.platform != 'linux':
        raise ValueError('artifact scale regression requires the supported Linux verifier')
    verify.linux_preflight(verify.tools_env(root))
    value = scale_manifest()
    raw = (json.dumps(value, separators=(',', ':')) + '\n').encode()
    parse_artifact(raw)
    source, template, targets = scale_contract(value)
    production_config = (root / 'verifier/comparator.json').read_bytes()
    score_path = root / 'scripts/score.json'
    production_score = score_path.read_bytes() if score_path.exists() else None
    owner = root / '.work' / ('artifact-scale-' + uuid.uuid4().hex)
    owner.mkdir(parents=True, mode=0o700)
    trusted, candidate, work = (owner / name for name in ('trusted', 'source', 'run'))
    try:
        prepare_trusted(root, owner)
        config = linkage_config(json.loads(production_config))
        config['theorem_names'] = targets
        (trusted / 'verifier/comparator.json').write_text(json.dumps(config) + '\n')
        (trusted / 'verifier/Challenge.lean.in').write_text(template)
        candidate.mkdir()
        (candidate / 'programs.json').write_bytes(raw)
        (candidate / 'Solution.lean').write_text(source)
        (candidate / 'claim.json').write_text(
            '{"proofBytes":1,"commitCycles":1,"openingCycles":1}\n')
        policy = check(candidate)
        if not policy['ok']:
            raise ValueError(f'invalid scale fixture: {policy["errors"]}')
        report = verify.verify(SimpleNamespace(work=work, commit=None, trusted=trusted,
            local=candidate, hide=[], repository=None, pr=None))
        report.pop('score', None)  # Admission-only evidence never publishes a security score.
        full_log = ((work / 'verify.log').read_text(errors='replace')
                    if (work / 'verify.log').is_file() else '')
        with (owner / 'verify.log').open('w') as log:
            log.write('Artifact scale only: all three images are 1048575 bytes.\n')
            log.write(full_log)
            log.write('\n' + json.dumps(report) + '\n')
        markers_match = native_markers_match(value, full_log)
        passed = report.get('status') == 'verified' and markers_match
        print(json.dumps({'scale_only': True, 'passed': passed, 'targets': len(targets),
                          'manifest_sha256': hashlib.sha256(raw).hexdigest(),
                          'observed': report.get('status'),
                          'native_checksums_match': markers_match}), flush=True)
        return 0 if passed else 1
    finally:
        for path in (work, candidate, trusted):
            remove_owned(path, owner)
        if (root / 'verifier/comparator.json').read_bytes() != production_config:
            raise ValueError('production comparator configuration changed during scale regression')
        if (score_path.read_bytes() if score_path.exists() else None) != production_score:
            raise ValueError('production score changed during scale-only regression')


if __name__ == '__main__':
    try:
        raise SystemExit(run())
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f'Artifact scale regression failed: {exc}', file=sys.stderr)
        raise SystemExit(1)
