import copy
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import MAX_MANIFEST_BYTES, MAX_PROGRAM_BYTES, MEMORY_BYTES, STEP_LIMIT
from artifact import PACKED_CHUNK_BYTES, PACKED_DECLARATION_FANOUT, packed_declarations
from artifact import load_artifact, parse_artifact, purge_artifact_cache, write_artifact_module
from artifact_fixture import manifest


def encoded(value):
    return json.dumps(value).encode()


class ArtifactTests(unittest.TestCase):
    def test_exact_word_and_data_bytes_reach_generated_module(self):
        value = manifest()
        value['images']['commit'] = {'code': '78563412ffffffff', 'data': '00ff'}
        artifact = parse_artifact(encoded(value))
        self.assertEqual(artifact.images[0].code, (0x12345678, 0xffffffff))
        self.assertEqual(artifact.images[0].data, bytes([0, 255]))
        source = artifact.lean_source()
        self.assertIn('def commitCode : ArtifactEncoding.Packed 2', source)
        self.assertIn(f'ArtifactEncoding.Packed.chunk 2 {int.from_bytes(bytes.fromhex("78563412ffffffff"), "little")}', source)
        self.assertIn('ArtifactEncoding.Packed.chunk 2 65280', source)
        self.assertIn('| .commit => ⟨ArtifactEncoding.decode 32 commitCode, '
                      'ArtifactEncoding.decode 8 commitData⟩', source)
        self.assertNotIn('sorry', source)
        self.assertNotIn('noncomputable', source)
        self.assertEqual(artifact.digest, hashlib.sha256(encoded(value)).hexdigest())

    def test_formatting_changes_digest_but_not_submission_value(self):
        value = manifest()
        left = parse_artifact(encoded(value))
        right = parse_artifact(json.dumps(value, indent=2).encode())
        self.assertNotEqual(left.digest, right.digest)
        self.assertEqual(left.lean_source(), right.lean_source())

    def test_packed_boundary_counts_and_trailing_zeros_preserve_exact_bytes(self):
        for bits, counts in ((32, (0, 1, 63, 64, 65)), (8, (0, 1, 2, 3, 255, 256, 257))):
            for count in counts:
                with self.subTest(bits=bits, count=count):
                    size = count * (bits // 8)
                    raw = bytearray(hashlib.shake_256(f'{bits}/{count}'.encode()).digest(size))
                    if raw:
                        raw[-1] = 0
                    source = '\n'.join(packed_declarations('probe', bytes(raw), bits))
                    leaves = [(int(n), int(payload)) for n, payload in
                              re.findall(r'Packed\.chunk ([0-9]+) ([0-9]+)', source)]
                    self.assertEqual(sum(n for n, _ in leaves), count)
                    self.assertEqual(b''.join(payload.to_bytes(n * (bits // 8), 'little')
                                              for n, payload in leaves), raw)
                    self.assertTrue(all(n <= PACKED_CHUNK_BYTES // (bits // 8) for n, _ in leaves))

    def test_large_packed_source_bounds_work_per_declaration(self):
        raw = hashlib.shake_256(b'named packed declarations').digest(PACKED_CHUNK_BYTES * 129 - 3)
        source = '\n'.join(packed_declarations('probe', raw, 8))
        blocks = source.split('def ')[1:]
        self.assertGreater(len(blocks), 16)
        for block in blocks:
            self.assertLessEqual(block.count('Packed.chunk '), PACKED_DECLARATION_FANOUT)
            self.assertLessEqual(block.count('Packed.join '), PACKED_DECLARATION_FANOUT - 1)
        leaves = [(int(n), int(payload)) for n, payload in
                  re.findall(r'Packed\.chunk ([0-9]+) ([0-9]+)', source)]
        self.assertEqual(b''.join(payload.to_bytes(n, 'little') for n, payload in leaves), raw)

    def test_code_and_abi_tampering_change_certified_value(self):
        original = manifest()
        reference = parse_artifact(encoded(original))
        for path, replacement in ((('images', 'commit', 'code'), '93000000'),
                                  (('layout', 'proof'), original['layout']['proof'] + 8),
                                  (('sizes', 'trapdoor'), 24), (('steps', 'check'), 19)):
            changed = copy.deepcopy(original)
            slot = changed
            for key in path[:-1]:
                slot = slot[key]
            slot[path[-1]] = replacement
            artifact = parse_artifact(encoded(changed))
            self.assertNotEqual(artifact.lean_source(), reference.lean_source())
            self.assertNotEqual(artifact.digest, reference.digest)

    def test_duplicate_keys_are_rejected_at_root_and_nested_levels(self):
        raw = json.dumps(manifest())
        for old, new in (('"schemaVersion": 1', '"schemaVersion": 1, "schemaVersion": 1'),
                         ('"code": "73000000"', '"code": "73000000", "code": "73000000"')):
            with self.assertRaisesRegex(ValueError, 'duplicate manifest key'):
                parse_artifact(raw.replace(old, new, 1).encode())

    def test_unknown_and_missing_keys_are_rejected_at_every_level(self):
        for path in ((), ('sizes',), ('layout',), ('steps',), ('images',), ('images', 'commit')):
            for extra in (True, False):
                value = manifest()
                slot = value
                for key in path:
                    slot = slot[key]
                if extra:
                    slot['unexpected'] = 0
                else:
                    del slot[next(iter(slot))]
                with self.assertRaisesRegex(ValueError, 'must contain exactly'):
                    parse_artifact(encoded(value))

    def test_integer_fields_reject_boolean_float_negative_and_overflow(self):
        for section, field, maximum in (('sizes', 'proof', MEMORY_BYTES),
                                        ('layout', 'proof', MEMORY_BYTES),
                                        ('steps', 'commit', STEP_LIMIT)):
            for invalid in (True, 1.0, '1', -1, maximum + 1):
                value = manifest()
                value[section][field] = invalid
                with self.assertRaises(ValueError):
                    parse_artifact(encoded(value))
        for invalid in (True, 1.0, 0, 2):
            value = manifest()
            value['schemaVersion'] = invalid
            with self.assertRaises(ValueError):
                parse_artifact(encoded(value))
        value = manifest()
        value['steps']['commit'] = 0
        with self.assertRaises(ValueError):
            parse_artifact(encoded(value))

    def test_noncanonical_hex_and_truncated_instructions_are_rejected(self):
        for invalid in ('0A', '00 ', '0x00', 'a', 'xz', '12\n34', '"\naxiom injected : False'):
            for field in ('code', 'data'):
                value = manifest()
                value['images']['commit'][field] = invalid
                with self.assertRaises(ValueError):
                    parse_artifact(encoded(value))
        value = manifest()
        value['images']['commit']['code'] = '0000'
        with self.assertRaisesRegex(ValueError, 'complete 32-bit instructions'):
            parse_artifact(encoded(value))

    def test_nan_and_infinity_are_rejected(self):
        raw = json.dumps(manifest())
        for invalid in ('NaN', 'Infinity', '-Infinity'):
            with self.assertRaisesRegex(ValueError, 'invalid JSON constant'):
                parse_artifact(raw.replace('"schemaVersion": 1', '"schemaVersion": ' + invalid).encode())

    def test_image_and_manifest_size_limits_are_strict(self):
        value = manifest()
        value['images']['commit']['data'] = '00' * (MAX_PROGRAM_BYTES - 4)
        with self.assertRaisesRegex(ValueError, 'smaller than 1 MiB'):
            parse_artifact(encoded(value))
        value['images']['commit']['data'] = '00' * (MAX_PROGRAM_BYTES - 5)
        parse_artifact(encoded(value))
        with self.assertRaisesRegex(ValueError, 'exceeds 8 MiB'):
            parse_artifact(b' ' * (MAX_MANIFEST_BYTES + 1))

    def test_generated_source_is_read_only_and_only_artifact_caches_are_removed(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            (project / 'CommitGolf').mkdir()
            artifact = parse_artifact(encoded(manifest()))
            write_artifact_module(artifact, project)
            source = project / 'CommitGolf/Artifact.lean'
            self.assertEqual(source.read_text(), artifact.lean_source())
            self.assertEqual(source.stat().st_mode & 0o222, 0)
            for root in ('lib/lean', 'ir'):
                folder = project / '.lake/build' / root / 'CommitGolf'
                folder.mkdir(parents=True)
                for name in ('Artifact.olean', 'Artifact.olean.private', 'Artifact.trace',
                             'Artifact.c', 'Artifact.c.o', 'Programs.olean'):
                    (folder / name).write_bytes(b'stale')
            purge_artifact_cache(project)
            for root in ('lib/lean', 'ir'):
                folder = project / '.lake/build' / root / 'CommitGolf'
                self.assertEqual([p.name for p in folder.iterdir()], ['Programs.olean'])
            delivered = project / 'programs.json'
            delivered.write_bytes(artifact.raw)
            self.assertEqual(load_artifact(delivered), artifact)

    def test_manifest_symlinks_and_fifos_are_not_read(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'target.json').write_bytes(encoded(manifest()))
            (root / 'link.json').symlink_to('target.json')
            with self.assertRaises((OSError, ValueError)):
                load_artifact(root / 'link.json')
            os.mkfifo(root / 'fifo.json')
            with self.assertRaisesRegex(ValueError, 'regular file'):
                load_artifact(root / 'fifo.json')


if __name__ == '__main__':
    unittest.main()
