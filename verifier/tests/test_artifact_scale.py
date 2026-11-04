import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import MAX_PROGRAM_BYTES, parse_artifact
from check_artifact_scale import (NATIVE_MARKER, PREFIX, expected_native_markers,
                                  native_markers_match, scale_contract, scale_manifest)
from artifact_fixture import manifest
from check_submission import check


class ArtifactScaleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.value = scale_manifest()
        cls.raw = (json.dumps(cls.value, separators=(',', ':')) + '\n').encode()

    def test_distinct_maximum_shapes_are_accepted_and_exact_limit_rejected(self):
        parse_artifact(self.raw)
        lengths = []
        for image in self.value['images'].values():
            code, data = bytes.fromhex(image['code']), bytes.fromhex(image['data'])
            self.assertEqual(len(code) + len(data), MAX_PROGRAM_BYTES - 1)
            self.assertEqual(code[-4:] if code else b'', b'\0' * min(len(code), 4))
            self.assertEqual(data[-1:], b'\0')
            lengths.append((len(code) // 4, len(data)))
        self.assertEqual(lengths, [(262143, 3), (0, 1048575), (131072, 524287)])
        # Each image individually rejects equality with the strict upper limit.
        for program in self.value['images']:
            changed = copy.deepcopy(self.value)
            changed['images'][program]['data'] += '00'
            with self.subTest(program=program), self.assertRaises(ValueError):
                parse_artifact(json.dumps(changed).encode())
        raw = bytes.fromhex(self.value['images']['opening']['data'])
        self.assertGreater(len({raw[i:i + 256] for i in range(0, len(raw), 256)}), 4000)

    def test_all_semantic_facts_are_requested_trusted_targets_and_policy_valid(self):
        source, trusted, targets = scale_contract(self.value)
        names = [name.removeprefix(PREFIX) for name in targets]
        self.assertGreater(len(targets), 60)
        self.assertEqual(len(targets), len(set(targets)))
        self.assertIn(PREFIX + 'artifact_admission', targets)
        self.assertIn(PREFIX + 'submission_matches_artifact', targets)
        for name in names:
            self.assertIn(f'theorem {name} :', source)
            self.assertIn(f'theorem {name} :', trusted)
        self.assertEqual(trusted.count(':= sorry'), len(targets) + 1)
        self.assertNotIn('sorry', source)
        self.assertNotIn('set_option', source)
        self.assertNotIn('native_decide', source)
        self.assertNotIn('theorem certificate', source + trusted)
        self.assertLess(len(source.encode()), 8 * 1024 * 1024)
        for suffix in ('commit_code_at_63', 'commit_code_at_64', 'opening_data_at_255',
                       'opening_data_at_256', 'opening_data_at_2047', 'opening_data_at_2048',
                       'opening_data_at_16383', 'opening_data_at_16384',
                       'check_code_at_4095', 'check_code_at_4096'):
            self.assertIn(PREFIX + suffix, targets)
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory)
            (candidate / 'programs.json').write_bytes(self.raw)
            (candidate / 'Solution.lean').write_text(source)
            (candidate / 'claim.json').write_text(
                '{"proofBytes":1,"commitCycles":1,"openingCycles":1}\n')
            result = check(candidate)
            self.assertTrue(result['ok'], result['errors'])

    def test_whole_image_native_markers_are_supplementary_and_strict(self):
        value = manifest()
        markers = expected_native_markers(value)
        self.assertEqual(len(markers), 6)
        log = '\n'.join(markers)
        self.assertTrue(native_markers_match(value, log))
        self.assertTrue(native_markers_match(value, '\n'.join(
            'info: Solution.lean:100:0: ' + marker for marker in markers)))
        for bad in ('\n'.join(markers[:-1]), log + '\n' + markers[0],
                    log + f'\n{NATIVE_MARKER} unexpected 1 2',
                    log.replace(markers[0], markers[0] + '0'),
                    log.replace(markers[0], markers[0].replace(' 1 ', ' 2 ', 1)),
                    log.replace(NATIVE_MARKER, NATIVE_MARKER + '_TYPO', 1),
                    'untrusted prefix ' + log, ''):
            with self.subTest(log=bad):
                self.assertFalse(native_markers_match(value, bad))
        source, trusted, _ = scale_contract(value)
        self.assertEqual(source.count('#eval do'), 6)
        self.assertNotIn(NATIVE_MARKER, trusted)
        self.assertNotIn('scaleChecksum', trusted)
        # The empty image uses the offset basis; code folds whole little-endian words.
        value['images']['commit'] = {'code': '0100000000000000', 'data': '61'}
        expected = expected_native_markers(value)
        self.assertIn(f'{NATIVE_MARKER} commit_code 2 589727492704079044', expected)
        self.assertIn(f'{NATIVE_MARKER} commit_data 1 12638187200555641996', expected)


if __name__ == '__main__':
    unittest.main()
