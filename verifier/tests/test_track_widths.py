import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from tracks import TRACKS, Track, prepare_contract


class TrackWidthTests(unittest.TestCase):
    def test_track_registration_matches_the_trusted_width_and_price(self):
        registered = json.loads((ROOT / 'benchmark.json').read_text())['tracks']
        expected = {
            'product': (64, 8, False),
            'pareto': (64, 8, True),
            'commit-golf-oracle-rounds-pareto': (64, 8, True),
            'commit-golf-work-span-pareto': (64, 8, True),
            'commit-golf-96-32-product': (96, 30, False),
            'commit-golf-96-32-pareto': (96, 30, True),
            'commit-golf-64-32-product': (64, 30, False),
            'commit-golf-64-32-pareto': (64, 30, True),
        }
        self.assertEqual({item['name'] for item in registered}, set(expected))
        self.assertEqual(set(TRACKS), set(expected))
        for item in registered:
            name = item['name']
            track = TRACKS[name]
            with self.subTest(track=name):
                self.assertEqual(item['editablePaths'], [track.submission])
                self.assertEqual(item['scorePath'], track.score_path)
                self.assertEqual(item.get('mode') == 'pareto', track.pareto)
                self.assertEqual((track.compression_input_bytes, track.permutation_cycles, track.pareto),
                                 expected[name])
                self.assertTrue((ROOT / '.github/workflows' / item['runner']['workflow']).is_file())

    def test_width_change_alone_invalidates_the_project_build(self):
        # Exercise width invalidation independently of the permutation-price change.
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            (project / 'CommitGolf').mkdir()
            shutil.copy2(ROOT / 'CommitGolf/Parameters.lean', project / 'CommitGolf/Parameters.lean')
            cached = project / '.lake/build/lib/lean/CommitGolf/Riscv.olean'
            cached.parent.mkdir(parents=True)
            cached.write_bytes(b'compiled 64-byte oracle')
            prepare_contract(project, Track('unused', 'unused', False, 8, 96))
            source = (project / 'CommitGolf/Parameters.lean').read_text()
            self.assertIn('def COMPRESSION_INPUT_LENGTH : Nat := 768\n', source)
            self.assertIn('def COMPRESSION_OUTPUT_LENGTH : Nat := 256\n', source)
            self.assertIn('def COMPRESSION_CYCLES : Nat := 8\n', source)
            self.assertIn('def PERMUTATION_CYCLES : Nat := 8\n', source)
            self.assertFalse((project / '.lake/build').exists())
