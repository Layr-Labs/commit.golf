"""Fixed executable clients for the resource-only comparator regression.

These images deliberately do not implement commitments. The normal ABI loads their
small embedded descriptor tables; caller instructions, macro work and child work
are measured. No fixture receives a host-prepared MachineState.
"""
from dataclasses import dataclass
from pathlib import Path

from artifact_fixture import manifest

FIXTURES = Path(__file__).parent / 'fixtures'


@dataclass(frozen=True)
class ResourceFixture:
    model: str
    track: str
    source: str
    template: str
    work: int
    depth: int
    instructions: int
    code: tuple[int, ...]
    data: tuple[int, ...]

    def manifest(self):
        value = manifest()
        value['schemaVersion'] = 2
        mode = 'batched' if self.model == 'oracle-rounds' else 'forkJoin'
        value['executionModes'] = dict.fromkeys(('commit', 'opening', 'check'), mode)
        image = {'code': b''.join(w.to_bytes(4, 'little') for w in self.code).hex(),
                 'data': b''.join(w.to_bytes(8, 'little') for w in self.data).hex()}
        value['images'] = {name: dict(image) for name in ('commit', 'opening', 'check')}
        value['steps'] = dict.fromkeys(('commit', 'opening', 'check'), self.instructions)
        return value


RESOURCE_FIXTURES = (
    ResourceFixture('oracle-rounds', 'commit-golf-oracle-rounds-pareto',
        'RoundsResources.lean', 'RoundsResources.lean.in', 33, 1, 7,
        (0x00010513, 0x00200593, 0x00300293, 0x73, 0x00100293, 0x00000513, 0x73),
        (0, 0, 64, 512, 0, 512, 64, 544)),
    ResourceFixture('work-span', 'commit-golf-work-span-pareto',
        'SpanResources.lean', 'SpanResources.lean.in', 103, 95, 16,
        (0x00010513, 0x00300293, 0x73, 0x00100293, 0x00000513, 0x73,
         0x02b585b3, 0x00b53023, 0x00100293, 0x00000513, 0x73),
        (0x1018, 5, 512, 8, 512, 7, 0, 0, 0x1018, 5, 520, 8, 520, 9, 0, 0)),
)
