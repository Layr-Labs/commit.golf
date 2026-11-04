#!/usr/bin/env python3
"""Exercise artifact equality in the real Linux comparator sandbox.

This is a linkage-only regression, not a security-certificate verifier. An isolated trusted
configuration checks only submission_matches_artifact, so the fixed source fixtures do not
import the baseline's cryptographic proofs. This program never writes a benchmark score.
Run after the normal full-certificate benchmark on a supported verifier host.
"""
from __future__ import annotations

import copy
from dataclasses import dataclass
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from types import SimpleNamespace
import uuid

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from artifact import parse_artifact
from artifact_fixture import manifest
from check_submission import check
import verify

MATCHES = 'CommitGolf.Challenge.submission_matches_artifact'


@dataclass(frozen=True)
class Case:
    name: str
    manifest: bytes
    source: str
    expected: str


def linkage_config(production):
    """Keep the production definition hole and axiom policy; select only the equality theorem."""
    if production['definition_names'] != ['CommitGolf.Challenge.submission'] or not {
            'CommitGolf.Challenge.certificate', MATCHES} <= set(production['theorem_names']):
        raise ValueError('unexpected production comparator contract')
    config = copy.deepcopy(production)
    config['theorem_names'] = [MATCHES]
    return config


def make_cases(raw):
    artifact = parse_artifact(raw)
    reference = artifact.lean_source().replace(
        'namespace CommitGolf.Artifact\n', 'namespace CommitGolf.LinkageReference\n').replace(
        'end CommitGolf.Artifact\n', 'end CommitGolf.LinkageReference\n').replace(
        'import CommitGolf.Programs\n', 'import CommitGolf.Artifact\n', 1)
    direct = reference + '''
namespace CommitGolf.Challenge
def submission : CommitGolf.Submission := CommitGolf.LinkageReference.submission
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by rfl
end CommitGolf.Challenge
'''
    classical = reference + '''
namespace CommitGolf.Challenge
private theorem exists_submission :
    ∃ candidate : CommitGolf.Submission, candidate = CommitGolf.LinkageReference.submission :=
  ⟨CommitGolf.LinkageReference.submission, rfl⟩
noncomputable def submission : CommitGolf.Submission := Classical.choose exists_submission
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  (Classical.choose_spec exists_submission).trans (by rfl)
end CommitGolf.Challenge
'''
    cases = [Case('matching', raw, direct, 'verified'),
             Case('classical_matching', raw, classical, 'verified')]
    original = json.loads(raw)
    for name in ('instruction', 'embedded_data', 'layout', 'capacity', 'fuel'):
        changed = copy.deepcopy(original)
        if name == 'instruction':
            code = bytearray.fromhex(changed['images']['commit']['code'])
            if not code:
                raise ValueError('linkage regression needs a nonempty commitment image')
            code[0] ^= 1
            changed['images']['commit']['code'] = code.hex()
        elif name == 'embedded_data':
            changed['images']['commit']['data'] += '00'
        elif name == 'layout':
            changed['layout']['proof'] += 8
        elif name == 'capacity':
            changed['sizes']['proof'] += 8
        else:
            changed['steps']['check'] += 1
        cases.append(Case(name, (json.dumps(changed, indent=2) + '\n').encode(), direct, 'rejected'))
    missing = direct.replace(
        'theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by rfl\n', '')
    cases.append(Case('missing_equality', raw, missing, 'rejected'))
    return cases


def case_passes(case, report, full_log):
    """Recognize the pinned compiler/exporter's specific boundary rejection, not generic failure.

    verify's `rejected` status includes subprocess failures. The fixed fixtures must instead
    reach the expected equality error (or the exact missing exported target). Unknown diagnostics
    fail closed and require review when the Lean/exporter pin changes.
    """
    if report.get('status') != case.expected:
        return False
    if case.expected == 'verified':
        return True
    if re.search(r'\b(?:OOM|SIGKILL|killed)\b|out[- ]of[- ]memory|missing dependency|'
                 r'no such file|object file .+ does not exist|failed to load|unknown module prefix|'
                 r'(?:exit(?:ed)?(?: with)?|code)\s*127\b', full_log, re.IGNORECASE):
        return False
    lines = full_log.rstrip().splitlines()
    errors = [line for line in lines if line.startswith('error: ')]
    panics = [line for line in lines if line.startswith('PANIC ')]
    if case.name == 'missing_equality':
        target = re.compile(r'PANIC at dumpConstant Export:[0-9]+:[0-9]+: Constant ' +
                            re.escape(MATCHES) + r' not found in environment\.')
        return (not errors and len(panics) == 1 and target.fullmatch(panics[0]) is not None and
                re.search(r'Build completed successfully \([0-9]+ jobs\)\.\n' +
                          re.escape(panics[0]), full_log) is not None and
                lines[-1] == 'uncaught exception: Child exited with 134')
    if case.name not in ('instruction', 'embedded_data', 'layout', 'capacity', 'fuel'):
        return False
    theorem_lines = [(i, line) for i, line in enumerate(case.source.splitlines(), 1)
                     if line.startswith('theorem submission_matches_artifact ')]
    if len(theorem_lines) != 1 or 'rfl' not in theorem_lines[0][1]:
        return False
    line, source = theorem_lines[0]
    header = f'error: Solution.lean:{line}:{source.index("rfl")}: Tactic `rfl` failed: The left-hand side'
    mismatch = (header + '\n  submission\nis not definitionally equal to the right-hand side\n'
                '  Artifact.submission\n\n⊢ submission = Artifact.submission\n')
    return (not panics and errors == [header, 'error: build failed'] and
            mismatch in full_log and lines[-1] == 'uncaught exception: Child exited with 1')


def remove_owned(path, owner):
    """Only remove direct children of the private regression directory we created."""
    if path.parent != owner or path.is_symlink():
        raise ValueError('refusing to remove an unowned regression path')
    if path.exists():
        shutil.rmtree(path)


def prepare_trusted(root, owner):
    trusted = owner / 'trusted'
    # Git metadata supplies the same canonical revision as production. Only trusted contract
    # sources, tooling paths and caches are copied; no baseline candidate proof modules are built.
    subprocess.run(['git', 'clone', '--quiet', '--no-checkout', '--shared', '--no-hardlinks',
                    str(root), str(trusted)], check=True, stdout=subprocess.DEVNULL,
                   stderr=subprocess.PIPE)
    for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'CommitGolf.lean'):
        shutil.copy2(root / name, trusted / name)
    shutil.copytree(root / 'CommitGolf', trusted / 'CommitGolf')
    (trusted / 'verifier/.tools').mkdir(parents=True)
    for name in ('Challenge.lean.in', '.tools/env.sh'):
        shutil.copy2(root / 'verifier' / name, trusted / 'verifier' / name)
    config = json.loads((root / 'verifier/comparator.json').read_bytes())
    (trusted / 'verifier/comparator.json').write_text(json.dumps(linkage_config(config)) + '\n')
    verify.clone_tree(root / '.lake', trusted / '.lake')
    return trusted


def run(root=ROOT):
    if sys.platform != 'linux':
        raise ValueError('artifact linkage regression requires the supported Linux verifier')
    verify.linux_preflight(verify.tools_env(root))
    # A fixed fixture keeps these regressions independent of solvers whose admitted images,
    # capacities or instruction allowances may already sit at the contract's limits.
    cases = make_cases(json.dumps(manifest()).encode())
    production_config = (root / 'verifier/comparator.json').read_bytes()
    score_path = root / 'scripts/score.json'
    production_score = score_path.read_bytes() if score_path.exists() else None
    owner = root / '.work' / ('artifact-linkage-' + uuid.uuid4().hex)
    owner.mkdir(parents=True, mode=0o700)
    trusted = owner / 'trusted'
    results = []
    try:
        trusted = prepare_trusted(root, owner)
        for case in cases:
            candidate, work = owner / ('source-' + case.name), owner / ('run-' + case.name)
            candidate.mkdir()
            try:
                (candidate / 'programs.json').write_bytes(case.manifest)
                (candidate / 'Solution.lean').write_text(case.source)
                # Parsing requires a claim, but the linkage-only config checks no certificate.
                (candidate / 'claim.json').write_text(
                    '{"proofBytes":1,"commitCycles":1,"openingCycles":1}\n')
                policy = check(candidate)
                if not policy['ok']:
                    raise ValueError(f'{case.name}: invalid regression fixture: {policy["errors"]}')
                args = SimpleNamespace(work=work, commit=None, trusted=trusted, local=candidate,
                                       hide=[], repository=None, pr=None)
                report = verify.verify(args)
                full_log = ((work / 'verify.log').read_text(errors='replace')
                            if (work / 'verify.log').is_file() else '')
                with (owner / 'verify.log').open('a') as log:
                    log.write(f'\nArtifact linkage only: {case.name}; expected {case.expected}; '
                              f'observed {report["status"]}\n')
                    log.write(full_log)
                    if report.get('reason'):
                        log.write('\n' + report['reason'] + '\n')
                result = {'case': case.name, 'expected': case.expected,
                          'observed': report['status'], 'passed': case_passes(case, report, full_log)}
                results.append(result)
                print(json.dumps({'linkage_only': True, **result}), flush=True)
            finally:
                remove_owned(work, owner)
                remove_owned(candidate, owner)
    finally:
        remove_owned(trusted, owner)
        if (root / 'verifier/comparator.json').read_bytes() != production_config:
            raise ValueError('production comparator configuration changed during regression')
        if (score_path.read_bytes() if score_path.exists() else None) != production_score:
            raise ValueError('production score changed during linkage-only regression')
    print(json.dumps({'linkage_only': True, 'passed': all(item['passed'] for item in results),
                      'cases': len(results)}), flush=True)
    return 0 if len(results) == len(cases) and all(item['passed'] for item in results) else 1


if __name__ == '__main__':
    try:
        raise SystemExit(run())
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f'Artifact linkage regression failed: {exc}', file=sys.stderr)
        raise SystemExit(1)
