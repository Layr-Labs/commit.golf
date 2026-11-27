#!/usr/bin/env python3
"""Real supported-Linux depth artifact/mode linkage and certificate-type rejection.

Matching toy images test equality only. The type-downgrade fixtures compile a True
proof but must fail the unchanged full production comparator. No fixture proves
cryptographic eligibility or writes a score; baseline full certificates run in
separate benchmark jobs.
"""
from dataclasses import dataclass
import json
from pathlib import Path
import re
import shutil
import sys
from types import SimpleNamespace
import uuid

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from artifact import parse_artifact
from check_artifact_linkage import prepare_trusted, remove_owned
from check_submission import check
from depth_profiles import depth_profile
from tracks import TRACKS
from artifact_fixture import manifest
import verify


@dataclass(frozen=True)
class Case:
    name: str
    track: str
    artifact: bytes
    source: str
    expected: str
    full_certificate: bool = False


def make_cases():
    cases = []
    for name, track in TRACKS.items():
        if track.depth_model is None:
            continue
        profile = depth_profile(track.depth_model)
        value = manifest()
        value.update(schemaVersion=2, executionModes=dict.fromkeys(('commit', 'opening', 'check'), 'legacy'))
        raw = json.dumps(value).encode()
        artifact = parse_artifact(raw, resource_model=track.depth_model)
        reference = artifact.lean_source().replace('namespace CommitGolf.Artifact\n',
            'namespace CommitGolf.LinkageReference\n').replace('end CommitGolf.Artifact\n',
            'end CommitGolf.LinkageReference\n').replace('import CommitGolf.Programs\n',
            'import CommitGolf.Artifact\n', 1)
        source = reference + f'''
namespace CommitGolf.Challenge
def submission : {profile.namespace}.Submission := CommitGolf.LinkageReference.depthSubmission
theorem submission_matches_artifact : submission = CommitGolf.Artifact.depthSubmission := by rfl
end CommitGolf.Challenge
'''
        prefix = track.depth_model.replace('-', '_')
        cases.append(Case(prefix + '_matching', name, raw, source, 'verified'))
        changed = json.loads(raw)
        changed['executionModes']['commit'] = profile.execution_modes[1]
        cases.append(Case(prefix + '_mode', name, json.dumps(changed).encode(), source, 'rejected'))
        changed = json.loads(raw)
        changed['images']['commit']['code'] = '13000000'
        cases.append(Case(prefix + '_bytes', name, json.dumps(changed).encode(), source, 'rejected'))
        # This fixture really compiles; generic compilation failure is never a passing result.
        partial = source + '\nnamespace CommitGolf.Challenge\ntheorem certificate : True := True.intro\nend CommitGolf.Challenge\n'
        cases.append(Case(prefix + '_partial_certificate', name, raw, partial, 'rejected', True))
    return cases


def case_passes(case, report, log):
    if report.get('status') != case.expected:
        return False
    if case.expected == 'verified':
        return True
    if re.search(r'\b(?:OOM|SIGKILL|killed)\b|out[- ]of[- ]memory|missing dependency|'
                 r'no such file|object file .+ does not exist|failed to load|unknown module prefix|'
                 r'(?:exit(?:ed)?(?: with)?|code)\s*127\b', log, re.I):
        return False
    if case.full_certificate:
        marker = "Challenge and solution theorem statement do not match: 'CommitGolf.Challenge.certificate'"
        return ('Build completed successfully (' in log and marker in log
                and not re.search(r'(?m)^(?:error: |PANIC )', log))
    theorem = [(i, s) for i, s in enumerate(case.source.splitlines(), 1)
               if s.startswith('theorem submission_matches_artifact ')]
    if len(theorem) != 1:
        return False
    line, source = theorem[0]
    header = f'error: Solution.lean:{line}:{source.index("rfl")}: Tactic `rfl` failed: The left-hand side'
    mismatch = (header + '\n  submission\nis not definitionally equal to the right-hand side\n'
                '  Artifact.depthSubmission\n\n⊢ submission = Artifact.depthSubmission\n')
    errors = re.findall(r'(?m)^error: .*$', log)
    return (errors == [header, 'error: build failed'] and mismatch in log
            and 'PANIC ' not in log and log.rstrip().endswith('uncaught exception: Child exited with 1'))


def run(root=ROOT):
    if sys.platform != 'linux':
        raise ValueError('depth linkage regression requires the supported Linux verifier')
    verify.linux_preflight(verify.tools_env(root))
    owner = root / '.work' / ('depth-linkage-' + uuid.uuid4().hex)
    owner.mkdir(parents=True, mode=0o700)
    trusted = owner / 'trusted'
    production = (root / 'verifier/comparator.json').read_bytes()
    scores = {root / t.score_path: (root / t.score_path).read_bytes()
              if (root / t.score_path).exists() else None for t in TRACKS.values()}
    results = []
    try:
        trusted = prepare_trusted(root, owner)
        shutil.copy2(root / 'CommitGolfDepth.lean', trusted / 'CommitGolfDepth.lean')
        shutil.copytree(root / 'CommitGolfDepth', trusted / 'CommitGolfDepth')
        for name in ('RoundsChallenge.lean.in', 'SpanChallenge.lean.in'):
            shutil.copy2(root / 'verifier' / name, trusted / 'verifier' / name)
        equality_config = (trusted / 'verifier/comparator.json').read_bytes()
        for case in make_cases():
            candidate, work = owner / ('source-' + case.name), owner / ('run-' + case.name)
            candidate.mkdir()
            track = TRACKS[case.track]
            profile = depth_profile(track.depth_model)
            try:
                (trusted / 'verifier/comparator.json').write_bytes(
                    production if case.full_certificate else equality_config)
                (candidate / 'programs.json').write_bytes(case.artifact)
                (candidate / 'Solution.lean').write_text(case.source)
                (candidate / 'claim.json').write_text(json.dumps(dict.fromkeys(profile.claim_keys, 1)))
                policy = check(candidate, resource_model=track.depth_model)
                if not policy['ok']:
                    raise ValueError(f'{case.name}: invalid regression fixture: {policy["errors"]}')
                args = SimpleNamespace(work=work, commit=None, trusted=trusted, local=candidate,
                                       hide=[], repository=None, pr=None, track=case.track)
                report = verify.verify(args)
                full_log = ((work / 'verify.log').read_text(errors='replace')
                            if (work / 'verify.log').is_file() else '')
                with (owner / 'verify.log').open('a') as log:
                    log.write(f'\nDepth linkage/type rejection: {case.name}; observed {report["status"]}\n')
                    log.write(full_log)
                    log.write('\n' + report.get('reason', '') + '\n')
                result = dict(case=case.name, expected=case.expected, observed=report['status'],
                              passed=case_passes(case, report, full_log))
                results.append(result)
                print(json.dumps(dict(depth_linkage_only=True, **result)), flush=True)
            finally:
                remove_owned(work, owner)
                remove_owned(candidate, owner)
    finally:
        remove_owned(trusted, owner)
        if (root / 'verifier/comparator.json').read_bytes() != production:
            raise ValueError('production comparator configuration changed')
        for path, before in scores.items():
            if (path.read_bytes() if path.exists() else None) != before:
                raise ValueError('production score changed during depth linkage regression')
    passed = len(results) == len(make_cases()) and all(r['passed'] for r in results)
    print(json.dumps(dict(depth_linkage_only=True, passed=passed, cases=len(results))), flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(run())
