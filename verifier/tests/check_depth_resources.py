#!/usr/bin/env python3
"""Supported comparator checks for real batched/fork resource proof clients.

This owned regression project replaces only its private trusted template/config.
It checks admission, delivered bytes/modes and a fixed-zero-message/all-fixed-oracle
resource theorem. It never substitutes for the production full Certificate and
never writes a benchmark score or emits a valid-score report.
"""
from dataclasses import dataclass
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import sys
from types import SimpleNamespace
import uuid

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from check_artifact_linkage import prepare_trusted, remove_owned
from check_submission import check, MAX_FILE_BYTES
from depth_profiles import depth_profile
from depth_resource_fixture import FIXTURES, RESOURCE_FIXTURES
from tracks import TRACKS
import verify

RESOURCE_TARGET = 'CommitGolf.Challenge.resource_fixture'
SYMBOLIC_STEP = 'CommitGolf.Challenge.symbolic_step'
SYMBOLIC_BOUNDS = 'CommitGolf.Challenge.symbolic_bounds'
EQUALITY_TARGET = 'CommitGolf.Challenge.submission_matches_artifact'
ADMISSION_TARGET = 'CommitGolf.Challenge.admission'


def load_library(root, relative):
    """Capture one bounded regular helper without following any source symlinks."""
    relative = Path(relative)
    if relative.is_absolute() or not relative.parts or '..' in relative.parts:
        raise ValueError('helper path must stay inside the repository')
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK
    directory = os.open(root, directory_flags)
    try:
        for part in relative.parts[:-1]:
            child = os.open(part, directory_flags, dir_fd=directory)
            os.close(directory)
            directory = child
        descriptor = os.open(relative.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
        try:
            if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                raise ValueError('helper must be a regular file')
            with os.fdopen(descriptor, 'rb', closefd=False) as source:
                captured = source.read(MAX_FILE_BYTES + 1)
        finally:
            os.close(descriptor)
        if len(captured) > MAX_FILE_BYTES:
            raise ValueError('helper exceeds the source-file size limit')
        return captured
    finally:
        os.close(directory)


@dataclass(frozen=True)
class Case:
    name: str
    fixture: object
    manifest: bytes
    work: int
    depth: int
    expected: str
    production_scope: bool = False
    symbolic_mismatch: bool = False


def resource_config(production):
    if production['definition_names'] != ['CommitGolf.Challenge.submission'] or set(
            production['theorem_names']) != {'CommitGolf.Challenge.certificate', EQUALITY_TARGET}:
        raise ValueError('unexpected production comparator contract')
    result = copy.deepcopy(production)
    result['theorem_names'] = [EQUALITY_TARGET, ADMISSION_TARGET, RESOURCE_TARGET,
                               SYMBOLIC_STEP, SYMBOLIC_BOUNDS]
    return result


def make_cases():
    cases = []
    for fixture in RESOURCE_FIXTURES:
        value = fixture.manifest()
        raw = json.dumps(value).encode()
        prefix = fixture.model.replace('-', '_')
        cases.append(Case(prefix + '_resources', fixture, raw, fixture.work, fixture.depth, 'verified'))
        cases.append(Case(prefix + '_under_work', fixture, raw, fixture.work - 1, fixture.depth, 'rejected'))
        cases.append(Case(prefix + '_under_depth', fixture, raw, fixture.work, fixture.depth - 1, 'rejected'))
        changed = copy.deepcopy(value)
        changed['executionModes']['commit'] = 'legacy'
        cases.append(Case(prefix + '_wrong_mode', fixture, json.dumps(changed).encode(),
                          fixture.work, fixture.depth, 'rejected'))
        changed = copy.deepcopy(value)
        code = bytearray.fromhex(changed['images']['commit']['code'])
        code[0] ^= 1
        changed['images']['commit']['code'] = code.hex()
        cases.append(Case(prefix + '_wrong_image', fixture, json.dumps(changed).encode(),
                          fixture.work, fixture.depth, 'rejected'))
        cases.append(Case(prefix + '_not_security_certificate', fixture, raw,
                          fixture.work, fixture.depth, 'rejected', True))
        cases.append(Case(prefix + '_symbolic_mismatch', fixture, raw,
                          fixture.work, fixture.depth, 'rejected', symbolic_mismatch=True))
    return cases


def expected_template(case):
    source = (FIXTURES / case.fixture.template).read_text()
    for name, value in (('work', case.work), ('depth', case.depth)):
        source = source.replace('{{' + name + '}}', str(value))
    if '{{' in source:
        raise ValueError('unresolved resource-fixture template')
    if case.symbolic_mismatch:
        before, marker, bounds = source.partition('theorem symbolic_bounds')
        old, new = (('rounds requests+depth', '0+depth')
                    if case.fixture.model == 'oracle-rounds' else ('max ls rs', 'min ls rs'))
        if not marker or bounds.count(old) != 1:
            raise ValueError('unexpected symbolic-bound regression template')
        source = before + marker + bounds.replace(old, new, 1)
    return source


def case_passes(case, report, log, source):
    if report.get('status') != case.expected:
        return False
    if case.expected == 'verified':
        return 'Your solution is okay!' in log
    if re.search(r'\b(?:OOM|SIGKILL|killed)\b|out[- ]of[- ]memory|missing dependency|'
                 r'no such file|object file .+ does not exist|failed to load|unknown module prefix|'
                 r'(?:exit(?:ed)?(?: with)?|code)\s*127\b', log, re.I):
        return False
    if case.production_scope:
        panics = re.findall(r'(?m)^PANIC .*$', log)
        target = re.compile(r"PANIC at dumpConstant Export:[0-9]+:[0-9]+: Constant "
                            r"CommitGolf\.Challenge\.certificate not found in environment\.")
        return (not re.search(r'(?m)^error: ', log) and len(panics) == 1
                and target.fullmatch(panics[0]) is not None
                and re.search(r'Build completed successfully \([0-9]+ jobs\)\.\n' +
                              re.escape(panics[0]), log) is not None
                and log.rstrip().splitlines()[-1] in (
                    'uncaught exception: Child exited with 134',
                    'uncaught exception: Child exited with 139'))
    if case.name.endswith(('_under_work', '_under_depth', '_symbolic_mismatch')):
        target = SYMBOLIC_BOUNDS if case.symbolic_mismatch else RESOURCE_TARGET
        marker = f"Challenge and solution theorem statement do not match: '{target}'"
        return ('Build completed successfully (' in log and marker in log
                and not re.search(r'(?m)^(?:error: |PANIC )', log))
    # Exact equality diagnostics are checked below; generic compiler failures never pass.
    theorem = [(i, s) for i, s in enumerate(source.splitlines(), 1)
               if s.startswith('theorem submission_matches_artifact ')]
    if len(theorem) != 1:
        return False
    line, declaration = theorem[0]
    if 'rfl' not in declaration:
        return False
    header = f'error: Solution.lean:{line}:{declaration.index("rfl")}: Tactic `rfl` failed: The left-hand side'
    mismatch = (header + '\n  submission\nis not definitionally equal to the right-hand side\n'
                '  Artifact.depthSubmission\n\n⊢ submission = Artifact.depthSubmission\n')
    return (re.findall(r'(?m)^error: .*$', log) == [header, 'error: build failed']
            and mismatch in log and 'PANIC ' not in log
            and log.rstrip().endswith('uncaught exception: Child exited with 1'))


def protected_snapshot(root):
    paths = [root / 'verifier' / name for name in
             ('comparator.json', 'Challenge.lean.in', 'RoundsChallenge.lean.in', 'SpanChallenge.lean.in')]
    paths += [root / t.score_path for t in TRACKS.values()]
    return {path: hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None
            for path in paths}


def run(root=ROOT):
    if sys.platform != 'linux':
        raise ValueError('resource fixtures require the supported Linux verifier')
    verify.linux_preflight(verify.tools_env(root))
    owner = root / '.work' / ('depth-resources-' + uuid.uuid4().hex)
    owner.mkdir(parents=True, mode=0o700)
    trusted = owner / 'trusted'
    before = protected_snapshot(root)
    production = json.loads((root / 'verifier/comparator.json').read_text())
    results = []
    cases = make_cases()
    try:
        trusted = prepare_trusted(root, owner)
        shutil.copy2(root / 'CommitGolfDepth.lean', trusted / 'CommitGolfDepth.lean')
        shutil.copytree(root / 'CommitGolfDepth', trusted / 'CommitGolfDepth')
        (trusted / 'verifier/comparator.json').write_text(json.dumps(resource_config(production)) + '\n')
        for case in cases:
            candidate, work = owner / ('source-' + case.name), owner / ('run-' + case.name)
            candidate.mkdir()
            fixture, profile = case.fixture, depth_profile(case.fixture.model)
            source = (FIXTURES / fixture.source).read_text()
            try:
                config = production if case.production_scope else resource_config(production)
                (trusted / 'verifier/comparator.json').write_text(json.dumps(config) + '\n')
                template = ((root / 'verifier' / profile.template).read_text()
                            if case.production_scope else expected_template(case))
                (trusted / 'verifier' / profile.template).write_text(template)
                (candidate / 'programs.json').write_bytes(case.manifest)
                (candidate / 'Solution.lean').write_text(source)
                library_bytes = load_library(trusted, fixture.library)
                claim = dict.fromkeys(profile.claim_keys, 0)
                claim[profile.work_fields[0]], claim[profile.depth_fields[0]] = case.work, case.depth
                (candidate / 'claim.json').write_text(json.dumps(claim))
                policy = check(candidate, resource_model=fixture.model)
                if not policy['ok']:
                    raise ValueError(f'{case.name}: invalid fixed fixture: {policy["errors"]}')
                args = SimpleNamespace(work=work, commit=None, trusted=trusted, local=candidate,
                                       hide=[], repository=None, pr=None, track=fixture.track)
                report = verify.verify(args)
                full_log = ((work / 'verify.log').read_text(errors='replace')
                            if (work / 'verify.log').is_file() else '')
                with (owner / 'verify.log').open('a') as log:
                    log.write(f'\nResource-only client: {case.name}; expected {case.expected}; observed {report["status"]}\n')
                    log.write(full_log)
                    log.write('\n' + report.get('reason', '') + '\n')
                result = dict(case=case.name, expected=case.expected, observed=report['status'],
                              passed=case_passes(case, report, full_log, source),
                              work_bound=case.work, depth_bound=case.depth,
                              source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                              library_sha256=hashlib.sha256(library_bytes).hexdigest(),
                              manifest_sha256=hashlib.sha256(case.manifest).hexdigest(),
                              template_sha256=hashlib.sha256(template.encode()).hexdigest(),
                              config_sha256=hashlib.sha256((trusted / 'verifier/comparator.json').read_bytes()).hexdigest())
                results.append(result)
                record = json.dumps(dict(resource_only=True, **result))
                with (owner / 'verify.log').open('a') as log:
                    log.write(record + '\n')
                print(record, flush=True)
            finally:
                remove_owned(work, owner)
                remove_owned(candidate, owner)
    finally:
        remove_owned(trusted, owner)
        if protected_snapshot(root) != before:
            raise ValueError('production comparator/templates/score files changed during resource regression')
    passed = len(results) == len(cases) and all(result['passed'] for result in results)
    summary = json.dumps(dict(resource_only=True, passed=passed, cases=len(results),
                              production_snapshot_unchanged=True))
    with (owner / 'verify.log').open('a') as log:
        log.write(summary + '\n')
    print(summary, flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(run())
