#!/usr/bin/env python3
"""Physical-input continuation controls, all authored UNRUN in this proposal.

Toy local Git/files/archive fixtures exercise the actual source capture and
physical verification functions. They are never native producer/owner evidence.
No source-only AST observation may be reported as one of these controls passing.
"""
from __future__ import annotations
import hashlib
import importlib.util
import io
import json
import os
import stat
from pathlib import Path
import tarfile
import tempfile
import time
import unittest

path = Path(__file__).with_name('linux_root_input_fixture.py')
spec = importlib.util.spec_from_file_location('input_fixture',path)
fixture = importlib.util.module_from_spec(spec)
# -B suppresses bytecode writes, not reads. Execute this exact fixture source;
# an unchecked-hash/timestamp pyc must not restore the old broad census.
fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC)
try:
    info = os.fstat(fd)
    if not stat.S_ISREG(info.st_mode) or info.st_size > 4 * 1024 * 1024:
        raise ValueError('input fixture is not bounded regular source')
    with os.fdopen(fd, 'rb', closefd=False) as stream:
        raw_fixture = stream.read(4 * 1024 * 1024 + 1)
    if len(raw_fixture) > 4 * 1024 * 1024:
        raise ValueError('input fixture exceeded its finite source bound')
finally:
    os.close(fd)
exec(compile(raw_fixture,str(path),'exec',dont_inherit=True),fixture.__dict__)
LOADER,CLOSURE,AUTH = fixture.modules()
R,C,A = CLOSURE.records,CLOSURE.committed,CLOSURE.archives


class PhysicalContinuationTests(unittest.TestCase):
    def make(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        return fixture.PhysicalFixture(Path(temporary.name).resolve(),LOADER,CLOSURE,AUTH)

    def test_actual_capture_chunks_seals_and_postclose_files_join_without_admission(self):
        value = self.make()
        result = CLOSURE.verify_closed_inputs(*value.complete())
        self.assertTrue(result['passed_declared_physical_joins'])
        self.assertFalse(result['complete_original_input_closure'])
        self.assertFalse(result['admitted_root_seed'])
        self.assertFalse(result['counts_as_trust_stage0_evidence'])
        self.assertEqual(len(result['canonical_installers']),5)
        self.assertEqual(len(result['external_archive_payloads']),6)
        self.assertEqual(len(result['refusals']),len(CLOSURE.OPEN_FAMILIES))
        self.assertLessEqual(result['unique_metadata_bytes'],64*1024*1024)

    def test_actual_added_extracted_source_refuses_before_diverse_ddc_seal(self):
        value = self.make()
        value.session.seal('before')
        value.common_files()
        value.session.seal('private-import')
        value.session.seal('common-self-host')
        fixture.write(value.work/'cargo-home/registry/src/provider/new/crate.rs',b'changed source')
        with self.assertRaisesRegex(ValueError,'BEFORE diverse DDC'):
            value.session.seal('common-ddc')
        self.assertEqual([row['stage'] for row in value.live.seals],['before','private-import','common-self-host'])

    def test_initial_private_copy_cannot_substitute_supplier_bytes(self):
        value = self.make()
        fixture.write(value.cache/'registry/cache/provider/pkg.crate',b'original supplier')
        value.session.seal('before')
        value.common_files()
        fixture.write(value.work/'cargo-home/registry/cache/provider/pkg.crate',b'changed private copy')
        with self.assertRaisesRegex(ValueError,'initial private Cargo copy differs'):
            value.session.seal('private-import')
        self.assertEqual([row['stage'] for row in value.live.seals],['before'])

    def test_actual_changed_config_refuses_before_diverse_ddc_seal(self):
        value = self.make()
        value.session.seal('before')
        value.common_files()
        value.session.seal('private-import')
        value.session.seal('common-self-host')
        fixture.write(value.work/'bootstrap.self-host.toml',b'changed compiler config')
        with self.assertRaisesRegex(ValueError,'BEFORE diverse DDC'):
            value.session.seal('common-ddc')

    def test_actual_oracle_change_after_closure_is_not_json_equality(self):
        value = self.make()
        arguments = value.complete()
        fixture.write(Path(value.values['ddc_sysroot'])/'bin/rustc',b'wrong actual oracle',0o755)
        with self.assertRaisesRegex(ValueError,'input tree changed'):
            CLOSURE.verify_closed_inputs(*arguments)

    def test_actual_mode_change_after_closure_refuses(self):
        value = self.make()
        arguments = value.complete()
        value.tool.chmod(0o644)
        with self.assertRaisesRegex(ValueError,'file/mode/resolution'):
            CLOSURE.verify_closed_inputs(*arguments)

    def test_actual_source_byte_change_after_closure_refuses(self):
        value = self.make()
        arguments = value.complete()
        fixture.write(value.source/'main.rs',b'fn changed() {}\n')
        with self.assertRaisesRegex(ValueError,'committed blob'):
            CLOSURE.verify_closed_inputs(*arguments)

    def test_original_owner_arguments_cannot_be_replaced_by_candidate_paths(self):
        value = self.make()
        owner,record,documents,loader = value.complete()
        record['native_arguments']['--source-root'] = '/candidate/alternate-source'
        with self.assertRaisesRegex(ValueError,'argument custody'):
            CLOSURE.verify_closed_inputs(owner,record,documents,loader)

    def test_live_seal_digest_cannot_be_rewritten_by_new_index(self):
        value = self.make()
        owner,record,documents,loader = value.complete()
        record['input_seals'][0]['reference']['sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'live seals'):
            CLOSURE.verify_closed_inputs(owner,record,documents,loader)

    def test_retained_chunk_corruption_is_not_a_second_capture(self):
        value = self.make()
        arguments = value.complete()
        path = next((value.work/'physical-input-closure').glob('*.json'))
        path.write_bytes(b'[]\n')
        with self.assertRaisesRegex(ValueError,'digest/size'):
            CLOSURE.verify_closed_inputs(*arguments)

    def test_installer_execution_cannot_mutate_its_original_source_bytes(self):
        value = self.make()
        arguments = value.complete()
        install = next((value.work/'unpack').rglob('install.sh'))
        fixture.write(install,b'#!/bin/sh\nexit 7\n',0o755)
        with self.assertRaisesRegex(ValueError,'input tree changed'):
            CLOSURE.verify_closed_inputs(*arguments)

    def test_same_original_endpoint_is_not_renewed_after_capture(self):
        value = self.make()
        owner,record,documents,loader = value.complete()
        owner.end = time.monotonic()-1
        with self.assertRaisesRegex(ValueError,'original input-closure deadline'):
            CLOSURE.verify_closed_inputs(owner,record,documents,loader)

    def test_wrong_original_seal_endpoint_refuses(self):
        value = self.make()
        owner,record,documents,loader = value.complete()
        owner.end += 1
        with self.assertRaisesRegex(ValueError,'live seals/end'):
            CLOSURE.verify_closed_inputs(owner,record,documents,loader)

    def test_source_stage_reorder_cannot_obtain_a_seal(self):
        value = self.make()
        with self.assertRaisesRegex(ValueError,'missing/reordered'):
            value.session.seal('common-ddc')
        self.assertEqual(value.live.seals,[])

    def test_old_file_only_genesis_path_remains_unconditionally_closed(self):
        with self.assertRaisesRegex(ValueError,'pending'):
            AUTH.initialization.validate_completed_producer(Path('/candidate'),
                'x86_64-unknown-linux-gnu',{'passed':True,'admitted_root_seed':True})


class CommittedInputTests(unittest.TestCase):
    def capture(self,root,commit):
        store = R.ChunkStore(root.parent/'proof',time.monotonic()+30,create=True)
        def collect(path,commit,tree,entries,raw):
            actual = C.committed_rows(path,entries,commit,tree,raw,store.end)
            self.capture_value = {'repository':'.','commit':commit,'tree':tree,
                'commit_object_hex':actual['commit_object_hex'],
                'files':store.rows(actual['files']),'directories':store.rows(actual['directories'])}
        AUTH.source_snapshot(root,commit,physical=collect,deadline=store.end)
        return store,self.capture_value

    def repository(self,root):
        root.mkdir()
        fixture.write(root/'file',b'original\n')
        fixture.write(root/'nested/git_mode',b'legal field-like filename\n')
        (root/'link').symlink_to('file')
        fixture.git(root,'init','-q')
        fixture.git(root,'add','.')
        fixture.git(root,'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','original')
        return fixture.git(root,'rev-parse','HEAD')

    def test_actual_git_commit_and_directory_order_reconstruct_after_close(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()/'repo'
            commit = self.repository(root)
            store,capture = self.capture(root,commit)
            rows = C.verify_providers(root,[capture],store,store.end,commit)
            self.assertEqual({row['path'] for row in rows['.']},{'file','link','nested/git_mode'})

    def test_literal_source_link_target_is_bound_to_committed_blob(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()/'repo'
            commit = self.repository(root)
            store,capture = self.capture(root,commit)
            (root/'link').unlink()
            (root/'link').symlink_to('nested/git_mode')
            with self.assertRaisesRegex(ValueError,'literal link'):
                C.verify_providers(root,[capture],store,store.end,commit)

    def test_nonexecutability_mode_is_preserved_beyond_git_exec_bit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()/'repo'
            commit = self.repository(root)
            store,capture = self.capture(root,commit)
            (root/'file').chmod(0o600)
            with self.assertRaisesRegex(ValueError,'file/mode/literal link'):
                C.verify_providers(root,[capture],store,store.end,commit)

    def test_committed_object_bytes_cannot_be_asserted_by_digest_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()/'repo'
            commit = self.repository(root)
            store,capture = self.capture(root,commit)
            capture['commit_object_hex'] = b'tree '.hex()
            with self.assertRaisesRegex(ValueError,'commit object'):
                C.verify_providers(root,[capture],store,store.end,commit)

    def test_missing_recursive_provider_is_not_a_closed_source_projection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()/'repo'
            commit = self.repository(root)
            store,capture = self.capture(root,commit)
            fake = {**capture,'repository':'unconnected-provider'}
            with self.assertRaisesRegex(ValueError,'unconnected provider'):
                C.verify_providers(root,[capture,fake],store,store.end,commit)


class CanonicalMetadataTests(unittest.TestCase):
    def test_duplicate_json_keys_refuse(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):
            R.decode(b'{"a":1,"a":2}\n')

    def test_newline_or_whitespace_variants_are_not_canonical(self):
        for raw in (b'{"a": 1}\n',b'{"a":1}',b'{"a":NaN}\n'):
            with self.assertRaises(ValueError):
                R.decode(raw)

    def test_one_actual_oversized_proof_refuses_without_reading_it(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'too-large.json'
            with path.open('wb') as stream:
                stream.truncate(R.PROOF_LIMIT+1)
            with self.assertRaisesRegex(ValueError,'bound'):
                R.MetadataBudget(time.monotonic()+10).read(path)

    def test_aggregate_is_not_renewed_for_each_chunk(self):
        with tempfile.TemporaryDirectory() as directory:
            budget = R.MetadataBudget(time.monotonic()+30)
            for index in range(16):
                path = Path(directory)/str(index)
                fixture.write(path,b' '*R.PROOF_LIMIT)
                budget.read(path)
            path = Path(directory)/'overflow'
            fixture.write(path,b'x')
            with self.assertRaisesRegex(ValueError,'aggregate'):
                budget.read(path)

    def test_merkle_row_chunk_references_cannot_escape_store(self):
        with tempfile.TemporaryDirectory() as directory:
            store = R.ChunkStore(Path(directory).resolve(),time.monotonic()+10)
            with self.assertRaisesRegex(ValueError,'reference'):
                store.get({'sha256':'../candidate','bytes':1})

    def test_special_input_fifo_is_never_opened_as_payload(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            os.mkfifo(root/'fifo')
            with self.assertRaisesRegex(ValueError,'special input'):
                R.tree(root,time.monotonic()+10)

    def test_parent_directory_resolution_link_is_literal_and_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            fixture.write(root/'real/file',b'payload')
            (root/'alias').symlink_to('real',target_is_directory=True)
            value,_ = R.binding(root/'alias/file',time.monotonic()+10)
            self.assertEqual(value['links'][0]['target'],'real')
            self.assertEqual(value['resolved'],str(root/'real/file'))


class ArchiveSourceTests(unittest.TestCase):
    def test_actual_archive_payload_extra_source_and_mode_changes_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            sha = fixture.make_archive(root/'p.crate',[('p',None,0o755),('p/lib.rs',b'original',0o644)],'w:gz')
            source = root/'source'
            fixture.write(source/'lib.rs',b'original')
            end = time.monotonic()+10
            self.assertTrue(A.archive_projection(root/'p.crate',R.tree(source,end),end,prefix='p'))
            fixture.write(source/'extra.rs',b'not in archive')
            with self.assertRaisesRegex(ValueError,'unbound extra'):
                A.archive_projection(root/'p.crate',R.tree(source,end),end,prefix='p')
            (source/'extra.rs').unlink()
            (source/'lib.rs').chmod(0o755)
            with self.assertRaisesRegex(ValueError,'mode/literal link'):
                A.archive_projection(root/'p.crate',R.tree(source,end),end,prefix='p')

    def test_archive_dotdot_and_special_member_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            fixture.make_archive(root/'escape.tar.xz',[('p/../escape',b'bad',0o644)])
            with self.assertRaisesRegex(ValueError,'escaping'):
                A.archive_rows(root/'escape.tar.xz',time.monotonic()+10)
            with tarfile.open(root/'fifo.tar.xz','w:xz') as archive:
                info = tarfile.TarInfo('fifo')
                info.type = tarfile.FIFOTYPE
                archive.addfile(info)
            with self.assertRaisesRegex(ValueError,'special'):
                A.archive_rows(root/'fifo.tar.xz',time.monotonic()+10)

    def test_extracted_registry_source_must_match_lock_pinned_archive(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            cargo = root/'cargo'
            source = cargo/'registry/src/provider/p-1.0.0'
            fixture.write(source/'lib.rs',b'original')
            sha = fixture.make_archive(cargo/'registry/cache/provider/p-1.0.0.crate',
                [('p-1.0.0',None,0o755),('p-1.0.0/lib.rs',b'original',0o644)],'w:gz')
            fixture.write(source/'.cargo-checksum.json',json.dumps({'package':sha,
                'files':{'lib.rs':hashlib.sha256(b'original').hexdigest()}}).encode())
            result = A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)
            self.assertEqual(result['verified_packages'],1)
            fixture.write(source/'lib.rs',b'tampered')
            with self.assertRaisesRegex(ValueError,'archive payload differs'):
                A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_registry_generated_marker_is_not_a_hiding_place_for_extra_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            cargo = root/'cargo'
            source = cargo/'registry/src/provider/p-1.0.0'
            fixture.write(source/'lib.rs',b'original')
            sha = fixture.make_archive(cargo/'registry/cache/provider/p-1.0.0.crate',
                [('p-1.0.0',None,0o755),('p-1.0.0/lib.rs',b'original',0o644)],'w:gz')
            fixture.write(source/'.cargo-checksum.json',json.dumps({'package':sha,
                'files':{'lib.rs':hashlib.sha256(b'original').hexdigest()}}).encode())
            fixture.write(source/'.cargo-ok',b'{"v":1,"extra":"source"}')
            with self.assertRaisesRegex(ValueError,'Cargo marker'):
                A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_registry_generated_checksum_extra_keys_and_executable_mode_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            cargo = Path(directory).resolve()/'cargo'
            source = cargo/'registry/src/provider/p-1.0.0'
            fixture.write(source/'lib.rs',b'original')
            sha = fixture.make_archive(cargo/'registry/cache/provider/p-1.0.0.crate',
                [('p-1.0.0',None,0o755),('p-1.0.0/lib.rs',b'original',0o644)],'w:gz')
            checksum = {'package':sha,'files':{'lib.rs':hashlib.sha256(b'original').hexdigest()}}
            fixture.write(source/'.cargo-checksum.json',json.dumps({**checksum,'extra':'source'}).encode())
            with self.assertRaisesRegex(ValueError,'extra fields or executable'):
                A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)
            fixture.write(source/'.cargo-checksum.json',json.dumps(checksum).encode(),0o755)
            with self.assertRaisesRegex(ValueError,'extra fields or executable'):
                A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_unpinned_registry_source_refuses_even_with_checksum_marker(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            fixture.write(root/'registry/src/provider/unknown-1/lib.rs',b'unknown')
            with self.assertRaisesRegex(ValueError,'not pinned'):
                A.registry_sources(root,{},time.monotonic()+10)


class AdditionalBoundaries(unittest.TestCase):
    def test_same_bounded_chunk_reference_consumes_aggregate_once(self):
        with tempfile.TemporaryDirectory() as directory:
            store = R.ChunkStore(Path(directory).resolve(),time.monotonic()+10)
            reference = store.put([{'original':'row'}])
            once = store.budget.total
            self.assertEqual(store.get(reference),[{'original':'row'}])
            self.assertEqual(store.budget.total,once)

    def test_actual_oversized_pax_header_is_refused_before_payload_parsing(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'pax.tar'
            with tarfile.open(path,'w') as archive:
                info = tarfile.TarInfo('pax')
                info.type = tarfile.XHDTYPE
                info.size = R.PROOF_LIMIT+1
                archive.addfile(info,io.BytesIO(b'x'*info.size))
            with self.assertRaisesRegex(ValueError,'PAX metadata exceeds'):
                A.archive_rows(path,time.monotonic()+10)

    def test_real_gitlink_children_are_required_by_committed_parent_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            helper = CommittedInputTests()
            parent,child = root/'parent',root/'child'
            helper.repository(parent)
            helper.repository(child)
            fixture.git(parent,'-c','protocol.file.allow=always','submodule','add','-q',str(child),'provider')
            fixture.git(parent,'-c','user.name=Fixture','-c','user.email=fixture@example.invalid',
                        'commit','-qm','recursive physical provider')
            commit = fixture.git(parent,'rev-parse','HEAD')
            store = R.ChunkStore(root/'proof',time.monotonic()+30,create=True)
            captures = []
            def collect(path,commit,tree,entries,raw):
                observed = C.committed_rows(path,entries,commit,tree,raw,store.end)
                captures.append({'repository':path.relative_to(parent).as_posix(),'commit':commit,'tree':tree,
                    'commit_object_hex':observed['commit_object_hex'],
                    'files':store.rows(observed['files']),'directories':store.rows(observed['directories'])})
            AUTH.source_snapshot(parent,commit,physical=collect,deadline=store.end)
            self.assertEqual(set(C.verify_providers(parent,captures,store,store.end,commit)),{'.','provider'})
            with self.assertRaisesRegex(ValueError,'provider is absent'):
                C.verify_providers(parent,captures[:1],store,store.end,commit)


if __name__ == '__main__':
    unittest.main()
