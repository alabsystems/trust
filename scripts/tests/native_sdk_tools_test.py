#!/usr/bin/env python3
"""Inert provenance fixtures; these never qualify or execute a real SDK tool."""
import hashlib
import importlib.util
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

MODULE = Path(__file__).resolve().parents[1] / 'native_sdk_tools.py'
spec = importlib.util.spec_from_file_location('native_sdk_tools_tested', MODULE)
tools = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tools)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class NativeToolsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / 'source'
        (self.source / 'src/llvm-project').mkdir(parents=True)
        (self.source / 'src/llvm-project/version').write_text('inert LLVM fixture\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', 'commit', '-qm', 'inert fixture')
        self.commit = self.git('rev-parse', 'HEAD')
        self.tree = self.git('rev-parse', 'HEAD:src/llvm-project')
        self.stage = self.root / 'stage'
        self.stage.mkdir()
        self.stage_raw = b'{"status":"internal-release-ready","scope":"inert test fixture"}\n'
        (self.stage / 'tool-provenance.json').write_bytes(self.stage_raw)
        self.files = {}
        for name in sorted(tools.TOOLS):
            path = self.root / name
            raw = ('inert non-executed fixture ' + name).encode()
            path.write_bytes(raw)
            path.chmod(0o755)
            self.files[name] = {'path':str(path),'bytes':len(raw),'sha256':sha(raw)}
        self.built = {'passed':True,'source':self.commit,'llvm_tree':self.tree,
                      'files':self.files,'retained_inputs_unchanged':True,
                      'phases':[{'exit':0,'scope':'inert fixture'}]}
        self.smoke = {'passed':True,'source':self.commit,'llvm_tree':self.tree,
                      'actual_native_resource_worker':True,
                      'tool_sha256':{k:v['sha256'] for k,v in self.files.items()},
                      'phases':[{'exit':0,'scope':'inert fixture'}]}
        self.record = {'schema':tools.SCHEMA,'source':self.commit,'llvm_tree':self.tree,
                       'stage_provenance_sha256':sha(self.stage_raw),'files':self.files,
                       'retained_inputs_unchanged':True}

    def git(self, *args):
        return subprocess.check_output(['git','-c','core.hooksPath=/dev/null','-C',str(self.source),*args],text=True).strip()

    def materialize(self):
        for key, value in [('built_receipt', self.built), ('native_smoke', self.smoke)]:
            path = self.root / (key + '.json')
            raw = json.dumps(value).encode()
            path.write_bytes(raw)
            self.record[key] = {'path':str(path),'sha256':sha(raw)}
        self.path = self.root / 'qualified.json'
        raw = json.dumps(self.record).encode()
        self.path.write_bytes(raw)
        self.expected = sha(raw)

    def validate(self):
        return tools.validate(self.source,self.stage,self.commit,self.path,self.expected)

    def external_stage(self):
        original = self.source / 'build/test-host/stage2'
        original.parent.mkdir(parents=True)
        self.stage.rename(original)
        self.stage = original
        rows = {}
        for name in ('trustc', 'rustc', 'ty', 'rustdoc', 'helper'):
            path = self.stage / 'bin' / name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(('inert stage ' + name).encode())
            rows[name] = {'path':f'build/test-host/stage2/bin/{name}', 'sha256':sha(path.read_bytes())}
        receipt = {'schema':'trust.stage-tool-provenance.v2', 'status':'internal-release-ready',
                   'tool_binding_status':'ready', 'errors':[], 'path_scope':'repository-root-relative',
                   'stage_root':'build/test-host/stage2', 'host':'test-host', 'trust_from_trust':True,
                   'bootstrap_lineage':{'schema':'trust.bootstrap-lineage.v1', 'mode':'seed',
                       'status':'trust_from_trust', 'trust_from_trust':True, 'errors':[],
                       'validated_seed':{'materialization_status':'fresh-from-validated-archives'}},
                   'tools':[dict(rows['ty'],name='ty',status='bound',producer_sha256=rows['ty']['sha256'])],
                   'compiler':{'path':rows['trustc']['path'], 'compiler_sha256':rows['trustc']['sha256'],
                       'source_commit':self.commit, 'compatibility_alias':rows['rustc']['path'],
                       'compatibility_alias_sha256':rows['rustc']['sha256']},
                   'rustdoc_alias':rows['rustdoc'], 'proc_macro_helper':rows['helper']}
        self.accepted = self.root / 'accepted-stage.json'
        self.accepted.write_text(json.dumps(receipt))
        self.accepted_sha = sha(self.accepted.read_bytes())
        self.record['stage_provenance_sha256'] = self.accepted_sha
        self.stage_raw = b'{"status":"rejected","errors":["original mapper omission"]}\n'
        (self.stage / 'tool-provenance.json').write_bytes(self.stage_raw)
        self.materialize()

    def validate_external(self, **changes):
        values = dict(receipt_path=self.accepted, receipt_sha256=self.accepted_sha)
        values.update(changes)
        return tools.validate(self.source,self.stage,self.commit,self.path,self.expected,**values)

    def test_selected_external_stage_binds_actual_origin_and_survives_install(self):
        self.external_stage()
        self.validate_external()
        dest = self.root / 'external-new-seal'
        (dest / 'bin').mkdir(parents=True)
        tools.install(self.source,self.stage,self.commit,self.path,self.expected,dest,
                      receipt_path=self.accepted,receipt_sha256=self.accepted_sha)
        self.assertEqual((self.stage/'tool-provenance.json').read_bytes(),self.stage_raw)
        self.assertEqual((dest/'NATIVE-TOOLS.json').read_bytes(),self.path.read_bytes())

    def test_external_stage_cannot_select_wrong_hash_or_a_copy(self):
        self.external_stage()
        with self.assertRaisesRegex(tools.Refusal,'sha256 differs'):
            self.validate_external(receipt_sha256='0'*64)
        import shutil
        copied = self.root / 'copied-stage'
        shutil.copytree(self.stage,copied)
        with self.assertRaisesRegex(tools.Refusal,'original producer stage'):
            tools.validate(self.source,copied,self.commit,self.path,self.expected,
                           receipt_path=self.accepted,receipt_sha256=self.accepted_sha)

    def test_external_stage_compiler_tamper_is_not_licensed_by_component_hash(self):
        self.external_stage()
        (self.stage/'bin/trustc').write_bytes(b'different compiler')
        with self.assertRaisesRegex(tools.Refusal,'the compiler'):
            self.validate_external()

    def test_external_stage_pair_and_component_provenance_must_agree(self):
        self.external_stage()
        with self.assertRaisesRegex(tools.Refusal,'both receipt and sha256'):
            self.validate_external(receipt_sha256=None)
        self.record['stage_provenance_sha256']='0'*64
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'base-stage provenance'):
            self.validate_external()

    def test_external_cli_threads_selection_to_validate_and_install(self):
        self.external_stage()
        args = ['--source-root',str(self.source),'--stage',str(self.stage),
                '--commit',self.commit,'--record',str(self.path),'--sha256',self.expected,
                '--stage-provenance-receipt',str(self.accepted),
                '--stage-provenance-sha256',self.accepted_sha]
        dest = self.root / 'cli-new-seal'
        (dest/'bin').mkdir(parents=True)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(tools.main(['validate',*args]),0)
            self.assertEqual(tools.main(['install',*args,'--destination',str(dest)]),0)
        self.assertEqual((self.stage/'tool-provenance.json').read_bytes(),self.stage_raw)
        self.assertEqual((dest/'NATIVE-TOOLS.json').read_bytes(),self.path.read_bytes())

    def test_external_cli_refuses_duplicate_and_partial_selector(self):
        self.external_stage()
        args = ['validate','--source-root',str(self.source),'--stage',str(self.stage),
                '--commit',self.commit,'--record',str(self.path),'--sha256',self.expected,
                '--stage-provenance-receipt',str(self.accepted)]
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(tools.main(args),1)
            with self.assertRaises(SystemExit) as refused:
                tools.main([*args,'--stage-provenance-receipt',str(self.accepted)])
            self.assertEqual(refused.exception.code,2)

    def test_valid_distinct_component_installs_without_changing_origin(self):
        self.materialize()
        before = {p.name:p.read_bytes() for p in self.stage.iterdir()}
        dest = self.root / 'new-seal'
        (dest / 'bin').mkdir(parents=True)
        tools.install(self.source,self.stage,self.commit,self.path,self.expected,dest)
        self.assertEqual(before,{p.name:p.read_bytes() for p in self.stage.iterdir()})
        self.assertEqual((dest/'NATIVE-TOOLS.json').read_bytes(),self.path.read_bytes())
        for name,row in self.files.items():
            self.assertEqual(sha((dest/'bin'/name).read_bytes()),row['sha256'])

    def test_record_hash_mismatch(self):
        self.materialize(); self.expected = '0'*64
        with self.assertRaisesRegex(tools.Refusal,'digest'): self.validate()

    def test_duplicate_authority_field(self):
        self.materialize(); raw=self.path.read_text().replace('{','{"source":"duplicate",',1)
        self.path.write_text(raw); self.expected=sha(raw.encode())
        with self.assertRaisesRegex(tools.Refusal,'duplicate'): self.validate()

    def test_wrong_compiler_source(self):
        self.record['source']='0'*40; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'compiler source'): self.validate()

    def test_wrong_llvm_tree(self):
        self.record['llvm_tree']='0'*40; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'LLVM source'): self.validate()

    def test_changed_base_provenance(self):
        self.materialize(); (self.stage/'tool-provenance.json').write_text('{"status":"internal-release-ready","changed":true}')
        with self.assertRaisesRegex(tools.Refusal,'base-stage provenance'): self.validate()

    def test_inputs_not_retained(self):
        self.record['retained_inputs_unchanged']=False; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'retain'): self.validate()

    def test_real_build_nonzero_cannot_be_relabelled(self):
        self.built['phases'][0]['exit']=101; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'nonzero'): self.validate()

    def test_boolean_is_not_an_actual_exit(self):
        self.smoke['phases'][0]['exit']=False; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'non-actual'): self.validate()

    def test_version_only_smoke_is_not_native_qualification(self):
        self.smoke['actual_native_resource_worker']=False; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'actual native resource worker'): self.validate()

    def test_smoke_of_other_tool_bytes_refused(self):
        self.smoke['tool_sha256']['rust-lld']='0'*64; self.materialize()
        with self.assertRaisesRegex(tools.Refusal,'these tool bytes'): self.validate()

    def test_payload_tamper_refused(self):
        self.materialize(); (self.root/'rust-lld').write_bytes(b'changed')
        with self.assertRaisesRegex(tools.Refusal,'size|digest'): self.validate()

    def test_symlink_payload_refused(self):
        self.materialize(); p=self.root/'rust-lld'; p.rename(self.root/'saved'); p.symlink_to(self.root/'saved')
        with self.assertRaises((tools.Refusal,OSError)): self.validate()

    def test_nonexecutable_payload_refused(self):
        self.materialize(); (self.root/'dsymutil').chmod(0o644)
        with self.assertRaisesRegex(tools.Refusal,'not executable'): self.validate()

    def test_existing_seal_tool_is_never_overwritten(self):
        self.materialize(); dest=self.root/'existing'; (dest/'bin').mkdir(parents=True)
        p=dest/'bin/rust-lld'; p.write_text('preserve existing bytes')
        with self.assertRaisesRegex(tools.Refusal,'overwrite'):
            tools.install(self.source,self.stage,self.commit,self.path,self.expected,dest)
        self.assertEqual(p.read_text(),'preserve existing bytes')
        self.assertFalse((dest/'bin/dsymutil').exists(), 'reject before installing any missing tool')
        self.assertFalse((dest/'NATIVE-TOOLS.evidence').exists())

    def test_identical_existing_lld_is_retained_while_missing_dsymutil_is_installed(self):
        self.materialize(); dest=self.root/'mixed'; (dest/'bin').mkdir(parents=True)
        existing=dest/'bin/rust-lld'
        existing.write_bytes((self.root/'rust-lld').read_bytes()); existing.chmod(0o755)
        original=tools.identity(existing.lstat())
        tools.install(self.source,self.stage,self.commit,self.path,self.expected,dest)
        self.assertEqual(tools.identity(existing.lstat()),original,'retained file is never overwritten')
        self.assertEqual(sha((dest/'bin/dsymutil').read_bytes()),self.files['dsymutil']['sha256'])
        index=json.loads((dest/'NATIVE-TOOLS.evidence/INDEX.json').read_bytes())
        self.assertEqual(index['retained_existing_tools'],['rust-lld'])
        self.assertEqual(index['installed_tools'],['dsymutil'])

    def test_existing_link_or_nonexecutable_cannot_be_accepted_by_equal_bytes(self):
        self.materialize()
        for case in ['symlink','nonexecutable']:
            with self.subTest(case=case):
                dest=self.root/case; (dest/'bin').mkdir(parents=True)
                target=dest/'bin/rust-lld'
                if case=='symlink':target.symlink_to(self.root/'rust-lld')
                else:target.write_bytes((self.root/'rust-lld').read_bytes());target.chmod(0o644)
                with self.assertRaises((tools.Refusal,OSError)):
                    tools.install(self.source,self.stage,self.commit,self.path,self.expected,dest)
                self.assertFalse((dest/'bin/dsymutil').exists())
                self.assertFalse((dest/'NATIVE-TOOLS.evidence').exists())


if __name__ == '__main__':
    unittest.main()
