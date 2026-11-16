#!/usr/bin/env python3
"""Current operational namespace controls; these tests never qualify an SDK."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

SCRIPTS=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);sys.modules[name]=value;spec.loader.exec_module(value)
    return value
api=load('current_targo_test',SCRIPTS/'sdk_targo_current_component.py')
legacy=load('legacy_targo_test',SCRIPTS/'sdk_targo_component.py')

class CurrentOperational(unittest.TestCase):
    def test_current_schema_cannot_be_a_historical_full_sdk_overlay(self):
        with self.assertRaises(legacy.Refusal):
            legacy.record_shape({'schema':api.SCHEMA,'whole_sdk_ready':False,'verified_tool_map':False})
        self.assertNotEqual(api.OPERATIONAL_SOURCE,legacy.COMPILER_SOURCE)
        self.assertNotEqual(api.OPERATIONAL_COMPILER,legacy.COMPILER_SHA256)

    def test_filename_inventory_capability_is_required_without_a_source_blacklist(self):
        cap=api.FILENAME_INVENTORY_CAPABILITY.encode()+b'\n'
        api.require_filename_inventory_capability(b'encoded-dep-info-version: 7\n'+cap)
        for raw in [b'encoded-dep-info-version: 5\n'+cap,
                    b'encoded-dep-info-version: 6\n'+cap,
                    b'encoded-dep-info-version: 6\n',
                    b'encoded-dep-info-version: 6\n'+cap+cap,
                    b'encoded-dep-info-version: 6\nencoded-dep-info-version: 7\n'+cap]:
            with self.assertRaises(ValueError):
                api.require_filename_inventory_capability(raw)

    def test_duplicate_phase_fields_do_not_get_last_writer_authority(self):
        with self.assertRaises(ValueError):
            api.json_document(b'{"whole_sdk_ready":false,"whole_sdk_ready":true}')

    def test_only_alias_pair_may_change_in_the_sdk_inventory(self):
        before=[{'path':'bin/cargo','kind':'file','mode':493,'bytes':1,'sha256':'a'},
                {'path':'bin/targo','kind':'file','mode':493,'bytes':1,'sha256':'a'},
                {'path':'lib/std','kind':'file','mode':420,'bytes':1,'sha256':'retained'}]
        after=api.expected_inventory(before,{'bytes':2,'sha256':'new'})
        self.assertEqual(next(x for x in after if x['path']=='lib/std'),before[-1])
        self.assertEqual({x['sha256'] for x in after if x['path'].startswith('bin/')},{'new'})

    def test_phase_streams_cannot_escape_the_evidence_or_change_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);(root/'case.stdout').write_bytes(b'real');(root/'case.stderr').write_bytes(b'')
            phase={'argv':['/selected/targo','--version'],'cwd':'/owned','exit':0,'retired':True,
                   'stdout':{'path':'case.stdout','sha256':api.sha(b'real')},
                   'stderr':{'path':'case.stderr','sha256':api.sha(b'')}}
            self.assertEqual(api.read_phase(root,phase)['stdout'],b'real')
            (root/'case.stdout').write_bytes(b'forged')
            with self.assertRaises(ValueError):api.read_phase(root,phase)
            phase['stdout']['path']='../other'
            with self.assertRaises(ValueError):api.read_phase(root,phase)

if __name__=='__main__':unittest.main()
