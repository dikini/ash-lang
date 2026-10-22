"""Benign tests only. Explicit guards prohibit any actual fork or execve."""
from pathlib import Path
import os,sys,hashlib,json,importlib.util,unittest
from unittest.mock import patch
R=Path(__file__).parent
expected={'PATH':'/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin','LANG':'C','LC_ALL':'C'}
assert dict(os.environ)==expected and sys.flags.isolated and sys.flags.no_site
sys.path.insert(0,str(R))
import diagnostic as d
spec=importlib.util.spec_from_file_location('owner_diagnostic_tests',R/'test_diagnostic.py');tests=importlib.util.module_from_spec(spec);spec.loader.exec_module(tests)
suite=unittest.defaultTestLoader.loadTestsFromModule(tests)
with patch.object(d.os,'fork',side_effect=AssertionError('actual fork prohibited in safe suite')),patch.object(d.os,'execve',side_effect=AssertionError('actual exec prohibited in safe suite')):
 result=unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
