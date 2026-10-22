"""Benign extracted pin tests only; never import or run operator main."""
from pathlib import Path
import ast,hashlib,tempfile,unittest
P=Path(__file__).with_name('execute-host.py');tree=ast.parse(P.read_text());fn=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='pin'];assert len(fn)==1
scope={'Path':Path,'hashlib':hashlib};exec(compile(ast.Module(body=fn,type_ignores=[]),str(P),'exec'),scope)
class PinTests(unittest.TestCase):
 def test_path_and_string_equivalent(self):
  with tempfile.TemporaryDirectory() as root:
   p=Path(root)/'source';p.write_bytes(b'abc');a=scope['pin'](p);b=scope['pin'](str(p));self.assertEqual(a,b);self.assertEqual(a,dict(path=str(p),size=3,sha256=hashlib.sha256(b'abc').hexdigest()))
 def test_missing_path_and_string_refuse(self):
  with tempfile.TemporaryDirectory() as root:
   p=Path(root)/'missing'
   for value in [p,str(p)]:
    with self.subTest(kind=type(value).__name__),self.assertRaises(FileNotFoundError):scope['pin'](value)
if __name__=='__main__':unittest.main(verbosity=2)
