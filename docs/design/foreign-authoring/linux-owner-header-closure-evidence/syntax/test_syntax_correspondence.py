"""Benign byte/monitor-association controls; never runs GCC or preprocessing."""
import ast,copy,hashlib,os,stat,tempfile,unittest
from pathlib import Path
SOURCE=Path(__file__).with_name('collect_syntax.py')
module=ast.parse(SOURCE.read_text())
functions=[node for node in module.body if isinstance(node,ast.FunctionDef) and node.name in {'need','admit_dependency','require_exact_dependencies'}]
assert len(functions)==3
scope={'hashlib':hashlib,'os':os,'stat':stat}
exec(compile(ast.Module(body=functions,type_ignores=[]),str(SOURCE),'exec'),scope)
admit=scope['admit_dependency']
class Association(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='header-association-benign-')
        self.addCleanup(self.temp.cleanup)
        self.path=Path(self.temp.name)/'native-build.log';self.data=b'owner_header_abi: /usr/include/stdlib.h\n';self.path.write_bytes(self.data)
        st=self.path.stat();self.row={'relative_path':'native-build.log','path':str(self.path),'file_class':'sidefile_log','limit_bytes':16777216,'observed_peak_bytes':len(self.data),'hash_is_prefix':False,'size_before':len(self.data),'size_after':len(self.data),'hashed_bytes':len(self.data),'sha256':hashlib.sha256(self.data).hexdigest(),'device':st.st_dev,'inode':st.st_ino}
    def refuse(self,rows):
        with self.assertRaises(SystemExit):admit(self.path,rows)
    def test_complete_matching_observation(self):
        raw,pin,row=admit(self.path,[self.row]);self.assertEqual(raw,self.data);self.assertIs(row,self.row);self.assertEqual(pin['sha256'],self.row['sha256'])
    def test_missing_observation(self):self.refuse([])
    def test_duplicate_observation(self):self.refuse([self.row,self.row.copy()])
    def test_wrong_path(self):
        row=self.row.copy();row['path']+='.other';self.refuse([row])
    def test_prefix_refuses(self):
        row=self.row.copy();row['hash_is_prefix']=True;self.refuse([row])
    def test_each_size_mismatch(self):
        for key in ['size_before','size_after','hashed_bytes']:
            with self.subTest(key=key):
                row=self.row.copy();row[key]+=1;self.refuse([row])
    def test_wrong_hash(self):
        row=self.row.copy();row['sha256']='0'*64;self.refuse([row])
    def test_wrong_class_or_cap(self):
        for key,value in [('file_class','link_map'),('limit_bytes',134217728)]:
            with self.subTest(key=key):
                row=self.row.copy();row[key]=value;self.refuse([row])
    def test_other_file_object_refuses(self):
        row=self.row.copy();row['inode']+=1;self.refuse([row])
    def test_changed_bytes_before_finalization(self):
        _,before,_=admit(self.path,[self.row]);self.path.write_bytes(self.data.replace(b'owner',b'other'));self.refuse([self.row])
    def test_actual_one_mib_admission(self):
        self.path.write_bytes(b'x'*1048577);st=self.path.stat();row=self.row.copy();row.update(size_before=st.st_size,size_after=st.st_size,hashed_bytes=st.st_size,observed_peak_bytes=st.st_size,sha256=hashlib.sha256(b'x'*1048577).hexdigest());self.refuse([row])
class FrozenSet(unittest.TestCase):
    def test_exact_set_order_independent(self):scope['require_exact_dependencies'](['/a','/b'],['/b','/a'])
    def test_missing_or_extra_dependency_refuses(self):
        for actual in [['/a'],['/a','/b','/c']]:
            with self.subTest(actual=actual),self.assertRaises(SystemExit):scope['require_exact_dependencies'](actual,['/a','/b'])
    def test_duplicate_dependency_refuses(self):
        with self.assertRaises(SystemExit):scope['require_exact_dependencies'](['/a','/a'],['/a'])
if __name__=='__main__':unittest.main(verbosity=2)

