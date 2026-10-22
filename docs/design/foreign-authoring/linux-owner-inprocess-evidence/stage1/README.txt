# Exact selected-source compiler command: review only

No compiler/build/generation/link/startup has run. tuple.json is the ordered
command/retention specification. compiler-build.monitor.json contains a fully
concrete Stage 1 argv, executable pin, cwd, exact environment, input pins,
private output/watch parent and shared-cache path. It has no opaque fields.
PR100 is retained at 2ac8c393846715249de5a475a65e47bf1309bb54.
The exact retained contract byte pin is
27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e.
Independent Stage 1 tuple clearance and an explicit root build assignment remain
required; retention does not authorize a build or startup.

Before assignment: independently review this tuple; verify PR100 actual retained
parent/tree/contract, record the retained commit, confirm the sole Cargo slot
and existing shared cache are available, and obtain root's exact Stage 1 build
assignment. The directory/source/tool correspondence checks performed here are
read-only preparation, not evidence that offline compilation succeeds. Missing
offline inputs, different tool/config bytes or unsupported monitor setup refuse;
no downloads, changed limits, fingerprint bypass or cached Borrow compiler reuse
are fallback permissions.

verify_inputs.py checks every selected Git blob's full size/SHA256/Git blob ID,
path set and executable mode, all 2784 files / 96,452,672 bytes; it also streams
the source archive and tool/native/config/monitor/interpreter pins. The complete
archive manifest is separate from the 177-file build.rs content census. The
verifier checks absence of extra applicable parent Cargo configurations. Its
before/after phase uses the same checks. It does not modify any source, invoke
children or run Rust tools. All hashes are byte correspondence, not protection
against hostile concurrent writers: the private, unchanged source/tool context
and sole-operator freeze are explicit premises. The selected snapshot is never
rewritten to match PR100 or current Borrow sources.

Interpreter /usr/bin/python3.14 is pinned directly. The monitor remains the
reviewed14aae431 source; its process-local subreaper and single owned group use
actual waits/reaping. Sampled sidefile checks and finite retained output are not
hard disk/CPU/memory containment; the shared cache is outside the sampled private
watch tree. Unexpected escaped descendants or pending reaping cannot be success.
The compiler is a tool/intermediate: no128MiB final-image cap applies. Capture
its actual post-success hash by streaming only after source-after verification;
do not prefill that hash using the current cached compiler. Tool/native/archive
sizes and hashes are explicit in preflight-inputs and referenced manifests.

Stage 1 ends at compiler byte observation. The actual build.rs fingerprint must
be derived by that build from exact Cargo target/profile/feature/config inputs
and rustc verbose version; the content-only census is not a full fingerprint.
A later ordinary-host config must pin the observed compiler and exact selected
input tuple before assignment. Actual generated .ash-build Cargo/name/bridge/
private payload/expected facts must be retained and frozen after that build.
Only then may a separately assigned root-only static relink use those exact
observed inputs. Neither the compiler command nor the old scalar flags approve
ownerful execution or promise a no-runtime-loading closure.

## Reviewed-tuple repair boundaries

PR100 is actually retained at 2ac8c393846715249de5a475a65e47bf1309bb54;
the contract byte pin remains27430b69. Every outer Python command now uses
canonical Python3.14 with `-I -S -B` and an explicit three-variable environment
map via the operator's trusted subprocess launcher. Do not inherit the parent
process environment. No PYTHON*, LD_PRELOAD or LD_LIBRARY_PATH is passed; user
site/site initialization is disabled. The read-only verifier also checks its
Python isolation flags and exact environment. This presumes a trusted operator
launcher/installed interpreter before Python itself starts; an inherited shell
command is not an equivalent launch specification.

The operator must first compare tuple/manifest/preflight/verifier/config/monitor/
interpreter hashes with the independent review and root's exact assignment.
preflight-inputs.json cannot authenticate itself. The external reviewed hashes
are the trust anchor; file self-consistency is the next, separate check.

Default linker correspondence now pins cc/gcc symlink chains, GCC collect2 and
its plugin/wrapper, bundled gcc-ld/ld.lld and rust-lld, plus absence of an earlier
PATH cc. Previous selected-source linker records establish this lookup route;
these pins do not claim that Stage1 has run or prove the complete dynamic build-
tool runtime closure. No linker/global flag was changed.

The assigned Cargo argv now emits JSON artifacts and verbose rustc commands.
Post-success observation requires the selected manifest's actual lib and bin
artifacts with exact selected src paths, same package identity and fresh=false,
Cargo build-finished success, debug/0 build-script env/output fingerprint,
selected-source ash.d dependencies without the Borrow checkout, and exact Cargo
fingerprint JSON paths from emitted rustc extra-filename values. These actual
records are retained before byte observation; missing or unfamiliar format
refuses for review. Normal compatible dependency reuse is allowed; the selected
Ash lib/bin must actually compile. No mtime or manually assigned source_commit
label substitutes for these records. This is trusted normal Cargo producer
correspondence, not formal compiler correctness or permission to execute an
owner/native image. There must be no concurrent Cargo user of the shared cache
through the entire build/after-check/correspondence observation sequence.
