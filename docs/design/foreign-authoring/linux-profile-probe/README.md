# Linux profile Stage A evidence

This is bounded evidence for the
[experiment contract](../linux-profile-experiment.md), recorded on 2026-10-21.
It establishes no accepted architecture, product behavior or isolated deployment.

Reproduce from the repository root:

```sh
python3 docs/design/foreign-authoring/linux-profile-probe/probe.py
/usr/bin/python3 docs/design/foreign-authoring/linux-profile-probe/probe.py
```

The [first observation](observations.json) uses the environment's Conda Python.
It lacks `os.memfd_create`; the first draft probe exited on that missing API.
The retained probe records that unsupported API rather than hiding it. The
[system-Python observation](observations-system-python.json) can create/seal a
memfd and gets EPERM on attempted mutation after all four seals. Neither run
executes a memfd or establishes executable-memfd deployment policy.

Both runs create an unprivileged user namespace and observe `no_new_privs=1`,
nonzero UID/GID and zero capability sets across exec/re-exec of the trusted Python
interpreter. Initial supplementary groups remain present. This is inherited
session policy, not proof of a newly configured worker credential policy; the
required empty-group invariant is not established. No arbitrary worker is trusted
to attest enforcement.

The cgroup hierarchy root is visible, but the observed controller/migration files
are not writable, and the root has no memory/CPU/task limit files. The probe does
not resolve the actual delegated subgroup or prove delegation impossible elsewhere.
No cgroup, quota, root, syscall allowlist, static worker, process fault, timeout or
reaping enforcement test ran. Stage B needs an identified delegated controller and
storage configuration, plus a bounded launcher/test realization. Until those
controls are established, the isolated profile must be treated as unavailable.

JSON records pin interpreter/probe bytes and kernel observations. Reproduction
must compare these before transferring findings; outputs can change with inherited
sandbox policy. [Design input pins](design-input-pins.json) bind the proposal's
canonical design snapshot. Probe observations apply only to the recorded controls,
not SQLite correctness, the source contract, target ABI or native executable bytes.
