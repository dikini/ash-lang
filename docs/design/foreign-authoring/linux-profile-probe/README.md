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

## Deployment prerequisite evidence

A further 2026-10-21 probe resolves the actual cgroup path and tests trusted
credential setup. It starts no foreign or static image, mutates no cgroup,
mounts no storage, changes no host policy, and claims no isolated execution.
The two invocations both return 78, refusing before worker startup:

```sh
cd docs/design/foreign-authoring/linux-profile-probe
/usr/bin/python3 deployment_preflight.py --label sandbox > /tmp/deployment-sandbox.json
# Run the following only through ordinary approved host execution:
/usr/bin/python3 deployment_preflight.py --label approved-host > /tmp/deployment-host.json
```

The label describes execution context; it grants no privilege or approval. The
[receipt](deployment-receipt.json) pins source, observations, commands and design
inputs. The receipt distinguishes the Main product base from governing preparation
commit `1cf1014fac94c3dfdaa86b825c276847e31ec629`, whose tree retains the
pre-amendment contract bytes. The [sandbox observation](deployment-sandbox.json) and
[approved-host observation](deployment-host.json) deliberately record different
inherited enforcement. Reproduction must record its own exit status and compare
these pins; new process counts and inherited state can differ.

The actual cgroup membership is an application scope below
`/user.slice/user-1000.slice/user@1000.service/app.slice`. On the host,
`user@1000.service` has user-owned migration and subtree-control files and enabled
`cpu memory pids` controllers. User-owned limit files below `app.slice` open for
writing without a write. In the command sandbox those same files fail with
EROFS. This refines Stage A's incomplete hierarchy-root observation: host
delegation exists, but neither opening files nor inherited limits establishes
per-worker assignment or actual enforcement. No limit was modified or tested.

The [trusted setup child](setup_probe.py) attempts, in order, a user namespace,
clearing supplementary groups, denying future setgroups, UID mapping, GID
mapping, clearing groups again, and a mount namespace. Each operation records
its own result. The host child creates both namespaces with namespace UID/GID
1000 mapped to host UID/GID 1000, without host-root mapping. Both group-clearing
attempts fail with EPERM. Ten supplementary groups remain after mapping: nine
appear as overflow GID 65534 and one as GID 1000. The sandbox child also fails
to establish empty groups and the attempted maps. Both children exit normally
and are reaped. This is trusted setup evidence, not worker self-attestation.

`newuidmap` and `newgidmap` are absent from the discovered PATH.
The user has subordinate UID/GID ranges, but those entries alone do not grant
mapping authority. The attempted unprivileged single-GID setup needs
`setgroups=deny` before its GID map and cannot clear inherited groups. The
[user namespace mapping rules](https://man7.org/linux/man-pages/man7/user_namespaces.7.html)
explain that restriction. A reviewed
deployment-supplied trusted credential launcher, potentially using a correctly
configured mapping helper that preserves setgroups authority, is an external
prerequisite. These failures do not prove every possible host deployment
impossible. No helper was installed and no privileges or host policy changed.

The preflight is disposable discovery tooling, not the production launcher or
a complete admission check. It always refuses and cannot authorize worker
startup. Stage B remains unexecuted. Required evidence still includes configured
post-exec/re-exec credentials, static-image approval and immutable execution,
private root and exclusive quota-backed storage, reviewed default-deny syscall
policy, actual limits, termination/reaping under faults, and real SQLite cases.
Root/storage access, capabilities in the namespace, and an available cgroup
hierarchy do not discharge those obligations. No F2 architecture is accepted.
