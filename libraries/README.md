# Source bindings

This directory currently ships no source binding modules. The former Arena,
native-buffer and SQLite libraries depended on the retired foreign policy API
and have been removed during the accepted
[slim FFI transition](../docs/proposals/CP-0024-checked-foreign-host-profile.md).

The current [native declarations](../tests/fixtures/source-native/native.ash),
[C fixture](../tests/fixtures/source-native/native_counter.c) and
[pointer client](../tests/fixtures/source-native/cases/pointers.ash) exercise the
Address/Bytes/void boundary through the existing
[program-build tests](../tests/program_build_native.rs). Static and shared native
inputs use the build machinery recorded in
[AD-0013](../docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md).

The ordinary binding example and direct SQLite getter canary remain the next
[delivery stage](https://github.com/dikini/ash-lang/issues/133); they are not
shipped library APIs at this checkpoint.
