#!/bin/sh
set -eu
cd /tmp/ash-checked-ffi-inprocess
/usr/bin/cc -O2 -fno-pie -MD -MF reporter-A.d -c reporter.c -o reporter-A.o
/usr/bin/cc -O2 -fno-pie '-DREPORT_ID="trusted-reporter-B"' -c reporter.c -o reporter-B.o
/usr/bin/cc -static -no-pie -Wl,--build-id=none -Wl,-Map,reporter-A.map -o reporter-A reporter-A.o
/usr/bin/cc -static -no-pie -Wl,--build-id=none -Wl,-Map,reporter-B.map -o reporter-B reporter-B.o
/usr/bin/readelf -h -l -d reporter-A > reporter-A.elf.txt
/usr/bin/readelf -h -l -d reporter-B > reporter-B.elf.txt
