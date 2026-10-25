#include <stdio.h>
#include <unistd.h>

#ifndef REPORT_ID
#define REPORT_ID "trusted-reporter-A"
#endif
int main(void) {
    gid_t groups[32];
    int count = getgroups(32, groups);
    if (count < 0) return 3;
    printf("%s uid=%lu gid=%lu groups=", REPORT_ID,
           (unsigned long)getuid(), (unsigned long)getgid());
    for (int i = 0; i < count; ++i)
        printf("%s%lu", i ? "," : "", (unsigned long)groups[i]);
    printf("\n");
    return fflush(stdout) == 0 ? 0 : 4;
}
