/* Qualify the injector with actual OS calls before giving it to a CLI. */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc != 5) return 2;
    int created = open(argv[1], O_WRONLY | O_CREAT, 0600);
    if (created >= 0 || errno != ENOSPC) return 3;
    int existing = open(argv[2], O_RDWR);
    if (existing < 0) return 4;
    if (write(existing, "changed", 7) != -1 || errno != ENOSPC) return 5;
    if (close(existing) != 0) return 6;
    if (mkdir(argv[3], 0700) != -1 || errno != ENOSPC) return 7;
    if (unlink(argv[4]) != 0) return 8;
    puts("create/write/mkdir refused with ENOSPC; existing unlink succeeded");
    return 0;
}
