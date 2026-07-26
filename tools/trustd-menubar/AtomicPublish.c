// Atomically publish a fully staged directory on macOS.
//
// Every parent component is opened with O_NOFOLLOW, and renameatx_np operates
// relative to those held descriptors. RENAME_EXCL handles first publication;
// RENAME_SWAP keeps the prior destination continuously present and moves it to
// the staging leaf for verification rollback or cleanup.

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/stdio.h>
#include <unistd.h>

struct parent_path {
    int descriptor;
    char *storage;
    char *leaf;
};

static void close_parent(struct parent_path *parent) {
    if (parent->descriptor >= 0) {
        (void)close(parent->descriptor);
    }
    free(parent->storage);
    free(parent->leaf);
}

static int valid_absolute_path(const char *path) {
    size_t length = strlen(path);
    if (length < 2 || path[0] != '/' || path[length - 1] == '/' ||
        strstr(path, "//") != NULL || strstr(path, "/./") != NULL ||
        strstr(path, "/../") != NULL || strcmp(path + length - 2, "/.") == 0 ||
        (length >= 3 && strcmp(path + length - 3, "/..") == 0)) {
        fprintf(stderr, "publish path must be absolute and normalized: %s\n", path);
        return 0;
    }
    return 1;
}

static int open_parent_no_symlinks(const char *path, struct parent_path *result) {
    result->descriptor = -1;
    result->storage = NULL;
    result->leaf = NULL;
    if (!valid_absolute_path(path)) {
        return -1;
    }

    result->storage = strdup(path);
    if (result->storage == NULL) {
        perror("strdup");
        return -1;
    }
    char *last_slash = strrchr(result->storage, '/');
    int root_parent = last_slash == result->storage;
    result->leaf = strdup(last_slash + 1);
    if (result->leaf == NULL) {
        perror("strdup");
        return -1;
    }
    *last_slash = '\0';

    int directory = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (directory < 0) {
        perror("open root directory");
        return -1;
    }

    char *component = root_parent ? result->storage : result->storage + 1;
    while (*component != '\0') {
        char *separator = strchr(component, '/');
        if (separator != NULL) {
            *separator = '\0';
        }
        int next = openat(directory, component,
                          O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (next < 0) {
            fprintf(stderr, "cannot safely open parent component %s for %s: %s\n",
                    component, path, strerror(errno));
            (void)close(directory);
            return -1;
        }
        (void)close(directory);
        directory = next;
        if (separator == NULL) {
            break;
        }
        component = separator + 1;
    }
    result->descriptor = directory;
    return 0;
}

static int path_kind_at(const struct parent_path *parent, int permit_missing) {
    struct stat metadata;
    if (fstatat(parent->descriptor, parent->leaf, &metadata, AT_SYMLINK_NOFOLLOW) == 0) {
        if (S_ISLNK(metadata.st_mode)) {
            fprintf(stderr, "refusing symlink publish leaf: %s\n", parent->leaf);
            return -1;
        }
        if (!S_ISDIR(metadata.st_mode)) {
            fprintf(stderr, "publish leaf is not a directory: %s\n", parent->leaf);
            return -1;
        }
        if (metadata.st_uid != geteuid()) {
            fprintf(stderr, "publish leaf is not owned by the current uid: %s\n",
                    parent->leaf);
            return -1;
        }
        return 1;
    }
    if (errno == ENOENT && permit_missing) {
        return 0;
    }
    fprintf(stderr, "cannot inspect publish leaf %s: %s\n", parent->leaf,
            strerror(errno));
    return -1;
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s STAGED_DIRECTORY DESTINATION_DIRECTORY\n", argv[0]);
        return 64;
    }

    struct parent_path staged;
    struct parent_path destination;
    if (open_parent_no_symlinks(argv[1], &staged) != 0) {
        close_parent(&staged);
        return 65;
    }
    if (open_parent_no_symlinks(argv[2], &destination) != 0) {
        close_parent(&staged);
        close_parent(&destination);
        return 65;
    }

    struct stat staged_parent_metadata;
    struct stat destination_parent_metadata;
    if (fstat(staged.descriptor, &staged_parent_metadata) != 0 ||
        fstat(destination.descriptor, &destination_parent_metadata) != 0) {
        perror("fstat publish parent");
        close_parent(&staged);
        close_parent(&destination);
        return 65;
    }
    if (staged_parent_metadata.st_uid != geteuid() ||
        destination_parent_metadata.st_uid != geteuid() ||
        (staged_parent_metadata.st_mode & 0022) != 0 ||
        (destination_parent_metadata.st_mode & 0022) != 0) {
        fprintf(stderr,
                "publish parents must be current-user-owned and not group/world writable\n");
        close_parent(&staged);
        close_parent(&destination);
        return 65;
    }
    if (staged_parent_metadata.st_dev == destination_parent_metadata.st_dev &&
        staged_parent_metadata.st_ino == destination_parent_metadata.st_ino &&
        strcmp(staged.leaf, destination.leaf) == 0) {
        fprintf(stderr, "staged and destination paths identify the same leaf\n");
        close_parent(&staged);
        close_parent(&destination);
        return 64;
    }

    int result = 75;
    for (unsigned int attempt = 0; attempt < 32; ++attempt) {
        if (path_kind_at(&staged, 0) != 1) {
            result = 65;
            break;
        }

        int destination_kind = path_kind_at(&destination, 1);
        if (destination_kind < 0) {
            result = 65;
            break;
        }
        if (destination_kind == 0) {
            if (renameatx_np(staged.descriptor, staged.leaf, destination.descriptor,
                             destination.leaf, RENAME_EXCL) == 0) {
                puts("created");
                result = 0;
                break;
            }
            if (errno == EEXIST) {
                continue;
            }
            fprintf(stderr, "atomic exclusive publish failed: %s\n", strerror(errno));
            result = 74;
            break;
        }

        if (renameatx_np(staged.descriptor, staged.leaf, destination.descriptor,
                         destination.leaf, RENAME_SWAP) == 0) {
            puts("swapped");
            result = 0;
            break;
        }
        if (errno == ENOENT) {
            continue;
        }
        fprintf(stderr, "atomic directory swap failed: %s\n", strerror(errno));
        result = 74;
        break;
    }
    if (result == 75) {
        fprintf(stderr, "destination changed too often during atomic publication\n");
    }

    close_parent(&staged);
    close_parent(&destination);
    return result;
}
