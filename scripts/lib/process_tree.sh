#!/usr/bin/env bash
# Shared, read-only process-tree accounting for the build resource guards.
#
# Keep this helper signal-free.  Callers may use its snapshot to choose a
# process, but must revalidate ancestry immediately before sending a signal.
# `ps`'s pid/ppid/rss columns are available on both macOS and Linux; RSS is KB.

trust_process_snapshot() {
    ps -axo pid=,ppid=,rss=,comm= 2>/dev/null
}

trust_descendant_process_rows() {
    local root_pid="${1:?root PID is required}"
    if [[ ! "$root_pid" =~ ^[1-9][0-9]*$ ]]; then
        echo "invalid root PID: $root_pid" >&2
        return 2
    fi

    trust_process_snapshot | awk -v root="$root_pid" '
        function belongs_to_root(pid, current, parent_pid, hops) {
            current = pid
            for (hops = 0; hops <= process_count; hops++) {
                if (current == root) {
                    return 1
                }
                if (!(current in parents)) {
                    return 0
                }
                parent_pid = parents[current]
                if (parent_pid == "" || parent_pid == 0 || parent_pid == current) {
                    return 0
                }
                current = parent_pid
            }
            return 0
        }

        {
            pid = $1
            parents[pid] = $2
            rss[pid] = $3
            command[pid] = $4
            order[++process_count] = pid
        }

        END {
            for (row_index = 1; row_index <= process_count; row_index++) {
                pid = order[row_index]
                if (belongs_to_root(pid)) {
                    print pid, parents[pid], rss[pid], command[pid]
                }
            }
        }
    '
}

# Print "RSS_KB PROCESS_COUNT" for ROOT_PID and all of its live descendants.
trust_process_tree_rss_kb() {
    local root_pid="${1:?root PID is required}"
    local rows
    rows="$(trust_descendant_process_rows "$root_pid")" || return
    [[ -n "$rows" ]] || return 1

    awk '{ rss += $3; count += 1 } END { print rss + 0, count + 0 }' <<<"$rows"
}

# Print "PID RSS_MIB" for the heaviest matching member of ROOT_PID's tree.
trust_heaviest_matching_descendant() {
    local root_pid="${1:?root PID is required}"
    local command_regex="${2:?command regex is required}"

    trust_descendant_process_rows "$root_pid" | awk -v re="$command_regex" '
        $4 ~ re && (!found || $3 > largest_rss) {
            found = 1
            largest_pid = $1
            largest_rss = $3
        }
        END {
            if (found) {
                print largest_pid, int(largest_rss / 1024)
            }
        }
    '
}

trust_process_is_descendant() {
    local root_pid="${1:?root PID is required}"
    local candidate_pid="${2:?candidate PID is required}"
    if [[ ! "$candidate_pid" =~ ^[1-9][0-9]*$ ]]; then
        return 1
    fi

    trust_descendant_process_rows "$root_pid" |
        awk -v candidate="$candidate_pid" '$1 == candidate { found = 1 } END { exit !found }'
}
