#!/usr/bin/env bash
# Probe the u64 -> u32 truncation in the uid_map line parser.
# Read-only experiment: creates throwaway user namespaces, writes a map
# into each, reads it back. Touches nothing outside the namespaces.
set -u

ME=$(id -u)

probe () {
    local label="$1" first="$2"
    local pidfile; pidfile=$(mktemp)

    unshare -U bash -c "echo \$\$ > $pidfile; sleep 30" &
    local job=$!
    sleep 0.5
    local nspid; nspid=$(cat "$pidfile")

    printf '%-28s written: %-26s ' "$label" "$first $ME 1"
    if printf '%s %s 1\n' "$first" "$ME" > "/proc/$nspid/uid_map" 2>/tmp/uiderr; then
        printf 'accepted -> %s\n' "$(tr -s ' ' < "/proc/$nspid/uid_map" | sed 's/^ //')"
    else
        printf 'REJECTED (%s)\n' "$(cat /tmp/uiderr | sed 's/.*: //')"
    fi

    kill "$job" 2>/dev/null; wait "$job" 2>/dev/null; rm -f "$pidfile"
}

echo "uid outside the namespace = $ME"
echo
probe "control, plain 0"            0
probe "2^32     (expect first=0)"   4294967296
probe "2^32 + 1 (expect first=1)"   4294967297
probe "2^32 + 5 (expect first=5)"   4294967301
probe "huge, saturating"            99999999999999999999999
probe "plain 5, for comparison"     5
rm -f /tmp/uiderr