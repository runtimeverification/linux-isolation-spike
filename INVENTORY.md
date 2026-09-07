# Phase 0 — Linux kernel isolation surface inventory

**Reference tree:** `~/linux-full`, read-only.
Version: `v7.2-rc7-687-ge172eee25cfe` (`Makefile` VERSION=7 PATCHLEVEL=2).
Every line reference below was read out of that tree; nothing here is from
recollection. Line numbers are for that exact commit.

Reading order: each section gives (a) the enforcement points with line
references, (b) the security property the code is responsible for, and (c) a
plain-language note on why a container/VM sandbox depends on it.

A convention used throughout: **"the isolation decision"** means the single
point where the kernel converts an untrusted-caller request into an
allow/deny or into a translated identity. Those points are what a
verification effort should target; the surrounding plumbing is not.

---

## 1. Namespaces

### 1.1 The nsproxy container and `setns`

| Symbol | File | Lines |
|---|---|---|
| `create_nsproxy` | `kernel/nsproxy.c` | 54 |
| `create_new_namespaces` | `kernel/nsproxy.c` | 88 |
| `copy_namespaces` (clone path) | `kernel/nsproxy.c` | 169 |
| `unshare_nsproxy_namespaces` | `kernel/nsproxy.c` | 211 |
| `switch_task_namespaces` | `kernel/nsproxy.c` | 245 |
| `check_setns_flags` | `kernel/nsproxy.c` | 301 |
| `prepare_nsset` | `kernel/nsproxy.c` | 354 |
| `validate_ns` / `validate_nsset` | `kernel/nsproxy.c` | 386 / 398 |
| `commit_nsset` | `kernel/nsproxy.c` | 535 |
| `SYSCALL_DEFINE2(setns)` | `kernel/nsproxy.c` | 569 |

**Security property.** `struct nsproxy` is the per-task table of namespace
pointers; every namespace-relative lookup in the kernel starts from
`current->nsproxy`. The property this file is responsible for is *atomic,
all-or-nothing namespace transition with pre-validated permission*:
`validate_nsset` (398) calls each namespace's `->install` handler (via
`validate_ns`, 386) for every requested namespace **before** any pointer is
swapped, and only `commit_nsset` (535) — the "point of no return" the comment
at 391–397 names — publishes the new set. A task must therefore never observe
a half-entered set (e.g. the new mount namespace with the old user namespace,
which would be a privilege combination no `->install` handler ever approved).
Two supporting properties: `validate_nsset` requires
`ptrace_may_access(tsk, PTRACE_MODE_READ_REALCREDS)` on the target task (415)
so `setns(pidfd)` cannot be used to enumerate namespaces of processes the
caller cannot already inspect; and `check_setns_flags` (301) rejects any bit
outside `CLONE_NS_ALL`, keeping the flag word from aliasing into unrelated
`CLONE_*` semantics.

**Why sandboxes depend on this.** Every sandbox is, at the kernel level, a
task whose `nsproxy` points at namespaces the host set up. If the transition
into that set could be made partial — or if a process inside could re-enter a
namespace it should not reach — the sandbox boundary is simply the wrong set
of pointers, and nothing downstream can recover.

### 1.2 User namespaces (the root of the other namespaces' trust)

| Symbol | File | Lines |
|---|---|---|
| `set_cred_user_ns` | `kernel/user_namespace.c` | 44 |
| `create_user_ns` | `kernel/user_namespace.c` | 83 |
| `unshare_userns` | `kernel/user_namespace.c` | 177 |
| `cmp_map_id` (bsearch predicate) | `kernel/user_namespace.c` | 251 |
| `map_id_range_down_max` / `_base` | `kernel/user_namespace.c` | 282 / 300 |
| `map_id_range_down` | `kernel/user_namespace.c` | 318 |
| `map_id_down` | `kernel/user_namespace.c` | 338 |
| `map_id_range_up_base` / `_max` | `kernel/user_namespace.c` | 349 / 372 |
| `map_id_range_up` | `kernel/user_namespace.c` | 384 |
| `map_id_up` | `kernel/user_namespace.c` | 404 |
| `make_kuid` / `from_kuid` / `from_kuid_munged` | `kernel/user_namespace.c` | 422 / 441 / 466 |
| `make_kgid` / `from_kgid` / `from_kgid_munged` | `kernel/user_namespace.c` | 490 / 509 / 533 |
| `make_kprojid` / `from_kprojid` / `_munged` | `kernel/user_namespace.c` | 557 / 576 / 601 |
| `mappings_overlap` | `kernel/user_namespace.c` | 745 |
| `insert_extent` | `kernel/user_namespace.c` | 789 |
| `cmp_extents_forward` / `_reverse` | `kernel/user_namespace.c` | 823 / 838 |
| `sort_idmaps` | `kernel/user_namespace.c` | 856 |
| `verify_root_map` | `kernel/user_namespace.c` | 890 |
| `map_write` | `kernel/user_namespace.c` | 932 |
| `proc_{uid,gid,projid}_map_write` | `kernel/user_namespace.c` | 1120 / 1137 / 1154 |
| `new_idmap_permitted` | `kernel/user_namespace.c` | 1172 |
| `proc_setgroups_write` / `userns_may_setgroups` | `kernel/user_namespace.c` | 1225 / 1292 |
| `in_userns` / `current_in_userns` | `kernel/user_namespace.c` | 1312 / 1321 |
| `userns_install` | `kernel/user_namespace.c` | 1343 |
| `ns_get_owner` | `kernel/user_namespace.c` | 1377 |
| `struct uid_gid_extent` | `include/linux/user_namespace.h` | 19–23 |
| `struct uid_gid_map` (a **union**) | `include/linux/user_namespace.h` | 25–35 |
| `UID_GID_MAP_MAX_BASE_EXTENTS` = 5, `UID_GID_MAP_MAX_EXTENTS` = 340 | `include/linux/user_namespace.h` | 16–17 |
| `struct user_namespace` | `include/linux/user_namespace.h` | 78– |
| `bsearch` / `__inline_bsearch` | `lib/bsearch.c` 31, `include/linux/bsearch.h` 9–28 | |
| `sort` (heapsort, used by `sort_idmaps`) | `lib/sort.c` | 1–357 |

**Security property.** The user namespace is the *authority* for every other
namespace: `pidns_install` (392), `utsns_install` (127 in `kernel/utsname.c`),
`ipcns_install` (233 in `ipc/namespace.c`), `netns_install` (1529 in
`net/core/net_namespace.c`) and `mntns_install` (6490 in `fs/namespace.c`) all
gate on `ns_capable(<ns>->user_ns, CAP_SYS_ADMIN)`. Within a user namespace,
the security-relevant object is the pair of ID maps, and the properties are:

1. **Total, injective, order-consistent translation.** `uid_map`/`gid_map`/
   `projid_map` are arrays of `(first, lower_first, count)` extents. Downward
   translation (`map_id_range_down`, 318) maps a namespace-local ID to the
   kernel-global ID; upward (`map_id_range_up`, 384) inverts it. Both must be
   *functions* (each input has at most one image) and mutual inverses on their
   domains, or a task's identity is not well-defined. Failure is signalled
   out-of-band by the sentinel `(u32)-1` (333, 399) — never by an unrelated
   ID.
2. **Two lookup implementations must agree.** For `nr_extents <= 5` the code
   linearly scans the inline `extent[]` array (300, 349); above 5 it binary
   searches heap copies `forward`/`reverse` sorted by `first` and by
   `lower_first` respectively (282, 372, via `bsearch`/`cmp_map_id`). The
   binary search is only correct if the arrays are sorted *and* the extents
   are pairwise non-overlapping in both coordinates — otherwise `cmp_map_id`'s
   three-way comparison is not a valid search predicate and lookups silently
   return the wrong extent or `NULL`.
3. **The write path establishes exactly those preconditions, once.**
   `map_write` (932) is the only writer. It enforces: one successful write per
   map ever (`map->nr_extents != 0` -> `-EPERM`, 980); `CAP_SYS_ADMIN` over the
   target ns held by the *opener* of the file (`file_ns_capable`, 986);
   `first != (u32)-1 && lower_first != (u32)-1` (1024); no range wrap
   (`extent.first + extent.count <= extent.first` -> reject, 1031, and the same
   for `lower_first`, 1033); pairwise non-overlap against everything inserted
   so far (`mappings_overlap`, 1038); the 340-extent cap (1041); that every
   `lower_first` is itself mappable in the parent map (1072, via
   `map_id_range_down`); and the policy checks in `new_idmap_permitted` (1172)
   plus `verify_root_map` (890). Only then does `sort_idmaps` (856) build the
   sorted arrays and the `smp_wmb()` + `nr_extents` store (1101–1102) publish
   them.
4. **Publication ordering.** Readers load `nr_extents` then `smp_rmb()` (322,
   388); the writer stores extents, `smp_wmb()`, then `nr_extents`. The
   invariant is that a non-zero `nr_extents` implies fully-initialized extent
   storage — which is also what lets `struct uid_gid_map`'s union be sound:
   `nr_extents` sits at offset 60, past the 16 bytes that `forward`/`reverse`
   alias, so the count is readable in both union arms while `insert_extent`
   (789) is allowed to clobber `extent[0..1]` when it migrates to the heap.
5. **Policy, not just arithmetic.** `verify_root_map` (890) refuses a map that
   claims parent UID 0 unless the writer held `CAP_SETFCAP`, because owning
   parent-0 inside the namespace lets the task write file capabilities that are
   valid in ancestor namespaces. `new_idmap_permitted` (1172) is what allows
   the unprivileged single-ID self-map that `unshare -Ur` relies on, and
   nothing wider.

**Why sandboxes depend on this.** "Root in the container, nobody on the host"
is exactly this table. Every file-ownership check, every `chown`, every
`CAP_*` decision, and every fscap the sandboxed process can write is resolved
through `make_kuid`/`from_kuid`. If two distinct in-container UIDs could map to
one host UID, or a container UID could map outside its granted extents, the
sandboxed process gains the host identity of another user — the whole point of
the boundary, undone by an arithmetic slip. This same `struct uid_gid_map` code
is also the engine of **idmapped mounts** (§7.3), so a defect here is not
confined to user namespaces.

### 1.3 PID namespaces

| Symbol | File | Lines |
|---|---|---|
| `create_pid_namespace` | `kernel/pid_namespace.c` | 76 |
| `MAX_PID_NS_LEVEL` = 32 | `include/linux/pid_namespace.h` | 15 |
| level cap enforcement | `kernel/pid_namespace.c` | 89 |
| `in_userns` precondition | `kernel/pid_namespace.c` | 85 |
| `copy_pid_ns` | `kernel/pid_namespace.c` | 175 |
| `zap_pid_ns_processes` | `kernel/pid_namespace.c` | 192 |
| `reboot_pid_ns` | `kernel/pid_namespace.c` | 319 |
| `pidns_is_ancestor` | `kernel/pid_namespace.c` | 380 |
| `pidns_install` | `kernel/pid_namespace.c` | 392 |
| `pidns_get_parent` | `kernel/pid_namespace.c` | 418 |

**Security property.** A process may not escape its PID namespace subtree.
`pidns_install` (392) enforces `ns_capable(new->user_ns, CAP_SYS_ADMIN)` *and*
`ns_capable(nsset->cred->user_ns, CAP_SYS_ADMIN)`, then — the escape-relevant
check — `pidns_is_ancestor(new, active)` (410), so `setns` can only move
*into* the active namespace or a descendant, never sideways or up. The comment
at 402–409 states the property: "processes and their children can not escape
their current pid namespace". `create_pid_namespace` additionally requires the
new namespace's user_ns to be inside the parent pid namespace's user_ns
(`in_userns`, 85) and caps nesting at 32 levels (89), which bounds `struct pid`
size and therefore the allocation the nesting can drive.

**Why sandboxes depend on this.** PID isolation is what makes `kill`, `/proc`
enumeration and signal delivery stop at the sandbox edge. The ancestor check
is why a nested sandbox cannot signal or inspect its supervisor.

### 1.4 UTS and IPC namespaces

| Symbol | File | Lines |
|---|---|---|
| `clone_uts_ns` | `kernel/utsname.c` | 36 |
| `copy_utsname` | `kernel/utsname.c` | 79 |
| `utsns_install` | `kernel/utsname.c` | 127 |
| `create_ipc_ns` | `ipc/namespace.c` | 39 |
| `copy_ipcs` | `ipc/namespace.c` | 111 |
| `ipcns_install` | `ipc/namespace.c` | 233 |

**Security property.** Both are *copy-on-unshare with a ucount budget*.
`copy_utsname` (79) returns the existing namespace unless `CLONE_NEWUTS` is
set, otherwise clones; `create_ipc_ns` (39) charges `inc_ipc_namespaces`
before allocating and unwinds on failure. `utsns_install` (127) requires
`CAP_SYS_ADMIN` in **both** the target namespace's user_ns and the caller's
own user_ns — the two-sided check that prevents a task from entering a
namespace owned by a user_ns it has no authority in. The IPC namespace also
carries the SysV/POSIX-mq object namespace and its own sysctl set
(`setup_ipc_sysctls`, `setup_mq_sysctls`), so its property includes "no SysV
key or mqueue name collides across namespaces".

**Why sandboxes depend on this.** UTS isolation is cosmetic-looking but is
what keeps a sandbox from rewriting the host's hostname; IPC isolation stops
shared-memory and message-queue channels between sandboxes, which are
otherwise a first-class escape path since SysV keys are global integers.

### 1.5 Network namespaces

| Symbol | File | Lines |
|---|---|---|
| `setup_net` | `net/core/net_namespace.c` | 436 |
| `copy_net_ns` | `net/core/net_namespace.c` | 549 |
| `netns_install` | `net/core/net_namespace.c` | 1529 |
| `netns_owner` | `net/core/net_namespace.c` | 1544 |

**Security property.** A net namespace is a complete, independent network
stack instance (device list, routing tables, netfilter state, socket tables,
per-namespace sysctls). `setup_net` (436) runs every registered
`pernet_operations` `->init` in order and unwinds in reverse on failure — the
property being that a namespace is either fully constructed or not published
at all, since a partially initialized namespace would leave subsystem state
pointing at the initial namespace. `netns_install` (1529) again requires
`CAP_SYS_ADMIN` in both the target's user_ns and the caller's.

**Why sandboxes depend on this.** Net namespaces are how a sandbox gets "no
network" or "only this veth" — and, less obviously, why a sandboxed process
holding `CAP_NET_ADMIN` (which it plausibly does inside its own user
namespace) cannot reconfigure the host's firewall: the capability is scoped to
a namespace whose user_ns it owns.

---

## 2. Capabilities

| Symbol | File | Lines |
|---|---|---|
| `cap_validate_magic` | `kernel/capability.c` | 71 |
| `SYSCALL_DEFINE2(capget)` | `kernel/capability.c` | 137 |
| `mk_kernel_cap` | `kernel/capability.c` | 193 |
| `SYSCALL_DEFINE2(capset)` | `kernel/capability.c` | 216 |
| `has_ns_capability` / `_noaudit` | `kernel/capability.c` | 276 / 301 |
| `ns_capable_common` | `kernel/capability.c` | 331 |
| `ns_capable` / `_noaudit` / `_setid` | `kernel/capability.c` | 361 / 379 / 398 |
| `capable` | `kernel/capability.c` | 414 |
| `file_ns_capable` | `kernel/capability.c` | 433 |
| `privileged_wrt_inode_uidgid` | `kernel/capability.c` | 455 |
| `capable_wrt_inode_uidgid` | `kernel/capability.c` | 473 |
| `ptracer_capable` | `kernel/capability.c` | 491 |
| `cap_capable_helper` | `security/commoncap.c` | 68 |
| `cap_capable` | `security/commoncap.c` | 124 |
| `cap_ptrace_access_check` / `_traceme` | `security/commoncap.c` | 164 / 201 |
| `cap_capget` | `security/commoncap.c` | 230 |
| `cap_inh_is_capped` | `security/commoncap.c` | 249 |
| `cap_capset` | `security/commoncap.c` | 272 |
| `is_v2header` / `is_v3header` | `security/commoncap.c` | 395 / 402 |
| `cap_inode_getsecurity` | `security/commoncap.c` | 420 |
| `rootid_from_xattr` | `security/commoncap.c` | 533 |
| `validheader` | `security/commoncap.c` | 545 |
| `cap_convert_nscap` | `security/commoncap.c` | 569 |
| `bprm_caps_from_vfs_caps` | `security/commoncap.c` | 626 |
| `get_vfs_caps_from_disk` | `security/commoncap.c` | 675 |
| `get_file_caps` | `security/commoncap.c` | 763 |
| `handle_privileged_root` | `security/commoncap.c` | 828 |
| `nonroot_raised_pE` | `security/commoncap.c` | 886 |
| `cap_bprm_creds_from_file` | `security/commoncap.c` | 919 |
| `cap_inode_setxattr` / `_removexattr` | `security/commoncap.c` | 1025 / 1066 |
| `cap_emulate_setxuid` | `security/commoncap.c` | 1120 |
| `cap_task_fix_setuid` | `security/commoncap.c` | 1159 |
| `cap_task_prctl` | `security/commoncap.c` | 1301 |
| `cap_mmap_addr` | `security/commoncap.c` | 1469 |
| `struct cred` (the five cap sets) | `include/linux/cred.h` | 115–151 |
| `cap_ambient_invariant_ok` | `include/linux/cred.h` | 174 |

**Security property.** Three distinct properties live here.

*(a) Capabilities are namespace-scoped, and authority flows only downward.*
`cap_capable_helper` (68) walks from the *target* namespace toward the root:
it grants if the target namespace equals the credential's own namespace and
the bit is in `cap_effective` (82); it grants unconditionally if the target's
parent is the credential's namespace and the credential's euid owns the target
(95); and it *denies* as soon as `ns->level <= cred_ns->level` (88) — the
check that makes the walk terminate and, more importantly, makes holding a
capability in a child namespace confer nothing in a parent. The property is:
"a capability held in namespace N applies in N and all descendants of N, and
nowhere else." Note the loop's termination is an invariant of the namespace
tree (strictly increasing `level` along `->parent`), not a syntactic bound.

*(b) The five-set transition rules are monotone.* `cap_capset` (272) is the
`capset(2)` gate: new pI must be a subset of old pI ∪ pP unless `CAP_SETPCAP`
is held (`cap_inh_is_capped`, 249); new pI must stay within old pI ∪ bounding
set; new pP ⊆ old pP; new pE ⊆ new pP; and ambient is intersected down to
pP ∩ pI (322). The bounding set is one-way (`cap_prctl_drop`, 1270). The
invariant `cap_ambient_invariant_ok` (`include/linux/cred.h` 174) —
ambient ⊆ pP ∩ pI — is asserted, not assumed. `cap_task_fix_setuid` (1159)
and `cap_emulate_setxuid` (1120) handle the legacy root-transition rules; the
property is that no sequence of `capset`/`setuid`/`prctl` can *add* a
capability that was not already reachable.

*(c) File capabilities cannot cross a namespace boundary they were not
written for.* `get_vfs_caps_from_disk` (675) reads the `security.capability`
xattr, computes the rootid (`make_kuid(fs_ns, 0)` for v1/v2, or
`make_kuid(fs_ns, nscaps->rootid)` for v3, 721), maps it through the mount's
idmap (`make_vfsuid`, 728) and returns `-ENODATA` unless the result is valid
and roots in the current namespace (`vfsuid_root_in_currentns`, 735). The
write side, `cap_convert_nscap` (569), requires `CAP_SETFCAP` with respect to
the inode's ids (`capable_wrt_inode_uidgid`, 587) and rewrites v2 -> v3 with a
rootid obtained by composing `make_kuid` (in `rootid_from_xattr`, 533),
`from_vfsuid` and `from_kuid` (594–602), rejecting each unmappable step. The
read-back path `cap_inode_getsecurity` (420) performs the inverse composition
(460–467). **These three functions are pure consumers of §1.2's ID
mapping** — their correctness is conditional on it.

**Why sandboxes depend on this.** Sandboxes hand the workload a user namespace
in which it is "root" precisely so that its capabilities are inert on the
host. `cap_capable_helper`'s level check is the line of code that makes that
true. And file capabilities are the classic bypass: a sandboxed process that
could write an fscap whose rootid maps to host UID 0 would have planted a
setuid-equivalent binary reachable from outside — which is why
`verify_root_map` (§1.2) and `cap_convert_nscap` are joined at the hip.

---

## 3. seccomp

| Symbol | File | Lines |
|---|---|---|
| `seccomp_check_filter` (opcode allowlist) | `kernel/seccomp.c` | 278 |
| `seccomp_cache_check_allow_bitmap` | `kernel/seccomp.c` | 349 |
| `seccomp_run_filters` | `kernel/seccomp.c` | 404 |
| `ACTION_ONLY` | `kernel/seccomp.c` | 394 |
| `seccomp_may_assign_mode` | `kernel/seccomp.c` | 435 |
| `seccomp_assign_mode` | `kernel/seccomp.c` | 447 |
| `is_ancestor` | `kernel/seccomp.c` | 467 |
| `seccomp_can_sync_threads` | `kernel/seccomp.c` | 488 |
| `seccomp_sync_threads` | `kernel/seccomp.c` | 598 |
| `seccomp_prepare_filter` | `kernel/seccomp.c` | 669 |
| `seccomp_prepare_user_filter` | `kernel/seccomp.c` | 722 |
| `seccomp_uprobe_exception` | `kernel/seccomp.c` | 744 |
| `seccomp_is_const_allow` | `kernel/seccomp.c` | 770 |
| `seccomp_cache_prepare_bitmap` | `kernel/seccomp.c` | 847 |
| `seccomp_attach_filter` | `kernel/seccomp.c` | 921 |
| `__secure_computing` | `kernel/seccomp.c` | 1103 / 1388 |
| `__seccomp_filter` | `kernel/seccomp.c` | 1259 |
| `init_listener` | `kernel/seccomp.c` | 1891 |
| `has_duplicate_listener` | `kernel/seccomp.c` | 1926 |
| `seccomp_set_mode_filter` | `kernel/seccomp.c` | 1956 |
| `do_seccomp` / `SYSCALL_DEFINE3(seccomp)` | `kernel/seccomp.c` | 2101 / 2126 |
| `check_load_and_stores` | `net/core/filter.c` | 931 |
| `bpf_check_classic` | `net/core/filter.c` | 1075 |
| `bpf_prog_create_from_user` | `net/core/filter.c` | 1426 |
| `___bpf_prog_run` (interpreter) | `kernel/bpf/core.c` | 1852 |
| `__bpf_prog_select_runtime` (JIT/interp choice) | `kernel/bpf/core.c` | 2667 |

**Security property.** Four layers, each with its own obligation.

*(a) Only memory-safe classic-BPF reaches the interpreter.*
`seccomp_check_filter` (278) is an *allowlist* over `sock_filter` opcodes. It
rewrites `BPF_LD|BPF_W|BPF_ABS` into `BPF_LDX|BPF_W|BPF_ABS` and requires
`k < sizeof(struct seccomp_data) && !(k & 3)` (290) — i.e. every absolute load
is 4-byte aligned and inside the 64-byte `seccomp_data`; it pins the two
`BPF_LEN` forms to that constant size (295, 300); and it rejects everything
not explicitly listed (`default: return -EINVAL`, 342). It is passed as the
per-program hook to `bpf_prog_create_from_user` (1426 in `net/core/filter.c`),
which runs it *alongside* the generic `bpf_check_classic` (1075). The generic
pass supplies what the seccomp pass does not: division-by-constant-zero
rejection (1094), shift counts `< 32` (1099), scratch-memory indices
`< BPF_MEMWORDS` (1107), and — the property the interpreter's termination
rests on — jump-target containment: `BPF_JA` requires
`k < (unsigned)(flen - pc - 1)` (1115) and conditional jumps require
`pc + jt + 1 < flen` and `pc + jf + 1 < flen` (1127). The last instruction
must be a `RET` (1144). So the composite property is: *an accepted program
only reads inside `seccomp_data`, only jumps forward to an existing
instruction, and always terminates in a `RET`.*

*(b) Lowest action wins, and the evaluation is total.* `seccomp_run_filters`
(404) walks the whole filter list, taking the numerically lowest
`ACTION_ONLY(ret)` (426), so a later (more recently added) filter can only
ever make the decision *stricter*. It fails closed: a `NULL` filter list
returns `SECCOMP_RET_KILL_PROCESS` (414), not allow.

*(c) The allow-bitmap cache must be a conservative under-approximation.*
`seccomp_is_const_allow` (770) is a small abstract interpreter over the same
opcode subset, evaluating the filter with only `sd->nr` and `sd->arch` known
(793, 796) and bailing out (`return false`) on any instruction whose result is
not constant. If and only if it reaches a `BPF_RET|BPF_K` equal to
`SECCOMP_RET_ALLOW` (805) does the syscall go into the per-arch bitmap
(`seccomp_cache_prepare_bitmap`, 847), after which `seccomp_run_filters` skips
filter evaluation entirely (417). **The property is a simulation: whenever
`seccomp_is_const_allow` returns true, the real interpreter must return
`SECCOMP_RET_ALLOW` for every `seccomp_data` agreeing on `nr` and `arch`.** A
false positive is a permanent, silent seccomp bypass for that syscall number.
Note it also depends on layer (a): `pc += insn->k` (807) and
`pc += op_res ? jt : jf` (831) are unguarded here, and are safe only because
`bpf_check_classic` already bounded them.

*(d) Filters are irrevocable and cannot be used to attack a more-privileged
child.* `seccomp_prepare_filter` (669) requires `no_new_privs` or
`CAP_SYS_ADMIN` in the caller's user namespace (691) — the comment at 685–689
states the reason. `seccomp_may_assign_mode` (435) forbids switching between
strict and filter mode. `is_ancestor` (467) and `seccomp_can_sync_threads`
(488) enforce that `TSYNC` may only *tighten* other threads (a thread's
existing filter must be an ancestor of the new one), and 648–649 propagate
`no_new_privs` to the synced threads.

**Why sandboxes depend on this.** seccomp is the only mechanism that reduces
the *syscall* attack surface rather than the resources a syscall can reach —
it is what keeps a sandboxed agent away from the ~400 syscalls nobody audited.
Two consequences of the above matter operationally: filters can only ever be
narrowed, so a sandbox can safely apply a filter and then run untrusted code;
and the bitmap cache means a sandbox's "allow" decisions are partly served
from a precomputed table, so the correctness of that precomputation is on the
critical path even though it is invisible at runtime.

---

## 4. cgroup v2: limits and delegation

| Symbol | File | Lines |
|---|---|---|
| `CGRP_ROOT_NS_DELEGATE` parse / apply | `kernel/cgroup/cgroup.c` | 2013, 2044–2047, 2076 |
| `cgroup_setup_root` | `kernel/cgroup/cgroup.c` | 2148 |
| `CGRP_ROOT_NS_DELEGATE` check in `cgroup_file_write` | `kernel/cgroup/cgroup.c` | 4313 (fn), 4331 (check) |
| `cgroup_max_descendants_write` | `kernel/cgroup/cgroup.c` | 3741 |
| `cgroup_max_depth_write` | `kernel/cgroup/cgroup.c` | 3784 |
| `cgroup_may_write` | `kernel/cgroup/cgroup.c` | 5335 |
| `cgroup_procs_write_permission` | `kernel/cgroup/cgroup.c` | 5351 |
| `cgroup_attach_permissions` | `kernel/cgroup/cgroup.c` | 5382 |
| `__cgroup_procs_write` | `kernel/cgroup/cgroup.c` | 5403 |
| `cgroup_css_set_fork` (CLONE_INTO_CGROUP) | `kernel/cgroup/cgroup.c` | 6785, 6836, 6854 |
| `free_cgroup_ns` / `copy_cgroup_ns` / `cgroupns_install` | `kernel/cgroup/namespace.c` | 36 / 48 / 92 |
| `pids_charge` / `pids_try_charge` / `pids_can_fork` | `kernel/cgroup/pids.c` | 145 / 166 / 273 |
| `misc` controller | `kernel/cgroup/misc.c` | whole file (478 lines) |

**Security property.** Two properties, and they are different in kind.

*Delegation.* The interesting one. `cgroup_procs_write_permission` (5351)
implements the "common ancestor" rule: it walks up from the source cgroup
until it finds an ancestor of the destination
(`while (!cgroup_is_descendant(dst_cgrp, com_cgrp)) com_cgrp = cgroup_parent(...)`,
5362), and requires the caller to have write permission on *that* cgroup's
`cgroup.procs` file (`cgroup_may_write`, 5366 -> `inode_permission`, 5346). The
property: **a delegatee can move processes freely within its own subtree but
cannot move a process into or out of the subtree without permission at the
boundary.** When `CGRP_ROOT_NS_DELEGATE` is set, both source and destination
must additionally be visible from the caller's cgroup namespace (5374–5377),
making the namespace a hard delegation boundary. `cgroup_attach_permissions`
(5382) adds the domain/threaded-mode check (5397). `cgroup_css_set_fork`
(6785) applies the same checks to `CLONE_INTO_CGROUP` (6836, 6854) — the point
being that the fork-time path must not be weaker than the write-time path.

*Resource containment.* `cgroup.max.descendants` (3741) and
`cgroup.max.depth` (3784) bound the tree a delegatee can build;
`pids_try_charge` (166) hierarchically reserves against every ancestor's limit
and `pids_can_fork` (273) refuses the fork if any ancestor is over — the
property being that a charge is either accepted at *every* level or fully
rolled back, so a descendant can never consume beyond an ancestor's cap.

**Why sandboxes depend on this.** cgroups are the only thing between a
sandboxed workload and a host-wide denial of service (fork bomb, memory
exhaustion, IO starvation). The delegation rules are what let a sandbox
supervisor hand a subtree to untrusted code and still be able to kill it: the
supervisor keeps write permission at the boundary, the workload cannot escape
the subtree, and `pids`/`memory` limits are enforced against every ancestor
regardless of what the workload does inside.

---

## 5. LSM hook dispatch and stacking

| Symbol | File | Lines |
|---|---|---|
| `lsm_active_cnt` | `security/security.c` | 79 |
| `LSM_HOOK` expansion: default-return table | `security/security.c` | 122–125 |
| `struct lsm_static_calls_table` | `security/security.c` | 139 |
| `LSM_HOOK` expansion: static-call slots | `security/security.c` | 147–152 |
| `LSM_RET_DEFAULT` definitions | `security/security.c` | 451–455 |
| `__CALL_STATIC_VOID` | `security/security.c` | 466 |
| `call_void_hook` | `security/security.c` | 473 |
| `__CALL_STATIC_INT` | `security/security.c` | 479 |
| `call_int_hook` | `security/security.c` | 488 |
| `lsm_for_each_hook` | `security/security.c` | 498 |
| `security_ptrace_access_check` | `security/security.c` | 578 |
| `security_capable` | `security/security.c` | 655 |
| `security_vm_enough_memory_mm` (manual loop) | `security/security.c` | 747 |
| `security_bprm_creds_from_file` | `security/security.c` | 803 |

**Security property.** The dispatcher must be *restrictive-only under
stacking*. `call_int_hook` (488) expands, via `LSM_LOOP_UNROLL`, into a fixed
sequence of `__CALL_STATIC_INT` (479) blocks. Each block is guarded by a
static branch (so an inactive LSM costs nothing), calls the module's hook, and
**short-circuits to the `OUT` label the moment the result differs from
`LSM_RET_DEFAULT(HOOK)`** (483–484). `RC` is initialized to the hook's default
(490). Two consequences: (i) the first module to return a non-default value
decides, so with the conventional convention that the default is the
permissive value (`0` for most access hooks) and any denial is non-default, a
denial by *any* stacked module is final — stacking can only remove
permissions, never add them; (ii) if no module is active, the result is the
compiled-in default from the `LSM_HOOK` table (122–125), so an unconfigured
kernel behaves as the hook's declared default rather than reading
uninitialized state. `call_void_hook` (473) has no short-circuit: every active
module runs, which is correct for notification hooks. A handful of hooks need
non-short-circuit accumulation and are written as explicit
`lsm_for_each_hook` (498) loops instead — `security_vm_enough_memory_mm` (747)
is the example. `capability` is registered as an LSM itself
(`DEFINE_LSM(capability)`, `security/commoncap.c` 1517), so §2's checks reach
the sandbox through this same dispatcher via `security_capable` (655).

**Why sandboxes depend on this.** SELinux/AppArmor confinement of a container
runtime is applied through these hooks, and hardening stacks (e.g. Landlock
plus AppArmor plus the capability module) rely on the "first denial wins"
property. It also bounds what a sandbox designer can assume: an LSM can only
*deny* what the base kernel would have allowed, so LSM policy cannot be used
to grant a sandbox something the DAC/capability layer refused.

---

## 6. Mount isolation

### 6.1 Mount namespace membership and locked mounts

| Symbol | File | Lines |
|---|---|---|
| `check_mnt` | `fs/namespace.c` | 947 |
| `check_anonymous_mnt` | `fs/namespace.c` | 952 |
| `clone_mnt` | `fs/namespace.c` | 1245 |
| `may_umount_tree` | `fs/namespace.c` | 1597 |
| `disconnect_mount` (honours `IS_MNT_LOCKED`) | `fs/namespace.c` | 1743, 1765 |
| `umount_tree` | `fs/namespace.c` | 1776 |
| `do_umount` `MNT_LOCKED` check | `fs/namespace.c` | 1943–1946 |
| `can_umount` | `fs/namespace.c` | 2021, 2030–2032 |
| `copy_tree` (propagates `MNT_LOCKED`) | `fs/namespace.c` | 2162, 2188, 2213–2214 |
| `attach_recursive_mnt` (`MNT_LOCKED` transfer) | `fs/namespace.c` | 2564, 2663–2665 |
| `graft_tree` | `fs/namespace.c` | 2836 |
| `may_change_propagation` | `fs/namespace.c` | 2848 |
| `flags_to_propagation_type` | `fs/namespace.c` | 2865 |
| `do_change_type` | `fs/namespace.c` | 2881 |
| `may_copy_tree` | `fs/namespace.c` | 2960 |
| `copy_mnt_ns` (marks root `MNT_LOCKED`) | `fs/namespace.c` | 4239, 3145, 3166 |
| `can_idmap_mount` | `fs/namespace.c` | 4806 (after `path_pivot_root`) |
| `path_pivot_root` | `fs/namespace.c` | 4678 |
| `SYSCALL_DEFINE2(pivot_root)` | `fs/namespace.c` | 4774 |
| `mntns_install` | `fs/namespace.c` | 6490 |

**Security property.** The load-bearing invariant is **`MNT_LOCKED`: a mount
that was already mounted-over when the namespace was created may not be
detached, because detaching it would reveal what it was hiding.** When
`copy_mnt_ns` builds a new namespace it marks the copied root `MNT_LOCKED`
(3166) and `copy_tree` propagates the flag to every clone (2213–2214);
`umount` refuses locked mounts (1946, 2032), `disconnect_mount` refuses to
disconnect them (1765), and `attach_recursive_mnt` *transfers* the flag rather
than dropping it when a locked mount is displaced (2663–2665). `path_pivot_root`
(4678) does the same transfer for the old root (4730–4732). Without this, an
unprivileged user namespace could unmount an overmount to expose a directory
the sandbox had deliberately covered.

The second invariant is **namespace membership**: `check_mnt` (947) is the
one-line predicate `mnt->mnt_ns == current->nsproxy->mnt_ns`, and it gates
every structural operation — `do_umount` (1943), `can_umount` (2030),
`may_copy_tree` (2965), the mount-target checks (3024, 3347, 3386), and
`path_pivot_root`'s check on both new root and current root (4706). This is
what confines mount-tree edits to the caller's own namespace.

`path_pivot_root` (4678) is worth reading as a single conjunction: it requires
`may_mount()`, then rejects shared propagation on the old mount, the new
mount's ex-parent, and the root's parent (4702–4705); requires both root and
new root in the caller's namespace (4706); rejects a `MNT_LOCKED` new root
(4708); requires both to be actual mountpoints with parents (4714–4721); and
requires mutual reachability (`is_path_reachable`, 4723, 4726). Only then does
it perform the swap. Every one of those clauses is load-bearing.

### 6.2 Propagation

| Symbol | File | Lines |
|---|---|---|
| `change_mnt_propagation` | `fs/pnode.c` | 93 |
| `transfer_propagation` | `fs/pnode.c` | 74 |
| `propagation_next` / `__propagation_next` | `fs/pnode.c` | 204 / 177 |
| `next_group` | `fs/pnode.c` | 228 |
| `need_secondary` | `fs/pnode.c` | 260 |
| `find_master` | `fs/pnode.c` | 274 |
| `propagate_mnt` | `fs/pnode.c` | 311 |
| `propagation_would_overmount` | `fs/pnode.c` | 395 |
| `propagate_mount_busy` | `fs/pnode.c` | 423 |
| `propagate_mount_unlock` | `fs/pnode.c` | 466 |
| `gather_candidates` / `trim_ancestors` / `handle_locked` | `fs/pnode.c` | 500 / 542 / 597 |
| `propagate_umount` | `fs/pnode.c` | 658 |

**Security property.** Propagation types (`MS_SHARED`, `MS_PRIVATE`,
`MS_SLAVE`, `MS_UNBINDABLE`) define a directed graph over mounts along which
mount and umount events replicate. The property is *directional containment*:
a **slave** receives events from its master but must not send events back, and
**private**/**unbindable** must neither send nor receive. `do_change_type`
(2881) is the only way to change a propagation type and requires
`ns_capable(ns->user_ns, CAP_SYS_ADMIN)` in the namespace owning the mount
(`may_change_propagation`, 2848) plus exactly one propagation flag
(`flags_to_propagation_type`'s `is_power_of_2` test, 2874).
`propagate_umount` (658) is the delicate half — `gather_candidates` (500),
`trim_ancestors` (542) and `handle_locked` (597) exist to ensure a propagated
umount never detaches a locked mount or a mount still in use elsewhere in the
peer group.

**Why sandboxes depend on this** (6.1 + 6.2). A container's filesystem view is
built by `pivot_root` into a prepared tree; propagation type is what decides
whether the host's later mounts appear inside the container (and, worse,
whether the container's mounts appear on the host). Runtimes explicitly set
the container root to `MS_PRIVATE` or `MS_SLAVE` for exactly this reason. And
`MNT_LOCKED` is why an unprivileged sandbox cannot simply unmount the
`/proc/kcore` overmount that the runtime placed to hide it.

### 6.3 Mount idmapping (the second consumer of §1.2)

| Symbol | File | Lines |
|---|---|---|
| `struct mnt_idmap` (two `uid_gid_map`s) | `fs/mnt_idmapping.c` | 20–24 |
| `nop_mnt_idmap` | `fs/mnt_idmapping.c` | 31 |
| `initial_idmapping` | `fs/mnt_idmapping.c` | 54 |
| `make_vfsuid` | `fs/mnt_idmapping.c` | 80, 96 |
| `make_vfsgid` | `fs/mnt_idmapping.c` | 120, 135 |
| `from_vfsuid` | `fs/mnt_idmapping.c` | 150, 159 |
| `from_vfsgid` | `fs/mnt_idmapping.c` | 179, 188 |
| `copy_mnt_idmap` | `fs/mnt_idmapping.c` | 219 |
| `alloc_mnt_idmap` | `fs/mnt_idmapping.c` | 287 |
| `statmount_mnt_idmap` | `fs/mnt_idmapping.c` | 339, 373 |
| `can_idmap_mount` | `fs/namespace.c` | 4806 |

**Security property.** An idmapped mount applies a `uid_gid_map` at the
*mount* rather than at the process, so the same on-disk inode presents
different owners through different mounts. `make_vfsuid` (80) calls
`map_id_down` on the mount's `uid_map`; `from_vfsuid` (150) calls `map_id_up`
— i.e. the identical machinery from §1.2 with the identical invariants.
`copy_mnt_idmap` (219) reads `nr_extents` with `READ_ONCE` + `smp_rmb` (222–
224) and refuses to copy a map with `nr_extents == 0` (235), documenting in
its comment why a torn read must not be tolerated. `can_idmap_mount` refuses
to idmap a mount that has ever been visible in the hierarchy, requires
`CAP_SYS_ADMIN` over the superblock's user_ns, and requires the filesystem to
opt in with `FS_ALLOW_IDMAP`.

**Why sandboxes depend on this.** Idmapped mounts are how modern runtimes give
a container a shifted view of a shared volume without `chown`-ing the host
tree. They mean §1.2's arithmetic is on the file-access path even for sandboxes
that use no user namespace at all.

### 6.4 overlayfs

| Symbol | File | Lines |
|---|---|---|
| `ovl_permission` | `fs/overlayfs/inode.c` | 306 |
| `ovl_copy_xattr` | `fs/overlayfs/copy_up.c` | 75, 156 |
| copy-up of `security.capability` | `fs/overlayfs/copy_up.c` | 787, 1106–1111 |
| `ovl_own_xattr_get` / `_set` (trusted/user `overlay.*`) | `fs/overlayfs/xattrs.c` | 174 / 192 |
| `security.capability` idmapping note | `fs/overlayfs/xattrs.c` | 87 |
| `ovl_get_link` | `fs/overlayfs/inode.c` | ~341 |

**Security property.** overlayfs performs every underlying operation with the
**mounter's** credentials, not the accessing task's. `ovl_permission` (306)
therefore does a *double* check: `generic_permission` against the overlay
inode with the caller's creds (325), then `inode_permission` on the real inode
under `with_ovl_creds` (336–337). The property is that overlay access is the
*intersection* of what the caller may do and what the mounter may do — if
either check fails, access fails. It also downgrades a write request to a read
request when there is no upper inode yet (329–334), because the write will be
served by a copy-up performed as the mounter. Copy-up must not launder
privilege: the `security.capability` xattr is explicitly re-set or removed on
copy-up (1106–1111), and `xattrs.c:87` notes that `vfs_getxattr` (not
`__vfs_getxattr`) is used so the capability rootid is passed through mount
idmapping.

**Why sandboxes depend on this.** Container images are overlay stacks. The
mounter-credentials design is what allows an unprivileged runtime to expose a
read-only lower layer; the `security.capability` handling on copy-up is what
prevents a container from turning a lower-layer file capability into an
upper-layer one under different ownership.

---

## 7. ptrace scoping

| Symbol | File | Lines |
|---|---|---|
| `ptracer_access_allowed` | `kernel/ptrace.c` | 52 |
| `ptrace_access_vm` | `kernel/ptrace.c` | 69 |
| `ptrace_check_attach` | `kernel/ptrace.c` | 257 |
| `ptrace_has_cap` | `kernel/ptrace.c` | 286 |
| `task_still_dumpable` | `kernel/ptrace.c` | 293 |
| `__ptrace_may_access` | `kernel/ptrace.c` | 305 |
| `ptrace_may_access` | `kernel/ptrace.c` | 374 |
| `ptrace_attach` | `kernel/ptrace.c` | 434 |
| `ptrace_traceme` | `kernel/ptrace.c` | 512 |
| `cap_ptrace_access_check` | `security/commoncap.c` | 164 |
| `cap_ptrace_traceme` | `security/commoncap.c` | 201 |

**Security property.** `__ptrace_may_access` (305) is the single predicate
behind both `ptrace(2)` and sensitive `/proc` reads. Its clauses: the caller
must have declared which credential set to use (`PTRACE_MODE_FSCREDS` xor
`PTRACE_MODE_REALCREDS`, 311); same-thread-group is always allowed (326);
otherwise **all six** of the target's uid/euid/suid and gid/egid/sgid must
equal the caller's (345–351) — not just the effective ids, which is what stops
a partially-dropped-privilege target from being attachable; failing that,
`ptrace_has_cap` (286) against the *target's* user namespace. Then the subtle
part: an `smp_rmb()` (365) followed by `task_still_dumpable` (293), with the
comment at 356–364 explaining that dumpability must be read *after* the
credentials, paired with a write barrier in `commit_creds()`, or a task that
drops privileges concurrently could be attached as though it had not become
non-dumpable. Finally `security_ptrace_access_check` (368) gives LSMs
(including Yama) a veto. `cap_ptrace_access_check` (164) supplies the
capability-layer rule: the tracer needs `CAP_SYS_PTRACE` in the tracee's user
namespace, and in `PTRACE_MODE_NOAUDIT`-less mode its permitted set must be a
superset of the tracee's.

**Why sandboxes depend on this.** ptrace is a total-control primitive: a
successful attach lets the tracer write the tracee's registers and memory,
which means inheriting its credentials and its seccomp filter's *context*
(though not removing the filter). Sandboxes that place several processes at
different privilege levels in one namespace — a supervisor and a workload —
depend entirely on `__ptrace_may_access` to keep the workload from attaching
to the supervisor. The six-id equality rule and the dumpability barrier are
the two clauses that make that hold under credential changes.

---

## 8. Attack-surface amplifiers

### 8.1 io_uring

| Symbol | File | Lines |
|---|---|---|
| `io_uring_allowed` (sysctl / group gate) | `io_uring/io_uring.c` | 3123 |
| `sysctl_io_uring_disabled` / `_group` | `io_uring/io_uring.c` | 129–147 |
| `io_check_restriction` | `io_uring/io_uring.c` | 1685 |
| SQE flag validation (`SQE_VALID_FLAGS`) | `io_uring/io_uring.c` | 1776 |
| personality lookup + `security_uring_override_creds` | `io_uring/io_uring.c` | 1830–1836 |
| per-request `override_creds` / `revert_creds` | `io_uring/io_uring.c` | 1386–1402 |
| `io_register_restrictions` | `io_uring/register.c` | 167 |
| `io_register_restrictions_task` | `io_uring/register.c` | 201 |
| `IORING_SETUP_R_DISABLED` enable path | `io_uring/register.c` | 279–293 |
| SQPOLL thread credential override | `io_uring/sqpoll.c` | 220–239, 466 |
| `io_uring_populate_bpf_ctx` | `io_uring/bpf_filter.c` | 26 |
| `__io_uring_run_bpf_filters` | `io_uring/bpf_filter.c` | 57 |
| `io_uring_check_cbpf_filter` | `io_uring/bpf_filter.c` | 174 |
| `io_bpf_filter_import` / `io_register_bpf_filter` | `io_uring/bpf_filter.c` | 313 / 359 |

**Provenance of `io_uring/bpf_filter.c` (checked, because §8.1's conclusions are
load-bearing).** The file is **mainline**, and every conclusion below applies to
an upstream kernel, not to a branch.

| Question | Answer (from `~/linux-full` git history) |
|---|---|
| Introducing commit | `d42eb05e60fe` "io_uring: add support for BPF filtering for opcode restrictions", Jens Axboe, authored 2026-01-15, committed 2026-01-27 |
| Merge into mainline | `591beb0e3a03` `Merge tag 'io_uring-bpf-restrictions.4-20260206'` from `git.kernel.org/.../axboe/linux`, 2026-02-09 |
| First release | `git describe --contains d42eb05e60fe` -> `v7.0-rc1~222^2~6`; i.e. the file first appears in **v7.0-rc1** |
| Reachable from HEAD | yes (`git merge-base --is-ancestor d42eb05e60fe HEAD`) |
| Evolution since | 10 further commits, most recently `785d4625d3e0` "use `bpf_prog_run_pin_on_cpu()` to prevent migration", merged by `e67bf352a084` `Merge tag 'io_uring-7.0-20260312'`. `ed82f35b926b` "allow registration of per-task restrictions" is what adds `io_register_restrictions_task` (`io_uring/register.c` 201). |
| Upstream posting | not identifiable offline: `d42eb05e60fe` carries only a `Signed-off-by:` and no `Link:` tag. The pull-request text in `591beb0e3a03` is the best offline record of intent. |

Two corrections to the provenance as it was reported to me: the file landed in
**v7.0-rc1**, not v7.0-rc4; and `io_uring-7.0-20260312` is the tag of the
*most recent* merge touching the file (bringing `785d4625d3e0`), not the merge
that introduced it. Both are bookkeeping errors in the same direction — the
substantive claim, that this is mainline and §8.1 stands as written, is
confirmed.

Worth quoting, because it corroborates §8.1's framing in the maintainer's own
words, from the merge commit `591beb0e3a03`: *"seccomp and io_uring don't play
along nicely, as most of the interesting data to filter on resides somewhat
out-of-band, in the submission queue ring. As a result, things like containers
and systemd that apply seccomp filters, can't filter io_uring operations."*

**Security property.** io_uring is the hard case for sandboxes because it
*decouples the syscall from the operation*: a single `io_uring_enter` executes
an arbitrary batch of file, network and (via `IORING_OP_URING_CMD`) driver
operations, so a seccomp filter that allows `io_uring_enter` has allowed all
of them. This kernel provides three in-subsystem mitigations, each with its
own property:

- **Availability gate.** `io_uring_allowed` (3123) returns `-EPERM` when
  `sysctl_io_uring_disabled == 2` (3128); when it is `1`, only `CAP_SYS_ADMIN` or
  membership in `sysctl_io_uring_group` passes (3131–3139), and
  `security_uring_allowed()` (3142) gets the final word. Note the group is resolved
  with `make_kgid(&init_user_ns, ...)` (3134) — deliberately the *initial*
  namespace, so a user namespace cannot fabricate membership.
- **Credential confinement.** A request may carry a registered "personality"
  (1830), and the ring's credentials are applied with `override_creds` around
  issue (1386–1402); the SQPOLL kernel thread does the same with the
  credentials captured at setup (`sqpoll.c` 466, applied 220–239). The
  property: **a request never executes with more authority than the credentials
  registered at setup time**, and every override is mediated by
  `security_uring_override_creds` (1834).
- **Opcode filtering.** `io_register_restrictions` (167) and the newer cBPF
  filters (`bpf_filter.c`) restrict which opcodes a ring may submit.
  `io_uring_check_cbpf_filter` (174) is a near-exact structural clone of
  `seccomp_check_filter` (§3): the same opcode allowlist, with the bound
  `k < sizeof(struct io_uring_bpf_ctx) && !(k & 3)` (188) instead of
  `seccomp_data`. `__io_uring_run_bpf_filters` (57) fails closed — a filter
  returning 0 denies the request and stops further filter processing, and the
  `dummy_filter` sentinel (25) denies unconditionally. Restrictions may only be
  registered while the ring is `IORING_SETUP_R_DISABLED` (173, 279–293), so
  they cannot be relaxed after the ring goes live.

**Why sandboxes depend on this.** Most container/agent sandboxes today block
io_uring outright, precisely because seccomp cannot see inside it. The
material change is that io_uring now has its own cBPF filter layer — meaning a
sandbox *can* allow io_uring with an opcode policy, and the trustworthiness of
that policy rests on a validator that has never been verified and that
duplicates seccomp's logic rather than sharing it.

### 8.2 eBPF

| Symbol | File | Lines |
|---|---|---|
| `sysctl_unprivileged_bpf_disabled` | `kernel/bpf/syscall.c` | 69 |
| `CAP_BPF` gating (`bpf_token_capable`) | `kernel/bpf/syscall.c` | 1274, 1470, 1507, 3015, 3030, 5635 |
| `bpf_check` (verifier entry) | `kernel/bpf/verifier.c` | 19771 |
| `do_check_main` / `do_check` | `kernel/bpf/verifier.c` | 18579 / 17340 |
| `check_mem_access` | `kernel/bpf/verifier.c` | 6078 |
| `check_helper_call` | `kernel/bpf/verifier.c` | 10171 |
| `check_alu_op` | `kernel/bpf/verifier.c` | 14917 |
| `adjust_reg_min_max_vals` | `kernel/bpf/verifier.c` | 14749 |
| tristate-number abstract domain | `kernel/bpf/tnum.c` | whole file (319 lines); operators 17–217 |
| `___bpf_prog_run` (interpreter) | `kernel/bpf/core.c` | 1852 |
| `__bpf_prog_select_runtime` | `kernel/bpf/core.c` | 2667 |
| cgroup-attached BPF (device/socket policy) | `kernel/bpf/cgroup.c` | whole file (2796 lines) |

**Security property.** eBPF inverts the usual trust direction: userspace
uploads code that runs *in kernel context*, and the only thing standing
between it and arbitrary kernel memory is the static verifier
(`bpf_check`, 19771). Its central obligation is **soundness of the abstract
interpretation**: for every instruction, the abstract state
(`bpf_reg_state`'s tnum plus signed/unsigned min/max) must over-approximate
every concrete state reachable at that point, so that a range check performed
abstractly (`check_mem_access`, 6078) implies the concrete access is in
bounds. `kernel/bpf/tnum.c` is the abstract domain itself — 319 lines of pure
`u64` bit arithmetic (`tnum_add` 63, `tnum_sub` 75, `tnum_and` 92, `tnum_mul`
137, `tnum_intersect` 174, `tnum_union` 188, `tnum_cast` 196, `tnum_in` 210)
whose soundness (`x ∈ a ∧ y ∈ b -> x op y ∈ tnum_op(a, b)`) every bounds
conclusion rests on. A soundness gap in ~40 lines of bit-twiddling is a
kernel-memory read/write primitive. Access is gated by `CAP_BPF` plus
`sysctl_unprivileged_bpf_disabled` (69, 1470, 3030) — and note `CAP_BPF` is
checked against the *initial* namespace semantics via `bpf_token_capable`, so
a user namespace does not confer it.

**Why sandboxes depend on this.** For most sandboxes, eBPF is not a
primitive to rely on but a surface to remove: if a sandboxed process can load
a program, verifier soundness becomes the sandbox boundary, which is a far
larger trusted computing base than namespaces plus seccomp. Conversely, the
*host* side often uses cgroup-attached BPF (`kernel/bpf/cgroup.c`) for device
and socket policy, so a sandbox's egress rules may themselves be BPF programs
— which puts the verifier on both sides of the boundary.

---

## 9. Dependency summary

The mechanisms are not independent. Reading the citations above bottom-up:

```
     kernel/user_namespace.c  map_id_{down,up}  +  struct uid_gid_map
                    (§1.2 — the ID-mapping algebra)
                                  |
        +-------------------------+--------------------------+
        |                         |                          |
  make_kuid/from_kuid      fs/mnt_idmapping.c          verify_root_map,
  (task identity)          make_vfsuid/from_vfsuid     new_idmap_permitted
        |                  (idmapped mounts, §6.3)     (write-path policy)
        |                         |
        |                  overlayfs copy-up of security.capability (§6.4)
        |                         |
  cap_capable_helper       get_vfs_caps_from_disk, cap_convert_nscap,
  (§2a, ns-scoped caps)    cap_inode_getsecurity  (§2c, fscaps)
        |
   ns_capable  --->  every namespace ->install (§1.1–1.5),
                     may_change_propagation (§6.2), can_idmap_mount (§6.3),
                     may_mount / pivot_root (§6.1), cgroup delegation (§4),
                     ptrace_has_cap (§7), io_uring_allowed (§8.1)
```

Every capability check in the kernel is `ns_capable`, every `ns_capable`
resolves through `cap_capable_helper`'s namespace walk, and a large share of
the identity comparisons that walk performs (`uid_eq(ns->owner, cred->euid)`)
and that the file-capability code performs are values produced by
`map_id_down`/`map_id_up`. **The ID-mapping algebra in
`kernel/user_namespace.c` is the deepest node in this graph**, which is what
motivates the Phase 1 scoring in `ROADMAP.md`.
