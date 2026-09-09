// SPDX-License-Identifier: GPL-2.0
#![no_std]
#![allow(clippy::needless_return)]
//! Faithful Rust reimplementation of the Linux user-namespace ID-mapping
//! algebra: `kernel/user_namespace.c` and the `struct uid_gid_map` machinery
//! in `include/linux/user_namespace.h`, at kernel
//! `v7.2-rc7-687-ge172eee25cfe` (`~/linux-full`).
//!
//! Specification: `../SPEC.md`. Target selection and scope: `../ROADMAP.md`.
//!
//! # Faithfulness rules observed here
//!
//! 1. **The C control flow is recognizable.** The linear scans stay indexed
//!    `while` loops, the binary search stays `__inline_bsearch`'s loop shape.
//!    No iterator chains, no `slice::binary_search`.
//! 2. **The C's checks appear in the C's order**, including the ones SPEC
//!    §1.2.1 proves redundant. Redundant in the C means redundant here.
//! 3. **Wrapping arithmetic is explicit at each site** (`wrapping_add` /
//!    `wrapping_sub`) wherever the C relies on `u32` wraparound, rather than
//!    relying on a profile setting.
//! 4. **One Rust function per C function, same name**, with the C file and
//!    line range in its doc comment.
//!
//! Every departure is tagged `// DEVIATION` with its justification.
//! Every place the model captures something the C does implicitly is tagged
//! `// MODEL`.

// ======================================================================
// Constants — include/linux/user_namespace.h:16-17
// ======================================================================

/// `UID_GID_MAP_MAX_BASE_EXTENTS`, include/linux/user_namespace.h:16
pub const UID_GID_MAP_MAX_BASE_EXTENTS: usize = 5;
/// `UID_GID_MAP_MAX_EXTENTS`, include/linux/user_namespace.h:17
pub const UID_GID_MAP_MAX_EXTENTS: usize = 340;

/// The failure sentinel the C returns as `(u32) -1`
/// (kernel/user_namespace.c:333, :399). SPEC §1.1 `⊥`.
pub const ID_SENTINEL: u32 = 0xFFFF_FFFF;

/// MODEL: the value written over the base extents when `insert_extent`
/// migrates to the heap arm and the two pointers overwrite the first 16 bytes
/// of the union (SPEC §1.3, Model T).
///
/// The C writes *kernel heap pointer bytes* there, which this model cannot
/// reproduce; a fixed constant is a refinement of "unspecified". It is chosen
/// distinguishable so that a read which should never happen would be visible
/// both to the Lean theorem S5 and to the Phase 4 differential harness (the C
/// would show pointer bytes, this shows `0xDEADBEEF`).
pub const CLOBBER_POISON: u32 = 0xDEAD_BEEF;

// ======================================================================
// Data model — SPEC §1.1, §1.3
// ======================================================================

/// `struct uid_gid_extent`, include/linux/user_namespace.h:19-23
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct UidGidExtent {
    pub first: u32,
    pub lower_first: u32,
    pub count: u32,
}

/// `struct uid_gid_map`, include/linux/user_namespace.h:25-35 — **Model T**
/// (SPEC §1.3): the C union's two arms are separate fields here, and the
/// aliasing is reproduced explicitly by `insert_extent`'s clobber write.
///
/// The C layout being modelled:
///
/// ```text
/// offset:  0                    16                60      64
///          |  extent[0..1]       |  extent[2..4]   | nr_ex |   arm 1
///          | forward | reverse   |  (not aliased)  | nr_ex |   arm 2
/// ```
///
/// `nr_extents` sits at offset 60, past the 16 bytes the two pointers alias,
/// so it is readable in both arms — which is what makes the union sound and
/// what lets `insert_extent` destroy `extent[0]` and `extent[1].first`.
///
/// DEVIATION: `forward`/`reverse` are fixed 340-slot arrays plus liveness
/// flags, not pointers. Justified because the C caps the extent count at
/// `UID_GID_MAP_MAX_EXTENTS` (kernel/user_namespace.c:1041), so no reachable
/// state needs more, and Charon/Aeneas cannot model raw pointers. The
/// consequence is that the `-ENOMEM` paths at :798 and :868 are unreachable
/// here; see SPEC §7 item 6.
pub struct UidGidMap {
    /// Union arm 1: `extent[UID_GID_MAP_MAX_BASE_EXTENTS]`.
    pub extent: [UidGidExtent; UID_GID_MAP_MAX_BASE_EXTENTS],
    /// Union arm 2: `*forward`, sorted by `first` once `sort_idmaps` has run.
    pub forward: [UidGidExtent; UID_GID_MAP_MAX_EXTENTS],
    /// Union arm 2: `*reverse`, sorted by `lower_first`.
    pub reverse: [UidGidExtent; UID_GID_MAP_MAX_EXTENTS],
    /// MODEL: `map->forward != NULL`.
    pub forward_live: bool,
    /// MODEL: `map->reverse != NULL`. NULL between `insert_extent`'s
    /// migration (:812) and `sort_idmaps` (:866) — see SPEC `WF-REVERSE-LIVE`.
    pub reverse_live: bool,
    /// `nr_extents`, at union offset 60.
    pub nr_extents: u32,
}

impl UidGidMap {
    /// `memset(&new_map, 0, sizeof(struct uid_gid_map))`,
    /// kernel/user_namespace.c:975.
    pub fn zeroed() -> UidGidMap {
        let z = UidGidExtent { first: 0, lower_first: 0, count: 0 };
        UidGidMap {
            extent: [z; UID_GID_MAP_MAX_BASE_EXTENTS],
            forward: [z; UID_GID_MAP_MAX_EXTENTS],
            reverse: [z; UID_GID_MAP_MAX_EXTENTS],
            forward_live: false,
            reverse_live: false,
            nr_extents: 0,
        }
    }

    /// `init_user_ns.uid_map`, kernel/user.c:39-48.
    ///
    /// Note `count` is `4294967295` = `2^32 - 1`, **not** `2^32`: the initial
    /// namespace deliberately does not map the sentinel. SPEC §1.2.2, §7.10.
    pub fn init_user_ns_map() -> UidGidMap {
        let mut m = UidGidMap::zeroed();
        m.extent[0] = UidGidExtent { first: 0, lower_first: 0, count: 4294967295 };
        m.nr_extents = 1;
        return m;
    }
}

/// `struct idmap_key`, kernel/user_namespace.c:240-244
///
/// DEVIATION: `Copy`, and passed to `cmp_map_id` **by value** rather than
/// behind a reference as the C's `const void *k`. Semantics-preserving:
/// `cmp_map_id` only reads the key and the C's key is a stack local at both
/// call sites (:286-288, :375-377), so no aliasing or mutation is observable.
/// This is also a **workaround for an Aeneas blocker** — branching on a
/// `bool` read through a reference, where the branch's joined value then
/// feeds a later condition, hits an internal `Unreachable` in
/// `InterpAbs.merge_abs_conts_aux`. See OPEN_CHALLENGES.md B-1 for the
/// five-line reproducer.
#[derive(Clone, Copy)]
pub struct IdmapKey {
    /// `true` -> id from kid; `false` -> kid from id
    pub map_up: bool,
    pub id: u32,
    pub count: u32,
}

// ======================================================================
// The comparison predicate — kernel/user_namespace.c:251-275
// ======================================================================

/// `cmp_map_id`, kernel/user_namespace.c:251-275.
///
/// DEVIATION: takes typed references instead of `const void *`, and the
/// `bsearch` callback indirection is monomorphized away (SPEC `A-BSEARCH`,
/// ROADMAP §5.1). The callback target is statically unique at both call
/// sites (:292, :381), so specializing it carries no data.
pub fn cmp_map_id(key: IdmapKey, el: &UidGidExtent) -> i32 {
    let first: u32;
    let last: u32;
    let id2: u32;

    // WRAPPING (:255). `key->id + key->count - 1` is u32 arithmetic. It wraps
    // when the caller hands in a range crossing 2^32; SPEC §4.1 is the
    // statement that it does not wrap for ranges that hit a well-formed map.
    id2 = key.id.wrapping_add(key.count).wrapping_sub(1);

    // handle map_id_{down,up}() — :262-266
    if key.map_up {
        first = el.lower_first;
    } else {
        first = el.first;
    }

    // WRAPPING (:269). `first + el->count - 1`.
    last = first.wrapping_add(el.count).wrapping_sub(1);

    if key.id >= first && key.id <= last && id2 >= first && id2 <= last {
        return 0;
    }

    if key.id < first || id2 < first {
        return -1;
    }

    return 1;
}

// ======================================================================
// The monomorphized binary search — include/linux/bsearch.h:9-28
// ======================================================================

/// `__inline_bsearch`, include/linux/bsearch.h:9-28, specialized to
/// `(struct uid_gid_extent, cmp_map_id)`.
///
/// The loop shape is preserved exactly, including the `num--` on the
/// greater-than branch *before* the unconditional `num >>= 1` — the site
/// where an off-by-one would live (SPEC §4.4 obligation 2). Pointer
/// arithmetic becomes index arithmetic: `base` is `lo`, `pivot` is an index,
/// and `+ size` is `+ 1`.
///
/// DEVIATION: returns `Option<UidGidExtent>` (a copy) rather than a pointer
/// into the array. The two call sites (:292, :381) only ever read `->first`
/// and `->lower_first` from the result and never write through it, so copying
/// is semantics-preserving; and Aeneas rejects references nested in `Option`
/// (prior spike barriers 2-3).
fn bsearch_extent(
    key: IdmapKey,
    arr: &[UidGidExtent; UID_GID_MAP_MAX_EXTENTS],
    nmemb: usize,
) -> Option<UidGidExtent> {
    let mut lo: usize = 0;
    let mut num: usize = nmemb;

    while num > 0 {
        let pivot: usize = lo + (num >> 1);
        let result: i32 = cmp_map_id(key, &arr[pivot]);

        if result == 0 {
            return Some(arr[pivot]);
        }

        if result > 0 {
            lo = pivot + 1;
            num -= 1;
        }

        num >>= 1;
    }

    return None;
}

// ======================================================================
// Downward mapping — kernel/user_namespace.c:278-341
// ======================================================================

/// `map_id_range_down_max`, kernel/user_namespace.c:282-292.
/// Binary search over the `forward` array. Only callable when the number of
/// mappings exceeds `UID_GID_MAP_MAX_BASE_EXTENTS`.
fn map_id_range_down_max(
    extents: u32,
    map: &UidGidMap,
    id: u32,
    count: u32,
) -> Option<UidGidExtent> {
    let key = IdmapKey { map_up: false, count, id };
    return bsearch_extent(key, &map.forward, extents as usize);
}

/// `map_id_range_down_base`, kernel/user_namespace.c:300-316.
/// Linear scan over the static base array. Only callable when the number of
/// mappings is `<= UID_GID_MAP_MAX_BASE_EXTENTS`.
fn map_id_range_down_base(
    extents: u32,
    map: &UidGidMap,
    id: u32,
    count: u32,
) -> Option<UidGidExtent> {
    let mut idx: u32;
    let mut first: u32;
    let mut last: u32;
    let id2: u32;

    // WRAPPING (:304).
    id2 = id.wrapping_add(count).wrapping_sub(1);

    // Find the matching extent — :307-314
    idx = 0;
    while idx < extents {
        let e: UidGidExtent = map.extent[idx as usize];
        first = e.first;
        // WRAPPING (:310).
        last = first.wrapping_add(e.count).wrapping_sub(1);
        if id >= first && id <= last && id2 >= first && id2 <= last {
            return Some(e);
        }
        idx += 1;
    }
    return None;
}

/// `map_id_range_down`, kernel/user_namespace.c:318-336.
pub fn map_id_range_down(map: &UidGidMap, id: u32, count: u32) -> u32 {
    let extent: Option<UidGidExtent>;
    let extents: u32 = map.nr_extents;
    // MODEL: `smp_rmb()` (:322). A sequential model cannot express the
    // publication protocol this barrier is half of; it is assumption `A-PUB`
    // (SPEC §3, §7 item 1) and NOT something these theorems establish.
    // smp_rmb();

    if extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        extent = map_id_range_down_base(extents, map, id, count);
    } else {
        extent = map_id_range_down_max(extents, map, id, count);
    }

    // Map the id or note failure — :329-334
    match extent {
        Some(e) => {
            // WRAPPING (:331). `(id - extent->first) + extent->lower_first`.
            return id.wrapping_sub(e.first).wrapping_add(e.lower_first);
        }
        None => {
            return ID_SENTINEL;
        }
    }
}

/// `map_id_down`, kernel/user_namespace.c:338-341.
pub fn map_id_down(map: &UidGidMap, id: u32) -> u32 {
    return map_id_range_down(map, id, 1);
}

// ======================================================================
// Upward mapping — kernel/user_namespace.c:344-407
// ======================================================================

/// `map_id_range_up_base`, kernel/user_namespace.c:349-365.
fn map_id_range_up_base(
    extents: u32,
    map: &UidGidMap,
    id: u32,
    count: u32,
) -> Option<UidGidExtent> {
    let mut idx: u32;
    let mut first: u32;
    let mut last: u32;
    let id2: u32;

    // WRAPPING (:353).
    id2 = id.wrapping_add(count).wrapping_sub(1);

    // Find the matching extent — :356-363
    idx = 0;
    while idx < extents {
        let e: UidGidExtent = map.extent[idx as usize];
        first = e.lower_first;
        // WRAPPING (:359).
        last = first.wrapping_add(e.count).wrapping_sub(1);
        if id >= first && id <= last && id2 >= first && id2 <= last {
            return Some(e);
        }
        idx += 1;
    }
    return None;
}

/// `map_id_range_up_max`, kernel/user_namespace.c:372-382.
/// Binary search over the `reverse` array.
fn map_id_range_up_max(
    extents: u32,
    map: &UidGidMap,
    id: u32,
    count: u32,
) -> Option<UidGidExtent> {
    let key = IdmapKey { map_up: true, count, id };
    return bsearch_extent(key, &map.reverse, extents as usize);
}

/// `map_id_range_up`, kernel/user_namespace.c:384-402.
pub fn map_id_range_up(map: &UidGidMap, id: u32, count: u32) -> u32 {
    let extent: Option<UidGidExtent>;
    let extents: u32 = map.nr_extents;
    // MODEL: `smp_rmb()` (:388). See `map_id_range_down`. Assumption `A-PUB`.
    // smp_rmb();

    if extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        extent = map_id_range_up_base(extents, map, id, count);
    } else {
        extent = map_id_range_up_max(extents, map, id, count);
    }

    // Map the id or note failure — :395-400
    match extent {
        Some(e) => {
            // WRAPPING (:397). `(id - extent->lower_first) + extent->first`.
            return id.wrapping_sub(e.lower_first).wrapping_add(e.first);
        }
        None => {
            return ID_SENTINEL;
        }
    }
}

/// `map_id_up`, kernel/user_namespace.c:404-407.
pub fn map_id_up(map: &UidGidMap, id: u32) -> u32 {
    return map_id_range_up(map, id, 1);
}

// ======================================================================
// The kuid/kgid interface — kernel/user_namespace.c:422-445
// ======================================================================

/// `make_kuid`, kernel/user_namespace.c:422-426.
/// `KUIDT_INIT` is the identity on the underlying `u32`.
pub fn make_kuid(uid_map: &UidGidMap, uid: u32) -> u32 {
    return map_id_down(uid_map, uid);
}

/// `from_kuid`, kernel/user_namespace.c:441-445.
pub fn from_kuid(targ_uid_map: &UidGidMap, kuid: u32) -> u32 {
    return map_id_up(targ_uid_map, kuid);
}

// ======================================================================
// Extent insertion and the union clobber — kernel/user_namespace.c:789-820
// ======================================================================

/// `insert_extent`, kernel/user_namespace.c:789-820.
///
/// This is the function Model T exists for: at `nr_extents == 5` the C
/// installs the two heap pointers over the first 16 bytes of the union,
/// which destroys `extent[0]` entirely and `extent[1].first`. That write is
/// reproduced below, so that "no read ever observes a clobbered slot" is
/// theorem S5 (`NO-STALE-READ`) rather than assumption `A-UNION`.
///
/// DEVIATION: the C's `-ENOMEM` path (:798) is unreachable here because the
/// 340-slot array is always present. Returns 0 always; the signature keeps
/// the `int` return so the call site in `map_write` stays recognizable.
pub fn insert_extent(map: &mut UidGidMap, extent: &UidGidExtent) -> i32 {
    if map.nr_extents == UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        // Allocate memory for 340 mappings — :796-799. Cannot fail here.

        // `memcpy(forward, map->extent, map->nr_extents * sizeof(...))`
        // — :803-804. Written as an indexed loop so Charon sees no intrinsic.
        let mut i: u32 = 0;
        while i < map.nr_extents {
            map.forward[i as usize] = map.extent[i as usize];
            i += 1;
        }

        map.forward_live = true; // `map->forward = forward;`  :806
        map.reverse_live = false; // `map->reverse = NULL;`     :807

        // MODEL: the two pointer stores above land on union offsets 0..15,
        // which are `extent[0]` (0..11) and `extent[1].first` (12..15).
        // Everything from offset 16 up — `extent[2..4]` — survives, and the
        // model preserves that too.
        map.extent[0] = UidGidExtent {
            first: CLOBBER_POISON,
            lower_first: CLOBBER_POISON,
            count: CLOBBER_POISON,
        };
        map.extent[1].first = CLOBBER_POISON;
    }

    // `dest = &map->extent[nr]` or `&map->forward[nr]`, then `*dest = *extent`
    // — :810-816. Split into two assignments because Model T's arms are
    // distinct fields; the branch structure is the C's.
    if map.nr_extents < UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        map.extent[map.nr_extents as usize] = *extent;
    } else {
        map.forward[map.nr_extents as usize] = *extent;
    }

    map.nr_extents += 1;
    return 0;
}

// ======================================================================
// The write path — kernel/user_namespace.c:745-782 (mappings_overlap),
// 823-876 (sort), 932-1118 (map_write, extent part)
// ======================================================================

/// `mappings_overlap`, kernel/user_namespace.c:745-782.
///
/// Checks the candidate extent against every extent already inserted, in
/// **both** coordinates: upper at :771-774, lower at :776-779. Note that in
/// `map_write` this runs at :1038, BEFORE the re-mapping loop at :1063-1083
/// overwrites `lower_first` — so the lower-range check here constrains the
/// parent-namespace ids, not the kernel-global ids the map ends up holding
/// (SPEC §1.5).
pub fn mappings_overlap(new_map: &UidGidMap, extent: &UidGidExtent) -> bool {
    let upper_first: u32;
    let lower_first: u32;
    let upper_last: u32;
    let lower_last: u32;
    let mut idx: u32;

    upper_first = extent.first;
    lower_first = extent.lower_first;
    // WRAPPING (:752, :753). `first + count - 1`; SPEC §1.2.1 shows the
    // caller's no-wrap checks at :1031/:1033 make these exact.
    upper_last = upper_first.wrapping_add(extent.count).wrapping_sub(1);
    lower_last = lower_first.wrapping_add(extent.count).wrapping_sub(1);

    idx = 0;
    while idx < new_map.nr_extents {
        let prev_upper_first: u32;
        let prev_lower_first: u32;
        let prev_upper_last: u32;
        let prev_lower_last: u32;
        let prev: UidGidExtent;

        // :761-764 — the third of the four union dispatch sites.
        if new_map.nr_extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
            prev = new_map.extent[idx as usize];
        } else {
            prev = new_map.forward[idx as usize];
        }

        prev_upper_first = prev.first;
        prev_lower_first = prev.lower_first;
        // WRAPPING (:768, :769).
        prev_upper_last = prev_upper_first.wrapping_add(prev.count).wrapping_sub(1);
        prev_lower_last = prev_lower_first.wrapping_add(prev.count).wrapping_sub(1);

        // Does the upper range intersect a previous extent? — :771-774
        if prev_upper_first <= upper_last && prev_upper_last >= upper_first {
            return true;
        }

        // Does the lower range intersect a previous extent? — :776-779
        if prev_lower_first <= lower_last && prev_lower_last >= lower_first {
            return true;
        }
        idx += 1;
    }
    return false;
}

/// The sort key selected by `cmp_extents_forward` (:823-836, key `first`) or
/// `cmp_extents_reverse` (:838-851, key `lower_first`).
///
/// DEVIATION: the two C comparison callbacks become one function with a
/// by-value `bool` selector. (By value, not through a reference: Aeneas
/// blocker B-1.)
fn sort_key(e: UidGidExtent, by_lower_first: bool) -> u32 {
    if by_lower_first {
        return e.lower_first;
    } else {
        return e.first;
    }
}

/// Inner step of an insertion sort: sink `arr[i]` leftwards while the element
/// before it has a strictly greater key.
///
/// Split from `sort_extents` so each function holds exactly one loop (Aeneas
/// computes one loop fixed point per function).
fn sort_sink(arr: &mut [UidGidExtent; UID_GID_MAP_MAX_EXTENTS], i: u32, by_lower_first: bool) {
    let mut j: u32 = i;
    while j > 0 && sort_key(arr[(j - 1) as usize], by_lower_first) > sort_key(arr[j as usize], by_lower_first) {
        let tmp: UidGidExtent = arr[j as usize];
        arr[j as usize] = arr[(j - 1) as usize];
        arr[(j - 1) as usize] = tmp;
        j -= 1;
    }
}

/// `sort(base, num, size, cmp, NULL)` — `lib/sort.c`, called at :870 and :872.
///
/// DEVIATION (`A-SORT`, ROADMAP Amendment 1): the kernel's heapsort (357 LOC,
/// callback comparison, size-dispatched byte swaps) is replaced by an
/// insertion sort with the same **contract** — the result is a permutation of
/// the input, sorted by the key. SPEC §1.5 argues the sorted order is unique
/// when keys are distinct, so any correct sort agrees with the kernel's; the
/// Phase 4 harness links the real `lib/sort.c` on the C side to test exactly
/// that. Stable, in place, and deliberately unclever.
fn sort_extents(arr: &mut [UidGidExtent; UID_GID_MAP_MAX_EXTENTS], n: u32, by_lower_first: bool) {
    let mut i: u32 = 1;
    while i < n {
        sort_sink(arr, i, by_lower_first);
        i += 1;
    }
}

/// `sort_idmaps`, kernel/user_namespace.c:856-876.
///
/// Sorts `forward` by `first`, duplicates it into `reverse`
/// (`kmemdup_array`, :866-869), sorts `reverse` by `lower_first`.
///
/// DEVIATION: `-ENOMEM` at :868-869 is unreachable (fixed array). Returns 0
/// always.
pub fn sort_idmaps(map: &mut UidGidMap) -> i32 {
    if map.nr_extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        return 0;
    }

    let n: u32 = map.nr_extents;

    // Sort forward array. — :862-863
    sort_extents(&mut map.forward, n, false);

    // Only copy the memory from forward we actually need. — :865-869
    let mut i: u32 = 0;
    while i < n {
        map.reverse[i as usize] = map.forward[i as usize];
        i += 1;
    }
    map.reverse_live = true;

    // Sort reverse array. — :871-873
    sort_extents(&mut map.reverse, n, true);

    return 0;
}

/// Linux errno values used by `map_write`. include/uapi/asm-generic/errno-base.h
pub const EPERM: i32 = 1;
pub const EINVAL: i32 = 22;

/// The body of `map_write` from the first parsed extent to the install,
/// kernel/user_namespace.c:975-1102, **on already-parsed extents**.
///
/// SCOPE (ROADMAP Amendment 2): the `__user` copy (:947-952), the
/// line-splitting and `simple_strtoul` parsing (:995-1020) and the mutex are
/// outside the model. The input `lines` is the sequence of `(first,
/// lower_first, count)` triples the parser would have produced, one per line,
/// in order. `next_line != NULL` at :1042 becomes `i + 1 < lines.len()`.
///
/// `A-CAPORACLE`: `cap_ok` stands for
/// `!(cap_valid(cap_setid) && !file_ns_capable(file, map_ns, CAP_SYS_ADMIN))`
/// at :986, and `permitted` for `new_idmap_permitted(...)` at :1056. Both are
/// inputs here; step 6 replaces `permitted` with the real function over an
/// oracle.
///
/// Return: `0` on success (DEVIATION: the C returns the byte count written,
/// which the model does not have), `-EPERM` / `-EINVAL` as the C. The
/// `goto out` cleanup at :1107-1113 is performed by the caller `map_write`.
fn map_write_body(
    map: &mut UidGidMap,
    parent_map: &UidGidMap,
    lines: &[UidGidExtent],
    cap_ok: bool,
    permitted: bool,
    new_map: &mut UidGidMap,
) -> i32 {
    let mut ret: i32;
    let mut idx: u32;

    ret = -EPERM;
    // Only allow one successful write to the map — :980
    if map.nr_extents != 0 {
        return ret;
    }

    // Adjusting namespace settings requires capabilities on the target. — :986
    if !cap_ok {
        return ret;
    }

    // Parse the user data — :990-1049
    ret = -EINVAL;
    let mut i: usize = 0;
    while i < lines.len() {
        let extent: UidGidExtent = lines[i];
        let has_next_line: bool = i + 1 < lines.len();

        // Verify we have been given valid starting values — :1024-1026.
        // SPEC §1.2.1: redundant given :1031/:1033, since first == (u32)-1
        // with count >= 1 wraps. Kept because the C keeps it.
        if extent.first == ID_SENTINEL || extent.lower_first == ID_SENTINEL {
            return ret;
        }

        // Verify count is not zero and does not cause the extent to wrap —
        // :1028-1034. WRAPPING: the u32 sum is compared against `first`; SPEC
        // §1.2.1 shows this accepts exactly count >= 1 && first + count <= 2^32-1.
        if extent.first.wrapping_add(extent.count) <= extent.first {
            return ret;
        }
        if extent.lower_first.wrapping_add(extent.count) <= extent.lower_first {
            return ret;
        }

        // Do the ranges in extent overlap any previous extents? — :1038
        if mappings_overlap(new_map, &extent) {
            return ret;
        }

        // :1041-1043 — the 340 cap. Exactly 340 extents fit; a 341st line fails.
        if new_map.nr_extents + 1 == UID_GID_MAP_MAX_EXTENTS as u32 && has_next_line {
            return ret;
        }

        ret = insert_extent(new_map, &extent);
        if ret < 0 {
            return ret;
        }
        ret = -EINVAL;
        i += 1;
    }
    // Be very certain the new map actually exists — :1052-1054
    if new_map.nr_extents == 0 {
        return ret;
    }

    ret = -EPERM;
    // Validate the user is allowed to use user id's mapped to. — :1056
    if !permitted {
        return ret;
    }

    ret = -EPERM;
    // Map the lower ids from the parent user namespace to the kernel global
    // id space. — :1063-1083. This is where lower_first is REWRITTEN (SPEC §1.5).
    idx = 0;
    while idx < new_map.nr_extents {
        let e: UidGidExtent;
        let lower_first: u32;

        // :1067-1070 — the fourth union dispatch site is verify_root_map's;
        // this one mirrors :761-764.
        if new_map.nr_extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
            e = new_map.extent[idx as usize];
        } else {
            e = new_map.forward[idx as usize];
        }

        lower_first = map_id_range_down(parent_map, e.lower_first, e.count);

        // Fail if we can not map the specified extent to the kernel global
        // id space. — :1079-1080
        if lower_first == ID_SENTINEL {
            return ret;
        }

        // `e->lower_first = lower_first;` — :1082
        if new_map.nr_extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
            new_map.extent[idx as usize].lower_first = lower_first;
        } else {
            new_map.forward[idx as usize].lower_first = lower_first;
        }
        idx += 1;
    }

    // If we want to use binary search for lookup, this clones the extent
    // array and sorts both copies. — :1089-1091
    ret = sort_idmaps(new_map);
    if ret < 0 {
        return ret;
    }

    // Install the map — :1094-1102
    if new_map.nr_extents <= UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        // memcpy(map->extent, new_map.extent, nr * sizeof(...)) — :1095-1096
        let mut k: u32 = 0;
        while k < new_map.nr_extents {
            map.extent[k as usize] = new_map.extent[k as usize];
            k += 1;
        }
    } else {
        // map->forward = new_map.forward; map->reverse = new_map.reverse; — :1098-1099
        map.forward = new_map.forward;
        map.reverse = new_map.reverse;
        map.forward_live = new_map.forward_live;
        map.reverse_live = new_map.reverse_live;
    }
    // MODEL: smp_wmb() (:1101) — the publication barrier. Assumption A-PUB.
    map.nr_extents = new_map.nr_extents;

    // *ppos = count; ret = count; — :1103-1104. DEVIATION: byte count not modelled.
    return 0;
}

/// `map_write`, kernel/user_namespace.c:932-1118, extent part: sets up the
/// zeroed `new_map` (:975), runs the body, and performs the `out:` cleanup
/// (:1107-1113) — which resets `map`'s heap arm only when the failed attempt
/// had migrated to it.
pub fn map_write(
    map: &mut UidGidMap,
    parent_map: &UidGidMap,
    lines: &[UidGidExtent],
    cap_ok: bool,
    permitted: bool,
) -> i32 {
    // memset(&new_map, 0, sizeof(struct uid_gid_map)); — :975
    let mut new_map: UidGidMap = UidGidMap::zeroed();

    let ret: i32 = map_write_body(map, parent_map, lines, cap_ok, permitted, &mut new_map);

    // out: — :1107-1113
    if ret < 0 && new_map.nr_extents > UID_GID_MAP_MAX_BASE_EXTENTS as u32 {
        // kfree(new_map.forward); kfree(new_map.reverse); — no-ops in the model
        map.forward_live = false; // map->forward = NULL;
        map.reverse_live = false; // map->reverse = NULL;
        map.nr_extents = 0;
    }
    return ret;
}
