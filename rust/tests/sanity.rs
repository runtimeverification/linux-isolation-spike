//! Sanity checks on the model before extraction. These are NOT the proofs;
//! they are here to catch a model that is obviously wrong before we spend
//! Charon/Aeneas/Lean effort on it.
use uidmap::*;

fn ext(first: u32, lower_first: u32, count: u32) -> UidGidExtent {
    UidGidExtent { first, lower_first, count }
}

/// Field-wise compare. Deliberately not `#[derive(Debug)]` on the library
/// type: keeping the extracted crate free of derived trait impls we do not
/// need keeps the Charon/Aeneas surface smaller.
#[track_caller]
fn same(a: UidGidExtent, b: UidGidExtent, what: &str) {
    assert!(
        a.first == b.first && a.lower_first == b.lower_first && a.count == b.count,
        "{what}: ({}, {}, {}) != ({}, {}, {})",
        a.first, a.lower_first, a.count, b.first, b.lower_first, b.count
    );
}

#[test]
fn init_user_ns_is_near_identity() {
    let m = UidGidMap::init_user_ns_map();
    assert_eq!(map_id_down(&m, 0), 0);
    assert_eq!(map_id_down(&m, 1000), 1000);
    assert_eq!(map_id_up(&m, 1000), 1000);
    // count == 2^32 - 1, so the top id is NOT mapped. SPEC §1.2.2 / §7.10.
    assert_eq!(map_id_down(&m, 0xFFFF_FFFE), 0xFFFF_FFFE);
    assert_eq!(map_id_down(&m, 0xFFFF_FFFF), ID_SENTINEL);
}

#[test]
fn single_extent_roundtrip() {
    let mut m = UidGidMap::zeroed();
    assert_eq!(insert_extent(&mut m, &ext(0, 1000, 1)), 0);
    assert_eq!(map_id_down(&m, 0), 1000);
    assert_eq!(map_id_down(&m, 1), ID_SENTINEL);
    assert_eq!(map_id_up(&m, 1000), 0);
    assert_eq!(map_id_up(&m, 1001), ID_SENTINEL);
}

/// Build a map with `n` extents, `first`/`lower_first` already in ascending
/// order, so `forward`/`reverse` are sorted without needing sort_idmaps.
fn ascending_map(n: u32) -> UidGidMap {
    let mut m = UidGidMap::zeroed();
    let mut i = 0u32;
    while i < n {
        // upper blocks of 10 at 0,10,20,..; lower blocks of 10 at 100000,...
        assert_eq!(insert_extent(&mut m, &ext(i * 10, 100_000 + i * 10, 10)), 0);
        i += 1;
    }
    m
}

#[test]
fn migration_clobbers_the_base_arm() {
    // 5 extents: still entirely in the base arm, nothing clobbered.
    let m5 = ascending_map(5);
    assert_eq!(m5.nr_extents, 5);
    assert!(!m5.forward_live);
    same(m5.extent[0], ext(0, 100_000, 10), "base[0] intact at n=5");

    // The 6th insert migrates and the two pointer stores destroy
    // extent[0] and extent[1].first. extent[2..4] survive.
    let m6 = ascending_map(6);
    assert_eq!(m6.nr_extents, 6);
    assert!(m6.forward_live);
    assert!(!m6.reverse_live, "reverse is NULL until sort_idmaps runs");
    assert_eq!(m6.extent[0].first, CLOBBER_POISON);
    assert_eq!(m6.extent[0].lower_first, CLOBBER_POISON);
    assert_eq!(m6.extent[0].count, CLOBBER_POISON);
    assert_eq!(m6.extent[1].first, CLOBBER_POISON);
    assert_eq!(m6.extent[1].lower_first, 100_010, "not aliased");
    same(m6.extent[2], ext(20, 100_020, 10), "offset >= 16 survives");
    // the copies made it to the forward arm intact
    same(m6.forward[0], ext(0, 100_000, 10), "forward[0] copied");
    same(m6.forward[5], ext(50, 100_050, 10), "forward[5] inserted");
}

#[test]
fn base_and_bsearch_agree_on_ascending_maps() {
    // The AGREEMENT property (SPEC §4.4) smoke-tested: for maps that are
    // sorted by construction, walk every id in range and compare the <=5
    // linear-scan answer against the >5 binary-search answer on maps built
    // from the same extents.
    for n in 1..=5u32 {
        let small = ascending_map(n);
        // reference: brute-force the abstract map
        for id in 0..(n * 10 + 5) {
            let want = if id < n * 10 { 100_000 + id } else { ID_SENTINEL };
            assert_eq!(map_id_down(&small, id), want, "n={n} id={id}");
        }
    }
    for n in 6..=40u32 {
        let big = ascending_map(n);
        // reverse must be populated for the up direction; sort_idmaps has not
        // been written yet, so mirror what it does for an ascending map.
        let mut big = big;
        let mut i = 0usize;
        while i < n as usize {
            big.reverse[i] = big.forward[i];
            i += 1;
        }
        big.reverse_live = true;
        for id in 0..(n * 10 + 5) {
            let want = if id < n * 10 { 100_000 + id } else { ID_SENTINEL };
            assert_eq!(map_id_down(&big, id), want, "n={n} id={id}");
            let kid = 100_000 + id;
            let want_up = if id < n * 10 { id } else { ID_SENTINEL };
            assert_eq!(map_id_up(&big, kid), want_up, "up n={n} kid={kid}");
        }
    }
}

#[test]
fn no_stale_read_smoke() {
    // S5 non-interference, tested rather than proved: perturbing the base arm
    // of a map with nr_extents > 5 must not change any lookup.
    let mut a = ascending_map(9);
    let mut i = 0usize;
    while i < 9 { a.reverse[i] = a.forward[i]; i += 1; }
    a.reverse_live = true;

    let mut b = UidGidMap {
        extent: a.extent,
        forward: a.forward,
        reverse: a.reverse,
        forward_live: a.forward_live,
        reverse_live: a.reverse_live,
        nr_extents: a.nr_extents,
    };
    // scribble over the whole base arm
    let mut k = 0usize;
    while k < UID_GID_MAP_MAX_BASE_EXTENTS {
        b.extent[k] = ext(0x1111_1111, 0x2222_2222, 0x3333_3333);
        k += 1;
    }
    for id in 0..100u32 {
        assert_eq!(map_id_down(&a, id), map_id_down(&b, id), "id={id}");
        assert_eq!(map_id_up(&a, 100_000 + id), map_id_up(&b, 100_000 + id));
    }
}

#[test]
fn range_forms_require_whole_range_in_one_extent() {
    let m = ascending_map(3); // [0,10) [10,20) [20,30)
    // a range inside one extent maps
    assert_eq!(map_id_range_down(&m, 2, 5), 100_002);
    // a range spanning two adjacent extents does NOT (cmp_map_id :267-268)
    assert_eq!(map_id_range_down(&m, 8, 5), ID_SENTINEL);
    // exact fit
    assert_eq!(map_id_range_down(&m, 0, 10), 100_000);
    assert_eq!(map_id_range_down(&m, 0, 11), ID_SENTINEL);
}

// ---------------------------------------------------------------------
// Write path (step 4)
// ---------------------------------------------------------------------

fn parent_identity() -> UidGidMap { UidGidMap::init_user_ns_map() }

#[test]
fn write_single_extent_installs() {
    let parent = parent_identity();
    let mut m = UidGidMap::zeroed();
    let r = map_write(&mut m, &parent, &[ext(0, 1000, 1)], true, true);
    assert_eq!(r, 0);
    assert_eq!(m.nr_extents, 1);
    same(m.extent[0], ext(0, 1000, 1), "installed");
    assert_eq!(map_id_down(&m, 0), 1000);
    assert_eq!(map_id_up(&m, 1000), 0);
}

#[test]
fn write_rejects_second_write() {
    let parent = parent_identity();
    let mut m = UidGidMap::zeroed();
    assert_eq!(map_write(&mut m, &parent, &[ext(0, 1000, 1)], true, true), 0);
    assert_eq!(map_write(&mut m, &parent, &[ext(1, 1001, 1)], true, true), -EPERM);
    assert_eq!(m.nr_extents, 1, "untouched");
}

#[test]
fn write_rejects_bad_extents() {
    let parent = parent_identity();
    let mut m = UidGidMap::zeroed();
    // sentinel (:1024), count 0 / wrap (:1031, :1033), overlap upper, overlap lower
    for bad in [
        vec![ext(ID_SENTINEL, 0, 1)],
        vec![ext(0, ID_SENTINEL, 1)],
        vec![ext(0, 0, 0)],
        vec![ext(0xFFFF_FFF0, 0, 0x20)],
        vec![ext(0, 0xFFFF_FFF0, 0x20)],
        vec![ext(0, 1000, 10), ext(5, 2000, 10)],      // upper overlap
        vec![ext(0, 1000, 10), ext(100, 1005, 10)],    // lower overlap (pre-remap)
        vec![],                                        // nr_extents == 0 (:1053)
    ] {
        let mut m2 = UidGidMap::zeroed();
        assert_eq!(map_write(&mut m2, &parent, &bad, true, true), -EINVAL);
        assert_eq!(m2.nr_extents, 0);
    }
    // exactly 2^32-1 total is the largest accepted (SPEC §1.2.1)
    assert_eq!(map_write(&mut m, &parent, &[ext(0, 0, 0xFFFF_FFFF)], true, true), 0);
    let mut m3 = UidGidMap::zeroed();
    assert_eq!(map_write(&mut m3, &parent, &[ext(1, 1, 0xFFFF_FFFF)], true, true), -EINVAL);
}

#[test]
fn write_340_cap_is_exact() {
    let parent = parent_identity();
    let lines: Vec<UidGidExtent> = (0..341u32).map(|i| ext(i * 10, 100_000 + i * 10, 10)).collect();
    let mut m = UidGidMap::zeroed();
    assert_eq!(map_write(&mut m, &parent, &lines[..340], true, true), 0, "340 fit");
    assert_eq!(m.nr_extents, 340);
    let mut m2 = UidGidMap::zeroed();
    assert_eq!(map_write(&mut m2, &parent, &lines[..341], true, true), -EINVAL, "341st line fails");
    assert_eq!(m2.nr_extents, 0, "cleanup reset");
    assert!(!m2.forward_live && !m2.reverse_live);
}

#[test]
fn write_remaps_through_parent_and_sorts() {
    // parent: container-style map, three extents out of order
    let mut parent = UidGidMap::zeroed();
    assert_eq!(map_write(&mut parent, &parent_identity(),
        &[ext(0, 100_000, 65536), ext(65536, 300_000, 65536)], true, true), 0);
    // child: seven extents given in descending order, lower ids in the parent's space
    let lines: Vec<UidGidExtent> = (0..7u32).rev().map(|i| ext(i * 100, 1000 + i * 100, 100)).collect();
    let mut child = UidGidMap::zeroed();
    assert_eq!(map_write(&mut child, &parent, &lines, true, true), 0);
    assert_eq!(child.nr_extents, 7);
    assert!(child.forward_live && child.reverse_live);
    // forward sorted by first, reverse sorted by lower_first, both permutations
    for i in 1..7usize {
        assert!(child.forward[i - 1].first < child.forward[i].first, "forward sorted");
        assert!(child.reverse[i - 1].lower_first < child.reverse[i].lower_first, "reverse sorted");
    }
    // lower_first was REMAPPED: parent maps 1000 -> 101000
    same(child.forward[0], ext(0, 101_000, 100), "remapped through parent");
    // round trip through the >5 path
    for x in [0u32, 99, 100, 350, 699] {
        let k = map_id_down(&child, x);
        assert_eq!(k, 101_000 + x);
        assert_eq!(map_id_up(&child, k), x);
    }
    assert_eq!(map_id_down(&child, 700), ID_SENTINEL);
}

#[test]
fn write_rejects_unmappable_lower() {
    let mut parent = UidGidMap::zeroed();
    assert_eq!(map_write(&mut parent, &parent_identity(), &[ext(0, 100_000, 10)], true, true), 0);
    let mut child = UidGidMap::zeroed();
    // lower range [5,15) straddles the parent's single extent [0,10): unmappable (:1079)
    assert_eq!(map_write(&mut child, &parent, &[ext(0, 5, 10)], true, true), -EPERM);
    assert_eq!(child.nr_extents, 0);
}

#[test]
fn write_oracle_gates() {
    let parent = parent_identity();
    let mut m = UidGidMap::zeroed();
    assert_eq!(map_write(&mut m, &parent, &[ext(0, 1000, 1)], false, true), -EPERM);
    assert_eq!(map_write(&mut m, &parent, &[ext(0, 1000, 1)], true, false), -EPERM);
    assert_eq!(m.nr_extents, 0);
}
