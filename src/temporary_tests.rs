#![allow(dead_code)]
include!("temporary.rs.txt");
#[test]
fn dense_scratch_matches_ordered_map_through_promotion_deletes_and_reuse() {
    let mut seed = 17u64;
    for _ in 0..12 {
        let mut fast = OwnedMap::<u32, u64>::new();
        let mut oracle = std::collections::BTreeMap::new();
        for i in 0..2048 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = if i == 1024 {
                u32::MAX
            } else {
                ((seed >> 32) % 128) as u32
            };
            if seed & 3 == 0 {
                fast = fast.remove(&key);
                oracle.remove(&key);
            } else {
                fast = fast.set(key, seed);
                oracle.insert(key, seed);
            }
            assert_eq!(fast.len() as usize, oracle.len());
            assert_eq!(fast.get(&key), oracle.get(&key).copied());
            assert_eq!(fast.keys(), oracle.keys().copied().collect::<Vec<_>>());
            assert_eq!(fast.values(), oracle.values().copied().collect::<Vec<_>>());
        }
    }
}
#[test]
fn generation_wrap_is_cleared_and_live_maps_do_not_alias() {
    INK_MAP_POOL.with(|p| p.borrow_mut().clear());
    let mut first = OwnedMap::<u32, bool>::new().set(0, true).set(3, false);
    let InkMapStorage::Dense(s) = &mut first.0 else {
        panic!("not dense")
    };
    s.epoch = u64::MAX;
    for slot in &mut s.slots {
        if slot.value.is_some() {
            slot.epoch = u64::MAX;
        }
    }
    drop(first);
    let a = OwnedMap::<u32, bool>::new();
    assert_eq!(a.len(), 0);
    assert_eq!(a.get(&0), None);
    let b = OwnedMap::<u32, bool>::new().set(0, false);
    assert_eq!(a.get(&0), None);
    assert_eq!(b.get(&0), Some(false));
    assert_eq!(a, OwnedMap::new_sparse());
}
#[test]
fn large_scratch_is_reclaimed_and_non_scalar_values_use_sparse_owners() {
    INK_MAP_POOL.with(|p| p.borrow_mut().clear());
    let mut map = OwnedMap::<u32, u32>::new();
    for i in 0..4096 {
        map = map.set(i, i);
    }
    drop(map);
    INK_MAP_POOL.with(|p| assert!(p.borrow().is_empty()));
    let map = OwnedMap::<u64, String>::new().set(1, "owned".into());
    assert!(matches!(map.0, InkMapStorage::Sparse(_)));
    let signed = OwnedMap::<i32, u32>::new().set(0, 7).set(-1, 9);
    assert_eq!(signed.keys(), vec![-1, 0]);
}
