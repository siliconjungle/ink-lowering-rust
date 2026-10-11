#![allow(dead_code)]
include!("identity_memo.rs.txt");
#[test]
fn weak_identity_arguments_eviction_and_reentrancy_are_exact() {
    use std::{cell::Cell, sync::Arc};
    INK_IDENTITY_MEMO.with(|cache| cache.borrow_mut().clear());
    let input = Arc::new(vec![1u64, 2]);
    let calls = Cell::new(0);
    let compute = || {
        calls.set(calls.get() + 1);
        3u64
    };
    assert_eq!(ink_identity_memo(&input, "sum", [0; 4], compute), 3);
    assert_eq!(ink_identity_memo(&input, "sum", [0; 4], compute), 3);
    assert_eq!(calls.get(), 1);
    let equal = Arc::new(vec![1u64, 2]);
    assert_eq!(ink_identity_memo(&equal, "sum", [0; 4], compute), 3);
    assert_eq!(calls.get(), 2);
    assert_eq!(ink_identity_memo(&input, "sum", [1, 0, 0, 0], || 4u64), 4);
    assert!(ink_identity_memo(&input, "flag", [0; 4], || true));
    let parent = Arc::new(8u64);
    let child = Arc::new(9u64);
    assert_eq!(
        ink_identity_memo(&parent, "recursive", [0; 4], || ink_identity_memo(
            &child,
            "recursive",
            [0; 4],
            || 9u64
        ) + 8),
        17
    );
    let weak = Arc::downgrade(&input);
    drop(input);
    assert!(weak.upgrade().is_none());
    ink_identity_memo(&equal, "sum", [0; 4], compute);
    assert!(
        INK_IDENTITY_MEMO.with(|cache| cache.borrow().iter().all(|e| e.input.strong_count() > 0))
    );
    for i in 0..100u64 {
        ink_identity_memo(&equal, "many", [i, 0, 0, 0], || i);
    }
    assert_eq!(INK_IDENTITY_MEMO.with(|cache| cache.borrow().len()), 64);
    assert_eq!(
        ink_identity_memo::<_, u64>(&equal, "many", [99, 0, 0, 0], || panic!("miss")),
        99u64
    );
}
