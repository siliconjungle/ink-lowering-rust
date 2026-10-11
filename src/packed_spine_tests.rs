#![allow(non_snake_case, dead_code)]
include!("packed_spine.rs.txt");
#[derive(Debug)]
struct Tag;

fn words(values: &[u64]) -> PackedSpine<Tag, u64> {
    values
        .iter()
        .rev()
        .fold(PackedSpine::C0, |xs, &x| xs.prepend(x))
}

#[test]
fn chunks_promote_exactly_and_shared_suffix_updates_preserve_originals() {
    for length in [0, 1, 63, 64, 65, 255, 256, 257, 513, 4097] {
        let values = (0..length)
            .map(|i| match i % 11 {
                0 => u64::MAX,
                1 => u32::MAX as u64,
                2 => u32::MAX as u64 + 1,
                _ => i as u64,
            })
            .collect::<Vec<_>>();
        let list = words(&values);
        assert_eq!(list.len(), values.len());
        assert_eq!(list.cells().collect::<Vec<_>>(), values);
        let mut suffix = list.clone();
        for i in 0..length {
            let (head, tail) = suffix.view().unwrap();
            assert_eq!(head, values[i]);
            let changed = tail.clone().prepend(u64::MAX - i as u64);
            assert_eq!(
                changed.cells().collect::<Vec<_>>(),
                std::iter::once(u64::MAX - i as u64)
                    .chain(values[i + 1..].iter().copied())
                    .collect::<Vec<_>>()
            );
            assert_eq!(list.cells().collect::<Vec<_>>(), values);
            suffix = tail;
        }
        assert!(suffix.is_empty());
        assert!(suffix.view().is_none());
    }
    let narrow = words(&[7, u32::MAX as u64]);
    assert!(matches!(
        narrow.chunk.as_ref().unwrap().block,
        WordBlock::Narrow(_)
    ));
    let shared = narrow.clone();
    assert!(std::sync::Arc::ptr_eq(
        narrow.chunk.as_ref().unwrap(),
        shared.chunk.as_ref().unwrap()
    ));
    let owners = std::sync::Arc::strong_count(narrow.chunk.as_ref().unwrap());
    let (_, borrowed_suffix) = narrow.as_view().view().unwrap();
    assert_eq!(
        std::sync::Arc::strong_count(narrow.chunk.as_ref().unwrap()),
        owners
    );
    assert_eq!(
        borrowed_suffix.cells().collect::<Vec<_>>(),
        [u32::MAX as u64]
    );
    let retained_suffix = borrowed_suffix.to_owned();
    assert_eq!(
        std::sync::Arc::strong_count(narrow.chunk.as_ref().unwrap()),
        owners + 1
    );
    drop(retained_suffix);
    assert_eq!(
        std::sync::Arc::strong_count(narrow.chunk.as_ref().unwrap()),
        owners
    );
    let promoted = shared.prepend(u32::MAX as u64 + 1);
    assert!(matches!(
        promoted.chunk.as_ref().unwrap().block,
        WordBlock::Wide(_)
    ));
    assert!(matches!(
        narrow.chunk.as_ref().unwrap().block,
        WordBlock::Narrow(_)
    ));
    assert_eq!(
        promoted.cells().collect::<Vec<_>>(),
        [u32::MAX as u64 + 1, 7, u32::MAX as u64]
    );
    // Different physical widths have the same exact logical equality.
    let widened = narrow.clone().prepend(u64::MAX).view().unwrap().1;
    assert_eq!(narrow, widened);
}

#[test]
fn boolean_suffixes_clear_hidden_bits_and_cross_word_boundaries() {
    for length in [0, 1, 63, 64, 65, 127, 128, 129, 4097] {
        let expected = (0..length).map(|i| i % 3 != 0).collect::<Vec<_>>();
        let list: PackedSpine<Tag, bool> = expected
            .iter()
            .rev()
            .fold(PackedSpine::C0, |xs, &x| xs.prepend(x));
        let mut suffix = list.clone();
        for i in 0..length {
            let (head, tail) = suffix.view().unwrap();
            assert_eq!(head, expected[i]);
            let changed = tail.clone().prepend(false);
            assert_eq!(
                changed.cells().collect::<Vec<_>>(),
                std::iter::once(false)
                    .chain(expected[i + 1..].iter().copied())
                    .collect::<Vec<_>>()
            );
            suffix = tail;
        }
        assert_eq!(list.cells().collect::<Vec<_>>(), expected);
    }
}

#[test]
fn reclaiming_deep_unique_and_shared_spines_is_iterative() {
    let worker = std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut list: PackedSpine<Tag, bool> = PackedSpine::C0;
            for i in 0..1_000_000 {
                list = list.prepend(i % 2 == 0);
            }
            let weak = std::sync::Arc::downgrade(list.chunk.as_ref().unwrap());
            let retained = list.clone();
            drop(list);
            assert!(weak.upgrade().is_some());
            drop(retained);
            assert!(weak.upgrade().is_none());
        })
        .unwrap();
    worker.join().unwrap();
}

#[test]
fn generic_cells_keep_record_identity_and_release_hidden_prefixes() {
    #[derive(Debug, PartialEq, Eq)]
    struct Record { words: Vec<u64> }
    use std::sync::Arc;
    let cells = (0..1025).map(|i| Arc::new(Record { words: vec![i, u64::MAX-i] })).collect::<Vec<_>>();
    let list: PackedSpine<Tag, Arc<Record>> = cells.iter().rev().fold(PackedSpine::C0, |xs,x| xs.prepend(x.clone()));
    assert!(list.cells().zip(&cells).all(|(a,b)| Arc::ptr_eq(&a,b)));
    let mut suffix = list.as_view();
    for _ in 0..100 { suffix = suffix.view().unwrap().1; }
    let added = Arc::new(Record { words: vec![17] });
    let changed = suffix.to_owned().prepend(added.clone());
    assert!(Arc::ptr_eq(&changed.cells().next().unwrap(), &added));
    assert_eq!(changed.cells().skip(1).map(|r|r.words.clone()).collect::<Vec<_>>(), cells[100..].iter().map(|r|r.words.clone()).collect::<Vec<_>>());
    assert_eq!(list.len(), 1025);
    drop(changed); drop(list);
    assert!(cells.iter().all(|r|Arc::strong_count(r)==1));
}
