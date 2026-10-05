//! Physical arena backing checks, without Ash layout or lifetime admission.

use ash_foreign_adapter::arena::{Arena, LayoutTag, PayloadLayout};

#[test]
fn real_bounded_backing_publishes_encoded_bytes_and_reports_physical_metadata() {
    let mut arena = Arena::new(24, 2).unwrap();
    let layout = PayloadLayout::new(LayoutTag::new(7), 8, 8).unwrap();
    let key = arena
        .allocate(layout, 0, |bytes| {
            bytes.copy_from_slice(&42_i64.to_le_bytes());
            Ok::<_, ()>(())
        })
        .unwrap();
    assert_eq!(arena.read(key, layout.tag()).unwrap(), 42_i64.to_le_bytes());
    let usage = arena.usage();
    assert_eq!(usage.used_payload_bytes, 8);
    assert_eq!(usage.payload_capacity, 24);
    assert_eq!(usage.object_count, 1);
    assert_eq!(usage.object_capacity, 2);
    let physical = arena.physical_usage();
    assert_eq!(physical.payload_allocation_bytes, 24);
    assert_eq!(
        physical.object_table_bytes,
        2 * physical.object_record_bytes
    );
    assert!(physical.object_record_bytes >= 3 * 8);
    assert_eq!(physical.owner_inline_bytes, size_of::<Arena>());
}

use ash_foreign_adapter::arena::{
    AccessError, AllocationError, AllocationFailure, AllocationKey, ArenaInitError,
};

fn publish(
    arena: &mut Arena,
    layout: PayloadLayout,
    requested_alignment: usize,
    value: u8,
) -> AllocationKey {
    arena
        .allocate(layout, requested_alignment, |bytes| {
            bytes.fill(value);
            Ok::<_, ()>(())
        })
        .unwrap()
}

#[test]
fn alignment_padding_counts_and_exact_payload_capacity_refuses_before_initialization() {
    let mut arena = Arena::new(72, 3).unwrap();
    let byte = PayloadLayout::new(LayoutTag::new(1), 1, 1).unwrap();
    let integer = PayloadLayout::new(LayoutTag::new(2), 8, 8).unwrap();
    let first = publish(&mut arena, byte, 0, 19);
    let second = publish(&mut arena, integer, 64, 42);
    assert_eq!(arena.usage().used_payload_bytes, 72);
    assert_eq!(
        arena.read(second, integer.tag()).unwrap().as_ptr().addr() % 64,
        0
    );
    assert_eq!(arena.read(first, byte.tag()).unwrap(), [19]);
    let before = arena.usage();
    let mut called = false;
    assert_eq!(
        arena.allocate(byte, 0, |_| {
            called = true;
            Ok::<_, ()>(())
        }),
        Err(AllocationFailure::Refused(AllocationError::OutOfPayload))
    );
    assert!(!called);
    assert_eq!(arena.usage(), before);
}

#[test]
fn zero_payload_publishes_distinct_zero_sized_objects_up_to_the_exact_record_limit() {
    let mut arena = Arena::new(0, 3).unwrap();
    let unit = PayloadLayout::new(LayoutTag::new(0), 0, 1).unwrap();
    let first = publish(&mut arena, unit, 0, 0);
    let second = publish(&mut arena, unit, 64, 0);
    let third = publish(&mut arena, unit, 0, 0);
    assert_ne!(first, second);
    assert_ne!(second, third);
    assert_eq!(size_of::<AllocationKey>(), 2 * size_of::<u64>());
    assert!(arena.read(second, unit.tag()).unwrap().is_empty());
    assert_eq!(arena.usage().used_payload_bytes, 0);
    assert_eq!(arena.usage().object_count, 3);
    assert_eq!(
        arena.allocate(unit, 0, |_| Ok::<_, ()>(())),
        Err(AllocationFailure::Refused(AllocationError::OutOfObjects))
    );
    let mut empty = Arena::new(0, 0).unwrap();
    assert_eq!(
        empty.allocate(unit, 0, |_| Ok::<_, ()>(())),
        Err(AllocationFailure::Refused(AllocationError::OutOfObjects))
    );
    assert_eq!(empty.physical_usage().payload_allocation_bytes, 0);
    assert_eq!(empty.physical_usage().object_table_bytes, 0);
}

#[test]
fn all_admitted_alignments_are_real_and_invalid_alignments_leave_usage_unchanged() {
    for alignment in [1, 2, 4, 8, 16, 32, 64] {
        let mut arena = Arena::new(128, 2).unwrap();
        let layout = PayloadLayout::new(LayoutTag::new(3), 1, alignment).unwrap();
        publish(&mut arena, layout, 0, 1);
        let key = publish(&mut arena, layout, alignment, 2);
        assert_eq!(
            arena.read(key, layout.tag()).unwrap().as_ptr().addr() % alignment,
            0
        );
        assert_eq!(arena.usage().used_payload_bytes, alignment + 1);
    }
    for alignment in [0, 3, 65, usize::MAX] {
        assert_eq!(
            PayloadLayout::new(LayoutTag::new(3), 1, alignment),
            Err(AllocationError::InvalidAlignment)
        );
    }
    let mut arena = Arena::new(128, 3).unwrap();
    let layout = PayloadLayout::new(LayoutTag::new(3), 8, 8).unwrap();
    for alignment in [1, 4, 3, 128, usize::MAX] {
        let before = arena.usage();
        let mut called = false;
        assert_eq!(
            arena.allocate(layout, alignment, |_| {
                called = true;
                Ok::<_, ()>(())
            }),
            Err(AllocationFailure::Refused(
                AllocationError::InvalidAlignment
            ))
        );
        assert!(!called);
        assert_eq!(arena.usage(), before);
    }
}

#[test]
fn partial_initializer_failure_rolls_back_and_retry_does_not_reveal_failed_bytes() {
    let mut arena = Arena::new(24, 3).unwrap();
    let old_layout = PayloadLayout::new(LayoutTag::new(4), 8, 8).unwrap();
    let old = publish(&mut arena, old_layout, 0, 23);
    let layout = PayloadLayout::new(LayoutTag::new(5), 8, 8).unwrap();
    let before = arena.usage();
    assert_eq!(
        arena.allocate(layout, 0, |bytes| {
            bytes[..4].copy_from_slice(b"fail");
            Err("conversion")
        }),
        Err(AllocationFailure::Initialization("conversion"))
    );
    assert_eq!(arena.usage(), before);
    assert_eq!(arena.read(old, old_layout.tag()).unwrap(), [23; 8]);
    let unpublished = AllocationKey::from_ids(old.owner_id(), old.object_id() + 1).unwrap();
    assert_eq!(
        arena.read(unpublished, layout.tag()),
        Err(AccessError::UnknownObject)
    );
    let retry = arena
        .allocate(layout, 0, |bytes| {
            bytes[7] = 55;
            Ok::<_, ()>(())
        })
        .unwrap();
    assert_eq!(
        arena.read(retry, layout.tag()).unwrap(),
        [0, 0, 0, 0, 0, 0, 0, 55]
    );
    assert_eq!(arena.usage().object_count, 2);
}

#[test]
fn initializer_panic_drops_partial_temporary_state_and_preserves_published_objects() {
    use std::{cell::Cell, rc::Rc};
    struct Temporary(Rc<Cell<usize>>);
    impl Drop for Temporary {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let mut arena = Arena::new(24, 3).unwrap();
    let layout = PayloadLayout::new(LayoutTag::new(6), 8, 8).unwrap();
    let old = publish(&mut arena, layout, 0, 42);
    let drops = Rc::new(Cell::new(0));
    let before = arena.usage();
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = arena.allocate(layout, 0, |bytes| -> Result<(), ()> {
            let _temporary = Temporary(Rc::clone(&drops));
            bytes[..3].copy_from_slice(b"bad");
            panic!("test initializer panic")
        });
    }));
    assert!(panicked.is_err());
    assert_eq!(drops.get(), 1);
    assert_eq!(arena.usage(), before);
    assert_eq!(arena.read(old, layout.tag()).unwrap(), [42; 8]);
    let retry = arena.allocate(layout, 0, |_| Ok::<_, ()>(())).unwrap();
    assert_eq!(arena.read(retry, layout.tag()).unwrap(), [0; 8]);
}

#[test]
fn candidates_are_non_owning_and_owner_object_and_layout_checks_are_independent() {
    assert!(AllocationKey::from_ids(0, 1).is_none());
    assert!(AllocationKey::from_ids(1, 0).is_none());
    let layout = PayloadLayout::new(LayoutTag::new(7), 4, 4).unwrap();
    let mut arena = Arena::new(16, 2).unwrap();
    let key = publish(&mut arena, layout, 0, 42);
    let copied = key;
    let other = Arena::new(16, 2).unwrap();
    assert_eq!(
        other.read(copied, layout.tag()),
        Err(AccessError::ForeignOwner)
    );
    let missing = AllocationKey::from_ids(key.owner_id(), 2).unwrap();
    assert_eq!(
        arena.read(missing, layout.tag()),
        Err(AccessError::UnknownObject)
    );
    assert_eq!(
        arena.read(key, LayoutTag::new(8)),
        Err(AccessError::LayoutMismatch)
    );
    drop(arena);
    let next = Arena::new(16, 2).unwrap();
    assert_eq!(
        next.read(copied, layout.tag()),
        Err(AccessError::ForeignOwner)
    );
}

#[test]
fn earlier_payloads_and_keys_remain_stable_after_more_publications_and_owner_moves() {
    let mut arena = Arena::new(256, 32).unwrap();
    let layout = PayloadLayout::new(LayoutTag::new(9), 8, 8).unwrap();
    let first = publish(&mut arena, layout, 0, 42);
    let address = arena.read(first, layout.tag()).unwrap().as_ptr().addr();
    for byte in 0..31 {
        publish(&mut arena, layout, 0, byte);
    }
    let arena = std::hint::black_box(arena);
    assert_eq!(arena.read(first, layout.tag()).unwrap(), [42; 8]);
    assert_eq!(
        arena.read(first, layout.tag()).unwrap().as_ptr().addr(),
        address
    );
    assert_eq!(arena.usage().used_payload_bytes, 256);
    assert_eq!(arena.usage().object_count, 32);
}

#[test]
fn pointer_and_metadata_products_reject_before_any_payload_initializer() {
    assert_eq!(
        Arena::new(usize::MAX, 0).unwrap_err(),
        ArenaInitError::InvalidConfiguration
    );
    assert_eq!(
        Arena::new(1, usize::MAX).unwrap_err(),
        ArenaInitError::InvalidConfiguration
    );
    assert_eq!(
        PayloadLayout::new(LayoutTag::new(10), usize::MAX, 1),
        Err(AllocationError::InvalidPayload)
    );
    let mut arena = Arena::new(8, 1).unwrap();
    let huge = PayloadLayout::new(LayoutTag::new(10), isize::MAX as usize, 1).unwrap();
    let mut called = false;
    assert_eq!(
        arena.allocate(huge, 0, |_| {
            called = true;
            Ok::<_, ()>(())
        }),
        Err(AllocationFailure::Refused(AllocationError::OutOfPayload))
    );
    assert!(!called);
    assert_eq!(arena.usage().used_payload_bytes, 0);
    assert_eq!(arena.usage().object_count, 0);
}
