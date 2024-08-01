use crate::*;
use std::mem::MaybeUninit;

#[test]
pub fn test() {
    reserve_buffer_capacity(4);
    let iter = (0u8..10).map(|x| {
        if x == 3 {
            let iter = (0u8..10).map(|x| {
                if x == 3 {
                    uninit(|arr: &mut MaybeUninit<[u8; 10]>| {
                        arr.write([0; 10]);
                    });
                }
                Box::new(x)
            });
            buffer(iter, |slice| {
                assert_eq!(slice, &Vec::from_iter((0..10).map(Box::new)))
            })
        }
        x
    });
    buffer(iter, |slice| assert_eq!(slice, &Vec::from_iter(0..10)))
}

#[test]
pub fn test2() {
    reserve_buffer_capacity(8);
    buffer((0..2).map(Box::new), |slice| {
        uninit(|arr: &mut MaybeUninit<[u8; 10]>| {
            arr.write([0; 10]);
        });
        assert_eq!(slice, &Vec::from_iter((0..2).map(Box::new)))
    })
}

#[test]
pub fn test_zst() {
    #[repr(align(8))]
    struct Aligned;

    reserve_buffer_capacity(4);
    buffer(0..3u8, |slice| {
        uninit_slice(10, |arr: &mut [MaybeUninit<Aligned>]| {
            assert_eq!(arr.len(), 10);
        });
        assert_eq!(slice, &Vec::from_iter(0..3))
    })
}

#[test]
pub fn test_into_slice_full() {
    reserve_buffer_capacity(8);
    with_stack_vec(|mut vec| {
        vec.extend((0..2).map(Box::new));
        let (slice, mut vec2) = vec.into_slice_full();
        vec2.extend_from_slice(&[0u8; 10]);
        assert_eq!(&*slice, &Vec::from_iter((0..2).map(Box::new)))
    })
}
