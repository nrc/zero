// Copyright 2016 Nicholas Cameron.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functions for reading binary data into Rust data structures. All functions
//! are zero-allocation.
//!
//! There are functions for reading a single value, an array of values, a single
//! null-terminated utf8 string (which should also work with ascii strings), and
//! an array of null-terminated strings terminated by another null byte.
//!
//! Functions preserve the lifetime of the underlying data. These functions are
//! memory safe, although this is in part based on the assumption that the
//! client only implements the unsafe trait `Pod` where safe to do so.
//!
//! Functions assert that the provided data is large enough. The string
//! functions check that strings are valid utf8. There is no checking that the
//! the privided input will produce a valid object (for example, an enum has a
//! valid discriminant). The user must assert this by implementing the trait
//! `Pod`.
//!
//! There are also unsafe versions of most functions which do not require the
//! return type to implement `Pod` and which do no checking.

#![no_std]

use core::mem;
use core::slice::from_raw_parts;
use core::str::{from_utf8, from_utf8_unchecked};

/// Reads a single `T` from `input`.
///
/// `input` must be at least as large as `T`.
pub fn read<'a, T: Pod>(input: &'a [u8]) -> &'a T {
    assert!(mem::size_of::<T>() <= input.len());

    unsafe {
        read_unsafe(input)
    }    
}

/// Read an array of `T`s from input.
///
/// `input` must contain an exact number of `T`s, there must be no extra bytes
/// after the last `T`. `T` may not be zero-sized.
pub fn read_array<'a, T: Pod>(input: &'a [u8]) -> &'a [T] {
    let t_size = mem::size_of::<T>();
    assert!(t_size > 0, "Can't read arrays of zero-sized types");
    assert!(input.len() % t_size == 0);

    unsafe {
        read_array_unsafe(input)
    }
}

/// Read a string from `input`. The string must be a null-termianted utf8 string.
/// Note that an ascii C string fulfils this requirement.
pub fn read_str<'a>(input: &'a [u8]) -> &'a str {
    from_utf8(read_str_bytes(input)).expect("Non-utf8 string")
}

/// Returns an iterator which will return a sequence of strings from `input`.
/// Each string must be a null-terminated utf8 string. The sequence of strings
/// is terminated either by a second null byte, or the end of input.
pub fn read_strs_to_null<'a>(input: &'a [u8]) -> StrReaderIterator<'a> {
    StrReaderIterator {
        data: input,
    }
}

/// Implementing this trait means that the concrete type is plain old data (POD).
/// Precisely, by implementing `Pod` the programmer asserts that it is safe to
/// read the type from binary slices provided to `read`, etc.
///
/// Some guidelines for when `Pod` may be implemented (note that whether `Pod`
/// should be implemented or not is a function of both the type and the input
/// data. I.e., just because a type is `Pod` in one context does not mean it
/// should be in another):
/// * primitive numeric types (`u8`, `i64`, `f32`, etc.) are fine,
/// * bools are fine, if the provided data ensures they may have only the values
///   `0` or `1` (note that this is a stricter requirement that C),
/// * structs containing only `Pod` data are fine,
/// * structs must be `repr(C)` or `repr(packed)`, if the former, the supplied
///   data must have the correct alignment,
/// * enums must have valid discriminants in the supplied data, this is probably
///   only feasible if they have a specified representation,
/// * there must not be invalid enum variants in the data,
/// * any kind of pointer is probably a bad idea. Theoretically one could make
///   raw pointers work.
pub unsafe trait Pod: Sized {}

unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}

/// Reads a `T` from `input` with no checks.
pub unsafe fn read_unsafe<'a, T: Sized>(input: &'a [u8]) -> &'a T {
    mem::transmute(input as *const [u8] as *const u8 as *const T)
}

/// Reads an array of `T`s from `input` with no checks.
pub unsafe fn read_array_unsafe<'a, T: Sized>(input: &'a [u8]) -> &'a [T] {
    let ptr = input.as_ptr() as *const T;
    from_raw_parts(ptr, input.len() / mem::size_of::<T>())
}

/// Reads a null-terminated string from `input` with no checks.
pub unsafe fn read_str_unsafe<'a>(input: &'a [u8]) -> &'a str {
    from_utf8_unchecked(read_str_bytes(input))
}

/// Iterates over `self.data`, yielding strings (null-terminated in `self.data`).
/// See `read_strs_to_null`.
#[derive(Clone, Debug)]
pub struct StrReaderIterator<'a> {
    data: &'a [u8]
}

impl<'a> Iterator for StrReaderIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if self.data.len() == 0 || self.data[0] == 0 {
            return None;
        }

        let result = read_str(self.data);
        self.data = &self.data[result.len() + 1..];
        Some(result)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // Potentially no strings here at all. Maximum number is if the whole
        // data is filled with one char-long strings alternating with null bytes.
        (0, Some(self.data.len() / 2))
    }
}

// Helper function for read_str and read_str_unsafe.
// Finds the sub-slice of input which contains a string by searching for a null
// byte.
fn read_str_bytes<'a>(input: &'a [u8]) -> &'a [u8] {
    for (i, byte) in input.iter().enumerate() {
        if *byte == 0 {
            return &input[..i];
        }
    }

    panic!("No null byte in input");
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Copy, Clone, PartialEq, Eq)]
    struct Zero;

    #[derive(Copy, Clone, PartialEq, Eq)]
    #[repr(packed)]
    struct Foo {
        a: u8,
    }

    #[derive(Copy, Clone, PartialEq, Eq)]
    #[repr(packed)]
    struct Bar {
        a: u32,
        b: u64,
        c: i8,
    }

    unsafe impl Pod for Zero {}
    unsafe impl Pod for Foo {}
    unsafe impl Pod for Bar {}

    // read

    #[test]
    fn test_read() {
        let a = &[];
        assert!(read::<Zero>(a) == &Zero);

        let a = &[42];
        assert!(read::<Foo>(a) == &Foo { a: 42 });

        let a = &[42, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0, -2i8 as u8];
        assert!(read::<Bar>(a) == &Bar { a: 42, b: 0xf000425b_a262ff03, c: -2 });
    }

    #[test]
    #[should_panic]
    fn test_too_small() {
        let a = &[];
        read::<Foo>(a);
    }

    #[test]
    #[should_panic]
    fn test_too_small2() {
        let a = &[42, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0];
        read::<Bar>(a);
    }

    // read_array

    #[test]
    fn test_read_array() {
        let a = &[42];
        assert!(read_array::<Foo>(a) == &[Foo { a: 42 }]);
        let a = &[42, 43, 44, 45];
        assert!(read_array::<Foo>(a) == &[Foo { a: 42 }, Foo { a: 43 }, Foo { a: 44 }, Foo { a: 45 }]);

        let a = &[42, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0, -2i8 as u8];
        assert!(read_array::<Bar>(a) == &[Bar { a: 42, b: 0xf000425b_a262ff03, c: -2 }]);
        let a = &[42, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0, -2i8 as u8,
                  43, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0, -2i8 as u8,
                  44, 0, 0, 0, 0x03, 0xff, 0x62, 0xa2, 0x5b, 0x42, 0x00, 0xf0, -2i8 as u8];
        assert!(read_array::<Bar>(a) == &[Bar { a: 42, b: 0xf000425b_a262ff03, c: -2 },
                                          Bar { a: 43, b: 0xf000425b_a262ff03, c: -2 },
                                          Bar { a: 44, b: 0xf000425b_a262ff03, c: -2 }]);
    }

    #[test]
    #[should_panic]
    fn test_array_zero_sized() {
        let a = &[0];
        read_array::<Zero>(a);
    }

    // read_str

    #[test]
    fn test_good_strs() {
        let a = &[0];
        assert_eq!(read_str(a), "");
        let a = &[0x61, 0];
        assert_eq!(read_str(a), "a");
        let a = &[0x61, 0x41, 0x7a, 0, 0x61];
        assert_eq!(read_str(a), "aAz");
    }

    #[test]
    #[should_panic]
    fn test_no_null() {
        let a = &[];
        read_str(a);
    }

    #[test]
    #[should_panic]
    fn test_no_null2() {
        let a = &[0x61, 0x41, 0x7a];
        read_str(a);
    }

    #[test]
    #[should_panic]
    fn test_not_unicode() {
        // TODO
        panic!();
    }

    // read_strs_to_null

    #[test]
    fn test_good_strs_to_null() {
        let a = &[0];
        assert_eq!(read_strs_to_null(a).count(), 0);
        let a = &[0, 0];
        assert_eq!(read_strs_to_null(a).count(), 0);
        let a = &[0, 1];
        assert_eq!(read_strs_to_null(a).count(), 0);

        let a = &[0x61, 0];
        let mut iter = read_strs_to_null(a);
        assert_eq!(iter.next(), Some("a"));
        assert_eq!(iter.next(), None);

        let a = &[0x61, 0, 0x61, 0x41, 0x7a, 0, 0x61, 0];
        let mut iter = read_strs_to_null(a);
        assert_eq!(iter.next(), Some("a"));
        assert_eq!(iter.next(), Some("aAz"));
        assert_eq!(iter.next(), Some("a"));
        assert_eq!(iter.next(), None);

        let a = &[0x61, 0, 0x61, 0x41, 0x7a, 0, 0x61, 0, 0, 0x61];
        let mut iter = read_strs_to_null(a);
        assert_eq!(iter.next(), Some("a"));
        assert_eq!(iter.next(), Some("aAz"));
        assert_eq!(iter.next(), Some("a"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[should_panic]
    fn test_no_null_to_null() {
        let a = &[0x61];
        let mut iter = read_strs_to_null(a);
        iter.next();
    }
}
