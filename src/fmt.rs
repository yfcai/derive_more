//! [`core::fmt::DebugTuple`] reimplementation with
//! [`DebugTuple::finish_non_exhaustive()`] method.

use ::core;
use core::fmt::{Debug, Formatter, Result, Write};
use core::fmt::{Binary, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex};
use core::prelude::v1::*;

use std::clone::Clone;
use std::marker::Copy;
use std::ops;
use std::ops::*;

/// Same as [`core::fmt::DebugTuple`], but with
/// [`DebugTuple::finish_non_exhaustive()`] method.
#[must_use = "must eventually call `finish()` or `finish_non_exhaustive()` on \
              Debug builders"]
pub struct DebugTuple<'a, 'b: 'a> {
    fmt: &'a mut Formatter<'b>,
    result: Result,
    fields: usize,
    empty_name: bool,
}

/// Creates a new [`DebugTuple`].
pub fn debug_tuple<'a, 'b>(
    fmt: &'a mut Formatter<'b>,
    name: &str,
) -> DebugTuple<'a, 'b> {
    let result = fmt.write_str(name);
    DebugTuple {
        fmt,
        result,
        fields: 0,
        empty_name: name.is_empty(),
    }
}

impl<'a, 'b: 'a> DebugTuple<'a, 'b> {
    /// Adds a new field to the generated tuple struct output.
    ///
    /// # Example
    ///
    /// ```rust
    /// use core::fmt;
    /// use derive_more::__private::debug_tuple;
    ///
    /// struct Foo(i32, String);
    ///
    /// impl fmt::Debug for Foo {
    ///     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         debug_tuple(fmt, "Foo")
    ///             .field(&self.0) // We add the first field.
    ///             .field(&self.1) // We add the second field.
    ///             .finish() // We're good to go!
    ///     }
    /// }
    ///
    /// assert_eq!(
    ///     format!("{:?}", Foo(10, "Hello World".to_string())),
    ///     "Foo(10, \"Hello World\")",
    /// );
    /// ```
    pub fn field(&mut self, value: &dyn Debug) -> &mut Self {
        self.result = self.result.and_then(|_| {
            if self.is_pretty() {
                if self.fields == 0 {
                    self.fmt.write_str("(\n")?;
                }

                let mut padded_formatter = Padded::new(self.fmt);
                padded_formatter.write_fmt(format_args!("{value:#?}"))?;
                padded_formatter.write_str(",\n")
            } else {
                let prefix = if self.fields == 0 { "(" } else { ", " };
                self.fmt.write_str(prefix)?;
                value.fmt(self.fmt)
            }
        });

        self.fields += 1;
        self
    }

    /// Finishes output and returns any error encountered.
    ///
    /// # Example
    ///
    /// ```
    /// use core::fmt;
    /// use derive_more::__private::debug_tuple;
    ///
    /// struct Foo(i32, String);
    ///
    /// impl fmt::Debug for Foo {
    ///     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         debug_tuple(fmt, "Foo")
    ///             .field(&self.0)
    ///             .field(&self.1)
    ///             .finish() // You need to call it to "finish" the
    ///                       // tuple formatting.
    ///     }
    /// }
    ///
    /// assert_eq!(
    ///     format!("{:?}", Foo(10, "Hello World".to_string())),
    ///     "Foo(10, \"Hello World\")",
    /// );
    /// ```
    pub fn finish(&mut self) -> Result {
        if self.fields > 0 {
            self.result = self.result.and_then(|_| {
                if self.fields == 1 && self.empty_name && !self.is_pretty() {
                    self.fmt.write_str(",")?;
                }
                self.fmt.write_str(")")
            });
        }
        self.result
    }

    /// Marks the struct as non-exhaustive, indicating to the reader that there are some other
    /// fields that are not shown in the debug representation, and finishes output, returning any
    /// error encountered.
    ///
    /// # Example
    ///
    /// ```rust
    /// use core::fmt;
    /// use derive_more::__private::debug_tuple;
    ///
    /// struct Bar(i32, f32);
    ///
    /// impl fmt::Debug for Bar {
    ///     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         debug_tuple(fmt, "Bar")
    ///             .field(&self.0)
    ///             .finish_non_exhaustive() // Show that some other field(s) exist.
    ///     }
    /// }
    ///
    /// assert_eq!(format!("{:?}", Bar(10, 1.0)), "Bar(10, ..)");
    /// ```
    pub fn finish_non_exhaustive(&mut self) -> Result {
        self.result = self.result.and_then(|_| {
            if self.fields > 0 {
                if self.is_pretty() {
                    let mut padded_formatter = Padded::new(self.fmt);
                    padded_formatter.write_str("..\n")?;
                    self.fmt.write_str(")")
                } else {
                    self.fmt.write_str(", ..)")
                }
            } else {
                self.fmt.write_str("(..)")
            }
        });
        self.result
    }

    fn is_pretty(&self) -> bool {
        self.fmt.alternate()
    }
}

/// Wrapper for a [`Formatter`] adding 4 spaces on newlines for inner pretty
/// printed [`Debug`] values.
struct Padded<'a, 'b> {
    formatter: &'a mut Formatter<'b>,
    on_newline: bool,
}

impl<'a, 'b> Padded<'a, 'b> {
    fn new(formatter: &'a mut Formatter<'b>) -> Self {
        Self {
            formatter,
            on_newline: true,
        }
    }
}

impl<'a, 'b> Write for Padded<'a, 'b> {
    fn write_str(&mut self, s: &str) -> Result {
        for s in s.split_inclusive('\n') {
            if self.on_newline {
                self.formatter.write_str("    ")?;
            }

            self.on_newline = s.ends_with('\n');
            self.formatter.write_str(s)?;
        }

        Ok(())
    }
}

/// TODO: document
#[derive(Copy, Clone)]
pub struct DisplayRef<'a, E>(pub &'a E);

// Forward all Display traits to the underlying type

macro_rules! forward_display_ref_trait {
    ($($imp:ident)*) => ($(
        impl<'a, E> $imp for DisplayRef<'a, E> where E: $imp {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result {
                $imp::fmt(self.0, f)
            }
        }
    )*)
}

forward_display_ref_trait! { Binary Debug Display LowerExp LowerHex Octal Pointer UpperExp UpperHex }

/// Enable Deref coercion
impl<'a, E> ops::Deref for DisplayRef<'a, E> {
    type Target = E;

    fn deref(&self) -> &'a E {
        self.0
    }
}

// Implement all the traits in std::ops to trigger coersion on operators
// Except instances containing "where" clauses

// trait Add

macro_rules! forward_display_ref_binop_for_base {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for DisplayRef<'a, $t> {
            type Output = <$t as $imp<$u>>::Output;

            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl<'a> $imp<DisplayRef<'a, $u>> for $t {
            type Output = <$t as $imp<$u>>::Output;

            fn $method(self, other: DisplayRef<'a, $u>) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl<'a> $imp<DisplayRef<'a, $u>> for DisplayRef<'a, $t> {
            type Output = <$t as $imp<$u>>::Output;

            fn $method(self, other: DisplayRef<'a, $u>) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}

macro_rules! forward_display_ref_binop_for_ref {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<&'a $u> for DisplayRef<'a, $t> {
            type Output = <$t as $imp<$u>>::Output;

            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }

        impl<'a> $imp<DisplayRef<'a, $u>> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            fn $method(self, other: DisplayRef<'a, $u>) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}

macro_rules! forward_display_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        forward_display_ref_binop_for_base! { impl $imp, $method for $t, $u }
        forward_display_ref_binop_for_ref! { impl $imp, $method for $t, $u }
    }
}

macro_rules! op_impl {
    ($imp:ident, $method:ident for $($t:ty)*) => ($(forward_display_ref_binop! { impl $imp, $method for $t, $t })*)
}

macro_rules! op_impl_fixint {
    ($imp:ident, $method:ident for $($t:ty)*) => ($(
        forward_display_ref_binop! { impl $imp, $method for std::num::Saturating<$t>, std::num::Saturating<$t> }
        forward_display_ref_binop! { impl $imp, $method for std::num::Wrapping<$t>, std::num::Wrapping<$t> }
    )*)
}

macro_rules! add_impl_duration {
    ($($t:ty)*) => ($(
        forward_display_ref_binop_for_base! { impl Add, add for $t, std::time::Duration }
    )*)
}

op_impl! { Add, add for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

op_impl_fixint! { Add, add for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }

add_impl_duration! { std::time::Duration std::time::Instant std::time::SystemTime }

// Impossible to forward for DisplayRef:
// impl<'a> Add for Cow<'a, str>
// impl<'a> Add<&'a str> for Cow<'a, str>

// impl<T, const N: usize> Add<&Simd<T, N>> for Simd<T, N> // unstable

// trait AddAssign // mutable

// trait AsyncFn // unstable
// trait AsyncFnMut // unstable
// trait AsyncFnOnce // unstable

// trait BitAnd

op_impl! { BitAnd, bitand for
    bool usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
    std::net::Ipv4Addr std::net::Ipv6Addr
}

op_impl_fixint! { BitAnd, bitand for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }

// trait BitAndAssign // mutable

// trait BitOr

op_impl! { BitOr, bitor for bool usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }

op_impl_fixint! { BitOr, bitor for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }

// trait BitOrAssign // mutable

// trait BitXor

op_impl! { BitXor, bitxor for bool usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }

op_impl_fixint! { BitXor, bitxor for usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }
