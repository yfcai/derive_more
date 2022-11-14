// These links overwrite the ones in `README.md`
// to become proper intra-doc links in Rust docs.
//! [`From`]: crate::From
//! [`Into`]: crate::Into
//! [`FromStr`]: crate::FromStr
//! [`TryInto`]: crate::TryInto
//! [`IntoIterator`]: crate::IntoIterator
//! [`AsRef`]: crate::AsRef
//!
//! [`Display`-like]: crate::Display
//!
//! [`Error`]: crate::Error
//!
//! [`Index`]: crate::Index
//! [`Deref`]: crate::Deref
//! [`Not`-like]: crate::Not
//! [`Add`-like]: crate::Add
//! [`Mul`-like]: crate::Mul
//! [`Sum`-like]: crate::Sum
//! [`IndexMut`]: crate::IndexMut
//! [`DerefMut`]: crate::DerefMut
//! [`AddAssign`-like]: crate::AddAssign
//! [`MulAssign`-like]: crate::MulAssign
//!
//! [`Constructor`]: crate::Constructor
//! [`IsVariant`]: crate::IsVariant
//! [`Unwrap`]: crate::Unwrap
#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![deny(rustdoc::broken_intra_doc_links, rustdoc::private_intra_doc_links)]
#![forbid(non_ascii_idents, unsafe_code)]

#[doc(inline)]
pub use derive_more_impl::*;
