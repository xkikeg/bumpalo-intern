//! Provides several methods to intern string or string-similar objects.
//!
//! This library currently provides two type of string intern mechanism.
//! One is [`direct::DirectInternStore`], which wraps the Bumpalo allocated `&str` directly.
//! This allows user to have just a `&str` wrapper which is quite convenient to use.
//!
//! The other is [`dense::DenseInternStore`], which gives the densely packed usize wrapper as a tag
//! (0, 1, 2, ...). This is a bit inconvenient to use as you need to query `DenseInternStore`
//! what was the original object. Instead, this gives two benefits;
//!
//! 1. Tag is always densely packed usize, so you can use Vec<> instead of HashMap<> to have interned object keyed map.
//! 2. Tag is always usize even if you store much larger object. This is optimal for performance if you want to embed
//!    interned object in many places.
//!
//! See https://github.com/xkikeg/okane for real world examples.

/// Provides [`dense::DenseInternStore`].
pub mod dense;

/// Provides [`direct::DirectInternStore`].
pub mod direct;
