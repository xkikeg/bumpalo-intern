//! Defines intern utility providing direct `&str` wrapped interning.
//!
//! Here is the basic usage of the [`DirectInternStore`].
//!
//! ```
//! use bumpalo_intern::direct::{InternedStr, FromInterned, DirectInternStore};
//!
//! // You should have a simple &str wrapper.
//! #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
//! struct MyInterned<'a>(InternedStr<'a>);
//!
//! // And the type must implement FromInterned.
//! impl<'arena> FromInterned<'arena> for MyInterned<'arena> {
//!     fn from_interned(v: InternedStr<'arena>) -> Self {
//!        Self(v)
//!    }
//!
//!    fn as_interned(&self) -> InternedStr<'arena> {
//!        self.0
//!    }
//! }
//!
//! let arena = bumpalo::Bump::new();
//! let mut interner = DirectInternStore::new(&arena);
//!
//! let foo: MyInterned<'_> = interner.ensure(&"foo".to_string());
//! let foo2 = interner.ensure(&"foo".to_string());
//! let bar = interner.ensure(&"bar".to_string());
//!
//! assert_eq!(foo, foo2);
//! assert_ne!(foo, bar);
//! assert_eq!(foo.as_interned().as_str(), "foo");
//! assert_eq!(bar.as_interned().as_str(), "bar");
//! ```
//!

use std::{collections::HashMap, fmt::Debug, hash::Hash, iter::FusedIterator, marker::PhantomData};

use bumpalo::Bump;

/// Wrapped `&str` interned by [`DirectInternStore`].
#[derive(Eq, Clone, Copy)]
pub struct InternedStr<'arena>(&'arena str);

impl<'arena> InternedStr<'arena> {
    pub fn as_str(&self) -> &'arena str {
        self.0
    }
}

impl Debug for InternedStr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InternedStr")
            .field(&std::ptr::from_ref(self.0))
            .field(&self.0)
            .finish()
    }
}

/// InternedStr equality is computed on the pointer, as it's interned and must have the same pointer
/// as long as the content is the same.
impl PartialEq for InternedStr<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

/// Hash is based on the pointer, as it's interned.
impl Hash for InternedStr<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state)
    }
}

/// Trait that the actual Interned object must implements.
pub trait FromInterned<'arena>: Copy {
    fn from_interned(v: InternedStr<'arena>) -> Self;

    fn as_interned(&self) -> InternedStr<'arena>;
}

/// Stored value in [`DirectInternStore`].
#[derive(Debug, PartialEq, Eq)]
pub enum StoredValue<'arena, T> {
    Canonical(T),
    Alias { alias: &'arena str, canonical: T },
}

impl<T: Copy> StoredValue<'_, T> {
    fn as_canonical(&self) -> T {
        match self {
            StoredValue::Canonical(x) => *x,
            StoredValue::Alias { canonical, .. } => *canonical,
        }
    }
}

/// Error returned when try_insert* method fails.
#[derive(Debug, PartialEq, Eq)]
pub struct OccupiedError<'arena, T> {
    pub existing: StoredValue<'arena, T>,
}

/// Manage interned `&str` in the arena allocator.
/// This can also handles alias.
/// Semantics of alias:
/// * Alias behaves as the same as canonical.
///   One can call [`ensure`] for the alias, and the corresponding canonical value is returned.
/// * It's prohibited to change account type once registered.
///   Caller can't register alias which is already registered as canonical,
///   or vice versa.
pub struct DirectInternStore<'arena, T> {
    // Contains None for canonical, Some for alias.
    records: HashMap<&'arena str, Option<InternedStr<'arena>>>,
    allocator: &'arena Bump,
    phantom: PhantomData<T>,
}

impl<'arena, T> DirectInternStore<'arena, T> {
    /// Creates a new instance.
    pub fn new(allocator: &'arena Bump) -> Self {
        Self {
            records: HashMap::new(),
            allocator,
            phantom: PhantomData,
        }
    }
}

impl<'arena, T: FromInterned<'arena>> DirectInternStore<'arena, T> {
    /// Interns the given `str` and returns the shared instance.
    /// If `value` is registered as alias, it'll resolve to the canonical one.
    /// If `value` is not registered yet, register the value as canonical value.
    pub fn ensure(&mut self, value: &str) -> T {
        match self.resolve(value) {
            Some(found) => found,
            None => self.insert_canonical_impl(value),
        }
    }

    /// Inserts given `value` as always canonical.
    /// Fails if the given value is already registered.
    pub fn try_insert(&mut self, value: &str) -> Result<T, OccupiedError<'arena, T>> {
        match self.get(value) {
            None => Ok(self.insert_canonical_impl(value)),
            Some(existing) => Err(OccupiedError { existing }),
        }
    }

    /// Inserts given `value` as always alias of `canonical`.
    /// Returns error if given `value` is already registered.
    pub fn insert_alias(
        &mut self,
        value: &str,
        canonical: T,
    ) -> Result<(), OccupiedError<'arena, T>> {
        match self.get(value) {
            Some(existing) => Err(OccupiedError { existing }),
            None => {
                self.insert_alias_impl(value, canonical.as_interned());
                Ok(())
            }
        }
    }

    /// Returns the specified value if found, otherwise None.
    pub fn resolve(&self, value: &str) -> Option<T> {
        let x = self.get(value)?;
        Some(x.as_canonical())
    }

    /// Returns the Iterator for all elements.
    pub fn iter<'container>(&'container self) -> Iter<'arena, 'container, T>
    where
        'arena: 'container,
    {
        Iter {
            base: self.records.iter(),
            phantom: PhantomData,
        }
    }

    #[inline]
    fn get(&self, value: &str) -> Option<StoredValue<'arena, T>> {
        let v = match self.records.get_key_value(value)? {
            (canonical, None) => StoredValue::Canonical(Self::as_type(canonical)),
            (alias, Some(canonical)) => StoredValue::Alias {
                alias,
                canonical: T::from_interned(*canonical),
            },
        };
        Some(v)
    }

    #[inline]
    fn insert_canonical_impl(&mut self, value: &str) -> T {
        let copied: &'arena str = self.allocator.alloc_str(value);
        let ret = self.records.insert(copied, None);
        debug_assert!(
            ret.is_none(),
            "insert must be called on non-existing key, but already found: {:#?}",
            ret
        );
        Self::as_type(copied)
    }

    #[inline]
    fn insert_alias_impl(&mut self, value: &str, canonical: InternedStr<'arena>) {
        let copied: &'arena str = self.allocator.alloc_str(value);
        let ret = self.records.insert(copied, Some(canonical));
        debug_assert!(
            ret.is_none(),
            "insert must be called on non-existing key, but already found: {:#?}",
            ret
        );
    }

    #[inline]
    fn as_type(s: &'arena str) -> T {
        <T as FromInterned>::from_interned(InternedStr(s))
    }
}

/// an iterator over the items of a `Interner`.
/// Compared to the underlying HashSet iterator,
/// this struct ensures the `T` type.
pub struct Iter<'arena, 'container, T> {
    base: std::collections::hash_map::Iter<'container, &'arena str, Option<InternedStr<'arena>>>,
    phantom: PhantomData<T>,
}

fn to_interned<'arena, T: FromInterned<'arena>>(x: &'arena str) -> T {
    <T as FromInterned>::from_interned(InternedStr(x))
}

impl<'arena, T> Iterator for Iter<'arena, '_, T>
where
    T: FromInterned<'arena>,
{
    type Item = StoredValue<'arena, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.base.next().map(|(key, value)| match value {
            None => StoredValue::Canonical(to_interned(key)),
            Some(value) => StoredValue::Alias {
                alias: key,
                canonical: <T as FromInterned>::from_interned(*value),
            },
        })
    }
}

impl<'arena, T> FusedIterator for Iter<'arena, '_, T> where T: FromInterned<'arena> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interned_str_eq_uses_ptr() {
        let bump = Bump::new();
        // Use non 'static str.
        let foo1 = InternedStr(bump.alloc_str(&String::from("foo")));
        let foo2 = InternedStr(bump.alloc_str(&String::from("foo")));
        assert_ne!(foo1, foo2);
        let foo_copy = foo1;
        assert_eq!(foo1, foo_copy);
    }
}
