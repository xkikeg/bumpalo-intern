//! Defines intern utility providing dense packed interning.
//!
//! Here is the basic usage of the [`DenseInternStore`].
//!
//! ```
//! use bumpalo_intern::dense::{Interned,Keyed,InternTag,DenseInternStore};
//!
//! // You should have a type (either struct or enum) with a unique str key.
//! #[derive(Debug, PartialEq, Eq, Clone, Copy)]
//! struct MyInterned<'a>(&'a str);
//!
//! impl<'a> Keyed<'a> for MyInterned<'a> {
//!     fn intern_key(&self) -> &'a str {
//!         self.0
//!     }
//! }
//!
//! impl<'a> Interned<'a> for MyInterned<'a> {
//!     type View<'b> = MyInterned<'b>;
//!
//!     fn intern_from<'b>(arena: &'a bumpalo::Bump, value: Self::View<'b>) -> (&'a str, Self) {
//!         let key = arena.alloc_str(value.0);
//!         (key, MyInterned(key))
//!     }
//! }
//!
//! let arena = bumpalo::Bump::new();
//! let mut interner = DenseInternStore::new(&arena);
//!
//! let tag: InternTag<MyInterned<'_>> = interner.ensure(MyInterned(&"foo".to_string()));
//!
//! assert!(matches!(interner.get(tag), Some(MyInterned("foo"))));
//! ```

use std::collections::HashMap;
use std::fmt::Display;
use std::iter::FusedIterator;
use std::marker::PhantomData;

use bumpalo::Bump;
use derive_where::derive_where;

/// Error on InternStore operations.
#[derive_where(Debug, PartialEq, Eq)]
pub struct OccupiedError<T> {
    pub existing: InternTag<T>,
}

impl<T> Display for OccupiedError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "given alias already exists with index {}",
            self.existing.as_index(),
        )
    }
}

impl<T> std::error::Error for OccupiedError<T> {}

/// Interned object tag, which is actually the number densely counts up.
/// You need [`DenseInternStore`] to resolve the actual value.
#[derive_where(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct InternTag<T> {
    id: usize,
    phantom: PhantomData<T>,
}

impl<T> InternTag<T> {
    /// Constructs InternTag out of the plain index.
    pub fn new(id: usize) -> Self {
        Self {
            id,
            phantom: PhantomData,
        }
    }

    /// Returns the underlying usize ID.
    pub fn as_index(&self) -> usize {
        self.id
    }
}

/// Value associated with the unique string key.
pub trait Keyed<'a> {
    /// Key of the object, used for interning.
    fn intern_key(&self) -> &'a str;
}

/// Object retrieved from [`DenseInternStore`], which has unique string key
/// so that we can intern its instance.
pub trait Interned<'a>: Keyed<'a> {
    /// Original value type, usually the same as `Self` itself.
    type View<'b>: Keyed<'b>;

    /// Interns the `self` with the given `arena`.
    fn intern_from<'b>(arena: &'a Bump, value: Self::View<'b>) -> (&'a str, Self);
}

/// Stores interned value.
pub struct DenseInternStore<'arena, T> {
    items: Vec<T>,
    refs: HashMap<&'arena str, usize>,
    arena: &'arena Bump,
}

impl<'arena, T> DenseInternStore<'arena, T> {
    /// Creates a new instance.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            items: Vec::new(),
            refs: HashMap::new(),
            arena,
        }
    }

    /// Returns `true` if there are no interned objects stored.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns the total number of registered interned objects.
    /// Note it doesn't contain aliases.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns the corresponding instance for the tag,
    /// or `None` if it doesn't exists.
    pub fn get(&self, tag: InternTag<T>) -> Option<T>
    where
        T: Copy,
    {
        self.items.get(tag.id).copied()
    }

    /// Interns given value and returns the corresponding tag.
    /// Note if `value` is registered as alias, it'll return the canonical one.
    /// If `value` is not registered yet, register the value as canonical value.
    pub fn ensure<'a>(&mut self, value: T::View<'a>) -> InternTag<T>
    where
        T: Interned<'arena>,
    {
        match self.resolve(value.intern_key()) {
            Some(found) => found,
            None => self.insert_impl(value),
        }
    }

    /// Interns the given value and returns the tag, only when there's no interned object yet.
    /// Returns `None` if insert failed because of existing element.
    pub fn try_insert<'a>(&mut self, value: T::View<'a>) -> Result<InternTag<T>, OccupiedError<T>>
    where
        T: Interned<'arena>,
    {
        if let Some(existing) = self.resolve(value.intern_key()) {
            return Err(OccupiedError { existing });
        }
        Ok(self.insert_impl(value))
    }

    /// Inserts the given value with interning it.
    /// This method doesn't check the duplication, so caller must ensure there's no dups.
    fn insert_impl<'a>(&mut self, value: T::View<'a>) -> InternTag<T>
    where
        T: Interned<'arena>,
    {
        let id = self.items.len();
        let (key, interned) = T::intern_from(self.arena, value);
        self.items.push(interned);
        self.refs.insert(key, id);
        InternTag {
            id,
            phantom: PhantomData,
        }
    }

    /// Inserts given `value` as always alias of `canonical`.
    /// Returns error if given `value` is already registered.
    pub fn insert_alias<'a>(
        &mut self,
        value: T::View<'a>,
        canonical: InternTag<T>,
    ) -> Result<(), OccupiedError<T>>
    where
        T: Interned<'arena>,
    {
        match self.resolve(value.intern_key()) {
            Some(existing) => Err(OccupiedError { existing }),
            None => {
                let (interned_alias, _) = T::intern_from(self.arena, value);
                self.refs.insert(interned_alias, canonical.id);
                Ok(())
            }
        }
    }

    /// Returns the specified value key if found, otherwise None.
    #[inline]
    pub fn resolve(&self, value: &str) -> Option<InternTag<T>> {
        let i = self.refs.get(value)?;
        Some(InternTag {
            id: *i,
            phantom: PhantomData,
        })
    }

    /// Returns the Iterator for all elements.
    pub fn iter<'container>(&'container self) -> Iter<T>
    where
        'arena: 'container,
    {
        Iter {
            base: 0..self.items.len(),
            phantom: PhantomData,
        }
    }
}

/// An iterator over the items of a [`DenseInternStore`].
/// Compared to the underlying HashSet iterator,
/// this struct ensures the `T` type.
pub struct Iter<T> {
    base: std::ops::Range<usize>,
    phantom: PhantomData<T>,
}

impl<T> Iterator for Iter<T> {
    type Item = InternTag<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.base.next().map(|id| InternTag {
            id,
            phantom: PhantomData,
        })
    }
}

impl<T> FusedIterator for Iter<T> {}
