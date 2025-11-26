use bumpalo_intern::dense::{DenseInternStore, InternTag, Interned, Keyed, OccupiedError};

use bumpalo::Bump;
use pretty_assertions::assert_eq;

#[derive(Clone, Copy)]
struct MyInterned<'a>(&'a str);

impl<'a> Keyed<'a> for MyInterned<'a> {
    fn intern_key(&self) -> &'a str {
        self.0
    }
}

impl<'a> Interned<'a> for MyInterned<'a> {
    type View<'b> = MyInterned<'b>;

    fn intern_from<'b>(arena: &'a Bump, value: Self::View<'b>) -> (&'a str, Self) {
        let key = arena.alloc_str(value.0);
        (key, MyInterned(key))
    }
}

#[test]
fn ensure_and_resolve() {
    let bump = Bump::new();
    let mut store: DenseInternStore<MyInterned<'_>> = DenseInternStore::new(&bump);

    let tag = store.ensure(MyInterned(&"foo".to_string()));
    let tag2 = store.ensure(MyInterned(&"bar".to_string()));

    assert_eq!(0, tag.as_index());
    assert_eq!(InternTag::new(1), tag2);

    assert_eq!("foo", store.get(tag).unwrap().0);
    assert_eq!("bar", store.get(tag2).unwrap().0);
}

#[test]
fn second_try_insert_fails() {
    let bump = Bump::new();
    let mut store: DenseInternStore<MyInterned<'_>> = DenseInternStore::new(&bump);

    store.try_insert(MyInterned("unregistered")).unwrap();

    let tag = store.try_insert(MyInterned("registered")).unwrap();

    assert_eq!(
        OccupiedError { existing: tag },
        store.try_insert(MyInterned("registered")).unwrap_err()
    );
}

#[test]
fn insert_alias() {
    let arena = Bump::new();
    let mut store: DenseInternStore<MyInterned<'_>> = DenseInternStore::new(&arena);

    let tag = store.try_insert(MyInterned("foo")).unwrap();
    store
        .insert_alias(MyInterned("foo_alias"), tag)
        .expect("foo_alias must be registered");

    assert_eq!(tag, store.ensure(MyInterned("foo")));
    assert_eq!(tag, store.ensure(MyInterned("foo_alias")));

    assert_eq!("foo", store.get(tag).unwrap().0);
}

#[test]
fn len_and_is_empty() {
    let arena = Bump::new();
    let mut store: DenseInternStore<MyInterned<'_>> = DenseInternStore::new(&arena);

    assert!(store.is_empty());
    assert_eq!(0, store.len());

    let foo = store.try_insert(MyInterned("foo")).unwrap();

    assert!(!store.is_empty());
    assert_eq!(1, store.len());

    store.try_insert(MyInterned("bar")).unwrap();

    assert!(!store.is_empty());
    assert_eq!(2, store.len());

    store.insert_alias(MyInterned("foo_alias"), foo).unwrap();

    assert!(!store.is_empty());
    assert_eq!(2, store.len());
}

#[test]
fn iter_returns_all() {
    let arena = Bump::new();
    let mut store: DenseInternStore<MyInterned<'_>> = DenseInternStore::new(&arena);

    let foo = store.try_insert(MyInterned("foo")).unwrap();
    store.insert_alias(MyInterned("foo_alias"), foo).unwrap();
    let bar = store.try_insert(MyInterned("bar")).unwrap();
    let baz = store.try_insert(MyInterned("baz")).unwrap();

    let got: Vec<InternTag<MyInterned<'_>>> = store.iter().collect();

    let want = vec![foo, bar, baz];
    assert_eq!(got, want);
}
