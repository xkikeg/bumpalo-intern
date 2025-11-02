use bumpalo::Bump;
use bumpalo_intern::direct::{
    DirectInternStore, FromInterned, InternedStr, OccupiedError, StoredValue,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct TestInterned<'arena>(InternedStr<'arena>);

impl<'arena> FromInterned<'arena> for TestInterned<'arena> {
    fn from_interned(v: InternedStr<'arena>) -> Self {
        Self(v)
    }

    fn as_interned(&self) -> InternedStr<'arena> {
        self.0
    }
}

#[test]
fn ensure_gives_distinct_strings() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);

    let foo: TestInterned = intern_store.ensure("foo");
    let bar: TestInterned = intern_store.ensure("bar");

    assert_ne!(foo, bar);
    assert_eq!(foo.0.as_str(), "foo");
    assert_eq!(bar.0.as_str(), "bar");
}

#[test]
fn ensure_gives_same_obj() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);

    let foo1: TestInterned = intern_store.ensure("foo");
    let foo2: TestInterned = intern_store.ensure("foo");

    assert_eq!(foo1, foo2);
    assert_eq!(foo2.0.as_str(), "foo");
}

#[test]
fn try_insert_succeeds_on_unregistered_value() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);

    let foo: TestInterned = intern_store.try_insert("foo").unwrap();
    let bar: TestInterned = intern_store.try_insert("bar").unwrap();

    assert_eq!(foo.as_interned().as_str(), "foo");
    assert_ne!(foo, bar);
    assert_eq!(bar.as_interned().as_str(), "bar");
}

#[test]
fn try_insert_fails_when_already_canonical() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let foo: TestInterned = intern_store.try_insert("foo").unwrap();

    let err = intern_store.try_insert("foo").unwrap_err();
    assert_eq!(
        OccupiedError {
            existing: StoredValue::Canonical(foo)
        },
        err
    );
}

#[test]
fn try_insert_fails_when_already_alias() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let foo: TestInterned = intern_store.try_insert("foo").unwrap();
    intern_store.insert_alias("bar", foo).unwrap();
    assert_eq!(
        OccupiedError {
            existing: StoredValue::Alias {
                alias: "bar",
                canonical: foo
            }
        },
        intern_store.try_insert("bar").unwrap_err()
    );
}

#[test]
fn insert_alias_succeeds_on_unregistered_value() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let foo: TestInterned = intern_store.try_insert("foo").unwrap();
    intern_store.insert_alias("bar", foo).unwrap();

    let bar = intern_store.ensure("bar");

    assert_eq!(foo, bar);
}

#[test]
fn insert_alias_fails_on_already_alias_value() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let foo: TestInterned = intern_store.try_insert("foo").unwrap();
    intern_store.insert_alias("bar", foo).unwrap();

    assert_eq!(
        OccupiedError {
            existing: StoredValue::Alias {
                alias: "bar",
                canonical: foo
            }
        },
        intern_store.insert_alias("bar", foo).unwrap_err()
    );
}

#[test]
fn insert_alias_fails_on_canonical() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let foo: TestInterned = intern_store.try_insert("foo").unwrap();
    let bar: TestInterned = intern_store.try_insert("bar").unwrap();

    assert_eq!(
        OccupiedError {
            existing: StoredValue::Canonical(bar)
        },
        intern_store.insert_alias("bar", foo).unwrap_err()
    );
}

#[test]
fn intern_store_iter_all_elements() {
    let bump = Bump::new();
    let mut intern_store = DirectInternStore::new(&bump);
    let v1: TestInterned = intern_store.ensure("abc");
    let v2: TestInterned = intern_store.ensure("def");
    intern_store.ensure("def");
    intern_store
        .insert_alias("efg", v1)
        .expect("efg must be an alias of abc");
    let v3: TestInterned = intern_store.ensure("ghi");
    let want = [
        StoredValue::Canonical(v1),
        StoredValue::Alias {
            alias: "efg",
            canonical: v1,
        },
        StoredValue::Canonical(v2),
        StoredValue::Canonical(v3),
    ];

    let mut got: Vec<StoredValue<TestInterned>> = intern_store.iter().collect();
    got.sort_by_key(|x| match x {
        StoredValue::Canonical(x) => (x.as_interned().as_str(), ""),
        StoredValue::Alias { alias, canonical } => (canonical.as_interned().as_str(), *alias),
    });

    assert_eq!(want.as_slice(), got.as_slice());
}
