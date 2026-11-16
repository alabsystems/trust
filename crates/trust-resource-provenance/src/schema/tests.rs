// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

fn row() -> Record {
    Record {
        pid: 42,
        birth: 1,
        host: "here".into(),
        boot: "now".into(),
        digest: "a".repeat(64),
        image: FileId { dev: 1, ino: 2 },
        directory: FileId { dev: 1, ino: 3 },
        socket_hex: hex(b"/a/\xff\n"),
        socket: FileId { dev: 1, ino: 4 },
    }
}
#[test]
fn exact_book_roundtrip_preserves_lossless_paths_and_refuses_duplicate_lifetimes() {
    let book = Book { version: 1, instances: vec![row()] };
    assert_eq!(Book::decode(&book.encode().unwrap()).unwrap(), book);
    assert_eq!(unhex(&book.instances[0].socket_hex).unwrap(), b"/a/\xff\n");
    let duplicate = Book { version: 1, instances: vec![row(), row()] };
    assert!(duplicate.encode().is_err());
    assert!(unhex("AB").is_err());
}
#[test]
fn duplicate_nested_or_unknown_fields_and_oversized_books_are_refused() {
    for bytes in [
        b"{\"version\":1,\"version\":1,\"instances\":[]}".as_slice(),
        b"{\"version\":1,\"instances\":[],\"other\":true}",
        b"{\"version\":2,\"instances\":[]}",
        b"{\"version\":1.0,\"instances\":[]}",
    ] {
        assert!(Book::decode(bytes).is_err());
    }
    let text =
        String::from_utf8(Book { version: 1, instances: vec![row()] }.encode().unwrap()).unwrap();
    assert!(Book::decode(text.replace("\"dev\":1", "\"dev\":1,\"dev\":1").as_bytes()).is_err());
    assert!(Book::decode(&vec![b' '; MAX_JSON + 1]).is_err());
}
