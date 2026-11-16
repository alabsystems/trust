//! Storage mechanism controls only. No saved data is proof authority.

use super::*;
use serde::Deserialize;
use serde::ser::SerializeSeq;
use std::path::PathBuf;

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let sequence = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "trust-vf5-publication-test-{}-{sequence}", std::process::id(),
        ));
        let mut create = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            create.mode(0o700);
        }
        create.create(&path).unwrap();
        Self(std::fs::canonicalize(path).unwrap())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Data {
    row_ids: Vec<String>,
    descriptions: Vec<String>,
}

fn data(body: usize) -> Data {
    Data {
        row_ids: vec![format!("{body}:0"), format!("{body}:1")],
        descriptions: vec!["unclaimed safety row".into(), "unrelated debt remains".into()],
    }
}

#[derive(Serialize)]
struct BorrowedData<'a> {
    row_ids: &'a [String],
    descriptions: &'a [String],
}

impl<'a> From<&'a Data> for BorrowedData<'a> {
    fn from(value: &'a Data) -> Self {
        Self { row_ids: &value.row_ids, descriptions: &value.descriptions }
    }
}

#[test]
fn borrowed_views_and_unsized_slices_decode_as_owned_data_after_borrows_end() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let (mut body, mut names) = {
        let original = data(7);
        let view = BorrowedData::from(&original);
        (
            spool.save_as::<_, Data>("body:7", 2, &view).unwrap(),
            spool.save_as::<[String], Vec<String>>("names:7", 2, &original.row_ids).unwrap(),
        )
        // Both original values and every borrow end before either decode.
    };
    assert_eq!(body.consume("body:7", 2).unwrap(), data(7));
    assert_eq!(names.consume("names:7", 2).unwrap(), data(7).row_ids);
    assert!(body.consume("body:7", 2).is_err());
}

#[test]
fn paired_borrowed_alternatives_return_independent_owned_records_only_after_both_seal() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let (mut body, mut names) = {
        let original = data(9);
        spool.save_pair_as::<_, Data, [String], Vec<String>>(
            "body:9", 2, &BorrowedData::from(&original), &original.row_ids,
        ).unwrap()
    };
    assert_eq!(body.rows, 2);
    assert_eq!(names.rows, 2, "both alternatives owe the original inventory");
    assert!(body.offset + body.length <= names.offset, "distinct sealed extents");
    assert_eq!(body.consume("body:9", 2).unwrap(), data(9));
    assert!(body.consume("body:9", 2).is_err(), "each handle has one attempt");
    assert_eq!(names.consume("body:9", 2).unwrap(), data(9).row_ids);
}

#[test]
fn typed_decode_refusal_keeps_the_live_inventory_and_cannot_be_retried() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    // The type parameter is a DATA decoding contract, not a schema proof.
    let mut saved = spool.save_as::<str, Data>("body:0", 2, "wrong DATA shape").unwrap();
    assert!(saved.consume("body:0", 2).is_err());
    assert_eq!(saved.rows, 2, "a decode refusal cannot erase owed rows");
    assert!(saved.consume("body:0", 2).is_err(), "no retry after decode refusal");
}

#[test]
fn saved_data_preserves_all_bodies_rows_and_single_consumption() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut saved = (0..257).map(|body| {
        let rows = data(body);
        // The original bulk values are dropped here, not retained by Saved.
        spool.save(&format!("body:{body}"), rows.row_ids.len(), &rows).unwrap()
    }).collect::<Vec<_>>();
    for (body, record) in saved.iter_mut().enumerate() {
        assert_eq!(record.consume(&format!("body:{body}"), 2).unwrap(), data(body));
        assert!(record.consume(&format!("body:{body}"), 2).is_err(), "one emission attempt");
    }
    let (_, store) = super::super::super::prepare_private_proof_artifact_store(&root.0).unwrap();
    assert_eq!(std::fs::read_dir(store).unwrap().count(), 0, "descriptor has no reopenable path");
}

#[test]
fn live_body_and_row_commitments_cannot_be_relabelled() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut wrong_body = spool.save("body:0", 2, &data(0)).unwrap();
    assert!(wrong_body.consume("body:1", 2).is_err());
    assert!(wrong_body.consume("body:0", 2).is_err(), "a refusal cannot be retried");
    let mut wrong_count = spool.save("body:0", 2, &data(0)).unwrap();
    assert!(wrong_count.consume("body:0", 1).is_err(), "inventory cannot shrink");
}

#[test]
fn same_length_mutation_and_record_reordering_refuse_before_decode() {
    for reorder in [false, true] {
        let root = Scratch::new();
        let spool = PublicationSpool::create(&root.0).unwrap();
        let mut first = spool.save("one", 1, &11u32).unwrap();
        let mut second = spool.save("two", 1, &22u32).unwrap();
        {
            let mut storage = spool.0.lock().unwrap();
            storage.file.seek(SeekFrom::Start(first.offset)).unwrap();
            storage.file.write_all(if reorder { b"22" } else { b"99" }).unwrap();
            if reorder {
                storage.file.seek(SeekFrom::Start(second.offset)).unwrap();
                storage.file.write_all(b"11").unwrap();
            }
        }
        let error = first.consume("one", 1).unwrap_err();
        assert!(error.to_string().contains("content changed"));
        if reorder {
            assert!(second.consume("two", 1).unwrap_err().to_string().contains("content changed"));
        } else {
            assert_eq!(second.consume("two", 1).unwrap(), 22, "other sealed record stays exact");
        }
    }
}

#[test]
fn mutation_before_first_seal_cannot_become_the_original_commitment() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    spool.0.lock().unwrap().before_seal = Some(Box::new(|file, offset| {
        file.seek(SeekFrom::Start(offset))?;
        file.write_all(b"22")
    }));
    let error = match spool.save("original", 1, &11u32) {
        Err(error) => error,
        Ok(_) => panic!("mutated first seal was admitted"),
    };
    assert!(error.to_string().contains("differs from emitted serialization"));
    assert!(spool.save("retry", 1, &11u32).is_err(), "first-seal failure stays poisoned");
}

#[test]
fn truncation_refuses_and_cannot_erase_the_live_inventory() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut saved = spool.save("body", 2, &data(0)).unwrap();
    spool.0.lock().unwrap().file.set_len(saved.offset + saved.length - 1).unwrap();
    assert!(saved.consume("body", 2).unwrap_err().to_string().contains("extent changed"));
    assert_eq!(saved.rows, 2, "refusal does not change owed row count");
}

struct InterruptedData;

impl Serialize for InterruptedData {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut sequence = serializer.serialize_seq(Some(2))?;
        sequence.serialize_element("partial data already written")?;
        Err(serde::ser::Error::custom("injected serializer failure"))
    }
}

#[test]
fn interrupted_write_poison_keeps_previous_record_and_forbids_retry() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut previous = spool.save("previous", 2, &data(0)).unwrap();
    assert!(spool.save("partial", 2, &InterruptedData).is_err());
    assert!(spool.save("later", 2, &data(1)).is_err(), "no retry-to-green after partial write");
    assert_eq!(previous.consume("previous", 2).unwrap(), data(0));
}

#[test]
fn partial_second_alternative_returns_no_pair_and_preserves_prior_sealed_records() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut previous = spool.save("previous", 2, &data(0)).unwrap();
    let previous_end = spool.0.lock().unwrap().end;
    let error = match spool.save_pair_as::<_, Data, _, Data>(
        "alternatives", 2, &BorrowedData::from(&data(1)), &InterruptedData,
    ) {
        Err(error) => error,
        Ok(_) => panic!("a partial second alternative must not return either handle"),
    };
    assert!(error.to_string().contains("injected serializer failure"));
    {
        let storage = spool.0.lock().unwrap();
        assert!(storage.write_failed, "partial second append permanently poisons writes");
        assert!(storage.end > previous_end, "the first alternative really sealed");
        assert!(storage.file.metadata().unwrap().len() > storage.end,
            "the second serializer actually wrote a partial payload");
    }
    assert!(spool.save("later", 2, &data(2)).is_err(), "no retry-to-green append");
    assert_eq!(previous.rows, 2, "failed pair cannot erase prior debt");
    assert_eq!(previous.consume("previous", 2).unwrap(), data(0));
    assert!(previous.consume("previous", 2).is_err());
}

#[test]
fn actual_io_admission_failure_creates_no_saved_handle() {
    let root = Scratch::new();
    let missing = root.0.join("missing-output-root");
    assert!(PublicationSpool::create(&missing).is_err());
    assert!(!missing.exists());
}
