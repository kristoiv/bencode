# bencode
Simple bencode encoder/decoder written in rust


## Examples:

### Encode
```rust
fn example_encode_from_vec_type() {
    assert_eq!(
        vec![100_u8, 100].bencode_encode().unwrap(),
        "li100ei100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![100_u16, 100].bencode_encode().unwrap(),
        "li100ei100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![100_u32, 100].bencode_encode().unwrap(),
        "li100ei100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![1337_u64, 1337].bencode_encode().unwrap(),
        "li1337ei1337ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![100_i8, -100].bencode_encode().unwrap(),
        "li100ei-100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![100_i16, -100].bencode_encode().unwrap(),
        "li100ei-100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![100_i32, -100].bencode_encode().unwrap(),
        "li100ei-100ee".as_bytes().to_vec(),
    );
    assert_eq!(
        vec![1337_i64, -1337].bencode_encode().unwrap(),
        "li1337ei-1337ee".as_bytes().to_vec(),
    );
}

fn example_encode_from_string() {
    assert_eq!(
        "Some val".to_owned().bencode_encode().unwrap(),
        "8:Some val".as_bytes().to_vec(),
    );
}

fn example_encode_from_hashmap() {
    let mut expected_inner = HashMap::new();
    expected_inner.insert("Some inner".to_owned(), 1337_u32);

    let mut expected_outer = HashMap::new();
    expected_outer.insert("Some outer".to_owned(), expected_inner);

    assert_eq!(
        expected_outer.bencode_encode().unwrap(),
        "d10:Some outerd10:Some inneri1337eee".as_bytes().to_vec(),
    );
}
```

### Decode
```rust
fn example_decode_to_vec_type() {
    assert_eq!(
        Vec::<u8>::from_bencode(&"li100ei100ee".as_bytes().to_vec()).unwrap(),
        vec![100, 100]
    );
    assert_eq!(
        Vec::<u16>::from_bencode(&"li100ei100ee".as_bytes().to_vec()).unwrap(),
        vec![100, 100]
    );
    assert_eq!(
        Vec::<u32>::from_bencode(&"li100ei100ee".as_bytes().to_vec()).unwrap(),
        vec![100, 100]
    );
    assert_eq!(
        Vec::<u64>::from_bencode(&"li1337ei1337ee".as_bytes().to_vec()).unwrap(),
        vec![1337, 1337]
    );
    assert_eq!(
        Vec::<i8>::from_bencode(&"li100ei-100ee".as_bytes().to_vec()).unwrap(),
        vec![100, -100]
    );
    assert_eq!(
        Vec::<i16>::from_bencode(&"li100ei-100ee".as_bytes().to_vec()).unwrap(),
        vec![100, -100]
    );
    assert_eq!(
        Vec::<i32>::from_bencode(&"li100ei-100ee".as_bytes().to_vec()).unwrap(),
        vec![100, -100]
    );
    assert_eq!(
        Vec::<i64>::from_bencode(&"li1337ei-1337ee".as_bytes().to_vec()).unwrap(),
        vec![1337, -1337]
    );
}

/// Will panic due to multiple data types in bencode-encoded list
fn example_will_fail_to_decode_to_vec_if_multiple_types() {
    Vec::<u8>::from_bencode(&"li100e8:Some vale".as_bytes().to_vec()).unwrap();
}

fn example_decode_to_string() {
    assert_eq!(
        String::from_bencode(&"8:Some val".as_bytes().to_vec()).unwrap(),
        "Some val".to_owned()
    );
}

fn example_decode_to_hashmap() {
    let mut expected_inner = HashMap::new();
    expected_inner.insert("Some inner".to_owned(), 1337_u32);

    let mut expected_outer = HashMap::new();
    expected_outer.insert("Some outer".to_owned(), expected_inner);

    assert_eq!(
        HashMap::from_bencode(&"d10:Some outerd10:Some inneri1337eee".as_bytes().to_vec())
            .unwrap(),
        expected_outer,
    );
}
```
