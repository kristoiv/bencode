use super::*;
use anyhow::{bail, Result};

/// Encode a Value (an intermediate format) into a bencoded vector of bytes
pub fn encode(val: &Value) -> Result<Vec<u8>> {
    match val {
        Value::Bytes(byts) => {
            let char_encoded_digits = byts
                .len()
                .to_string()
                .chars()
                .map(|it| it as u8)
                .collect::<Vec<u8>>();

            Ok(vec![char_encoded_digits, vec![':' as u8], byts.to_owned()]
                .iter()
                .flatten()
                .map(|it| *it)
                .collect::<Vec<u8>>())
        }

        Value::Number(num) => {
            let char_encoded_digits = num.to_string().chars().map(|it| it as u8).collect();
            Ok(vec![vec!['i' as u8], char_encoded_digits, vec!['e' as u8]]
                .iter()
                .flatten()
                .map(|it| *it)
                .collect::<Vec<u8>>())
        }

        Value::List(values) => {
            let mut results = vec![vec!['l' as u8]];
            for v in values {
                let res = encode(v)?;
                results.push(res);
            }
            results.push(vec!['e' as u8]);
            Ok(results.iter().flatten().map(|it| *it).collect::<Vec<u8>>())
        }

        Value::Dict(entries) => {
            let mut entries = entries.clone();
            entries.sort_by(|(a, _), (b, _)| a.cmp(b));

            let mut prev_key: Option<Vec<u8>> = None;
            let mut results = vec![vec!['d' as u8]];
            for (key, val) in entries {
                let res_key = encode(&Value::Bytes(key))?;

                // Verify that we don't have duplicate keys
                if let Some(prev) = &prev_key {
                    if prev.eq(&res_key) {
                        bail!("unexpected duplicate key (not allowed): {:?}", res_key);
                    }
                }
                prev_key = Some(res_key.clone());

                results.push(res_key);
                let res_value = encode(&val)?;
                results.push(res_value);
            }
            results.push(vec!['e' as u8]);
            Ok(results.iter().flatten().map(|it| *it).collect::<Vec<u8>>())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_bytestr() {
        // Encode bytes
        let val = "Some val";
        let res =
            encode(&Value::Bytes(val.as_bytes().to_vec())).expect("encoding to be successful");
        let res_str = String::from_utf8(res).expect("parsable as utf-8");
        assert_eq!(res_str.as_str(), "8:Some val");
    }

    #[test]
    fn test_encode_number() {
        // Encode number
        {
            let num = 1337;
            let res = encode(&Value::Number(num)).expect("encoding to be successful");
            let res_str = String::from_utf8(res).expect("parsable as utf-8");
            assert_eq!(res_str.as_str(), "i1337e");
        }
        {
            let num = -1337;
            let res = encode(&Value::Number(num)).expect("encoding to be successful");
            let res_str = String::from_utf8(res).expect("parsable as utf-8");
            assert_eq!(res_str.as_str(), "i-1337e");
        }
        {
            let num = 0;
            let res = encode(&Value::Number(num)).expect("encoding to be successful");
            let res_str = String::from_utf8(res).expect("parsable as utf-8");
            assert_eq!(res_str.as_str(), "i0e");
        }
    }

    #[test]
    fn test_encode_list() {
        // Encode list
        let num_0 = 1337;
        let val_0 = Value::Number(num_0);

        let string = "Some val";
        let val_1 = Value::Bytes(string.as_bytes().to_vec());

        let num_1 = -1337;
        let val_2 = Value::Number(num_1);

        let res =
            encode(&Value::List(vec![val_0, val_1, val_2])).expect("encoding to be successful");
        let res_str = String::from_utf8(res).expect("parsable as utf-8");
        assert_eq!(res_str.as_str(), "li1337e8:Some vali-1337ee");
    }

    #[test]
    fn test_encode_dict() {
        // Encode dict
        let num_0 = 1337;
        let val_0 = Value::Number(num_0);

        let string = "Some val";
        let val_1 = Value::Bytes(string.as_bytes().to_vec());

        let num_1 = -1337;
        let val_2 = Value::Number(num_1);

        let val = Value::Dict(vec![
            (b"foo".to_vec(), val_0),
            (b"bar".to_vec(), val_1),
            (b"hello".to_vec(), val_2),
        ]);

        let res = encode(&val).expect("encoding to be successful");
        let res_str = String::from_utf8(res).expect("parsable as utf-8");
        assert_eq!(
            res_str.as_str(),
            "d3:bar8:Some val3:fooi1337e5:helloi-1337ee"
        );
    }

    #[test]
    fn test_encode_primitive_types() {
        let vu8: u8 = 8;
        let vu16: u16 = 16;
        let vu32: u32 = 32;
        let vu64: u64 = 64;

        assert_eq!(vu8.bencode_encode().unwrap(), "i8e".as_bytes().to_vec());
        assert_eq!(vu16.bencode_encode().unwrap(), "i16e".as_bytes().to_vec());
        assert_eq!(vu32.bencode_encode().unwrap(), "i32e".as_bytes().to_vec());
        assert_eq!(vu64.bencode_encode().unwrap(), "i64e".as_bytes().to_vec());

        let vi8: i8 = -8;
        let vi16: i16 = -16;
        let vi32: i32 = -32;
        let vi64: i64 = -64;

        assert_eq!(vi8.bencode_encode().unwrap(), "i-8e".as_bytes().to_vec());
        assert_eq!(vi16.bencode_encode().unwrap(), "i-16e".as_bytes().to_vec());
        assert_eq!(vi32.bencode_encode().unwrap(), "i-32e".as_bytes().to_vec());
        assert_eq!(vi64.bencode_encode().unwrap(), "i-64e".as_bytes().to_vec());
    }

    #[test]
    fn test_encode_from_vec_type() {
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

    #[test]
    fn test_encode_from_string() {
        assert_eq!(
            "Some val".to_owned().bencode_encode().unwrap(),
            "8:Some val".as_bytes().to_vec(),
        );
    }

    #[test]
    fn test_encode_from_hashmap() {
        let mut expected_inner = HashMap::new();
        expected_inner.insert("Some inner".to_owned(), 1337_u32);

        let mut expected_outer = HashMap::new();
        expected_outer.insert("Some outer".to_owned(), expected_inner);

        assert_eq!(
            expected_outer.bencode_encode().unwrap(),
            "d10:Some outerd10:Some inneri1337eee".as_bytes().to_vec(),
        );
    }
}
