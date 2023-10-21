use anyhow::{bail, Result};

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bytes(Vec<u8>),
    Number(i64),
    List(Vec<Value>),
    Map(Vec<(Vec<u8>, Value)>),
}

#[derive(Debug, PartialEq)]
enum DecodeState {
    Initial,
    ByteStringLength,
    ByteStringData(usize),
    Number,
    List(Option<Value>),
    MapKey(Option<Value>),
    MapValue(Option<Value>, Value),
}

pub fn decode(buf: Vec<u8>) -> Result<Value> {
    let mut state: Vec<DecodeState> = vec![DecodeState::Initial];
    let mut state_buffer: Vec<u8> = vec![];
    let mut current_container_value: Option<Value> = None;

    for (idx, c) in buf.iter().enumerate() {
        let curr_state = state.last().unwrap();
        match curr_state {
            // Initial state
            DecodeState::Initial
            | DecodeState::List(..)
            | DecodeState::MapKey(..)
            | DecodeState::MapValue(..) => match *c as char {
                '0'..='9' => {
                    state.push(DecodeState::ByteStringLength);
                    state_buffer.push(*c);
                }
                'i' => state.push(DecodeState::Number),
                'l' => {
                    state.push(DecodeState::List(current_container_value.clone()));
                    current_container_value = Some(Value::List(vec![]));
                }
                'd' => {
                    state.push(DecodeState::MapKey(current_container_value.clone()));
                    current_container_value = Some(Value::Map(vec![]));
                }
                'e' => match state.pop().unwrap() {
                    DecodeState::List(prev_container_value) => {
                        let list_val = current_container_value.unwrap();
                        current_container_value = prev_container_value.clone();
                        if current_container_value.is_none() {
                            return Ok(list_val);
                        } else {
                            match current_container_value.as_mut().unwrap() {
                                Value::List(items) => {
                                    items.push(list_val);
                                }
                                _ => todo!(),
                            }
                        }
                    }
                    DecodeState::MapValue(prev_container_value, _) => {
                        let map_val = current_container_value.unwrap();
                        current_container_value = prev_container_value.clone();
                        if current_container_value.is_none() {
                            return Ok(map_val);
                        } else {
                            match current_container_value.as_mut().unwrap() {
                                Value::List(items) => {
                                    items.push(map_val);
                                }
                                _ => todo!(),
                            }
                        }
                    }
                    _ => todo!(),
                },
                _ => bail!("invalid format near {}", c),
            },
            // Byte string state
            DecodeState::ByteStringLength => {
                decode_byte_string_length(c, &mut state, &mut state_buffer)?;
            }
            // Byte string state
            DecodeState::ByteStringData(len) => {
                let len = *len;
                if let Some(decoded_val) = decode_byte_string_data(
                    c,
                    &mut state,
                    &mut state_buffer,
                    len,
                    idx,
                    &buf,
                    &mut current_container_value,
                )? {
                    return Ok(decoded_val);
                }
            }
            // Number state
            DecodeState::Number => {
                if let Some(decoded_val) = decode_number(
                    c,
                    &mut state,
                    &mut state_buffer,
                    idx,
                    &buf,
                    &mut current_container_value,
                )? {
                    return Ok(decoded_val);
                }
            }
        }
    }

    Ok(Value::Number(-1))
}

fn decode_byte_string_length(
    c: &u8,
    state: &mut Vec<DecodeState>,
    state_buffer: &mut Vec<u8>,
) -> Result<()> {
    match *c as char {
        '0'..='9' => {
            state_buffer.push(*c);
        }
        ':' => {
            let len = String::from_utf8(state_buffer.clone())
                .unwrap()
                .parse::<usize>()
                .unwrap();

            state_buffer.clear();
            state.pop();
            state.push(DecodeState::ByteStringData(len));
        }
        _ => bail!("invalid format near {}", c),
    }
    return Ok(());
}

fn decode_byte_string_data(
    c: &u8,
    state: &mut Vec<DecodeState>,
    state_buffer: &mut Vec<u8>,
    len: usize,
    idx: usize,
    buf: &Vec<u8>,
    current_container_value: &mut Option<Value>,
) -> Result<Option<Value>> {
    state_buffer.push(*c);
    if state_buffer.len() == len {
        // Done!
        let val = Value::Bytes(state_buffer.clone());

        state_buffer.clear();
        state.pop();

        if state.last().unwrap() == &DecodeState::Initial {
            if (idx + 1) != buf.len() {
                bail!(
                    "invalid bencode format, expected input to end after index={}",
                    idx
                );
            }
            return Ok(Some(val));
        } else {
            match current_container_value.as_mut().unwrap() {
                Value::List(items) => {
                    items.push(val);
                }
                Value::Map(entries) => match state.last().unwrap() {
                    DecodeState::MapKey(..) => {
                        let prev = match state.pop().unwrap() {
                            DecodeState::MapKey(prev) => prev,
                            _ => todo!(),
                        };
                        state.push(DecodeState::MapValue(prev, val));
                    }
                    DecodeState::MapValue(_, key) => {
                        let inner_key = match key {
                            Value::Bytes(byts) => byts,
                            _ => todo!(),
                        };
                        entries.push((inner_key.clone(), val));
                    }
                    _ => todo!(),
                },
                _ => bail!("unsupported parent state: {:?}", state.last().unwrap()),
            }
        }
    }
    return Ok(None);
}

fn decode_number(
    c: &u8,
    state: &mut Vec<DecodeState>,
    state_buffer: &mut Vec<u8>,
    idx: usize,
    buf: &Vec<u8>,
    current_container_value: &mut Option<Value>,
) -> Result<Option<Value>> {
    match *c as char {
        'e' => {
            // Done!
            let num = String::from_utf8(state_buffer.clone())
                .unwrap()
                .parse::<i64>()
                .unwrap();
            let val = Value::Number(num);

            state_buffer.clear();
            state.pop();

            if state.last().unwrap() == &DecodeState::Initial {
                if (idx + 1) != buf.len() {
                    bail!(
                        "invalid bencode format, expected input to end after index={}",
                        idx
                    );
                }
                return Ok(Some(val));
            } else {
                match current_container_value.as_mut().unwrap() {
                    Value::List(items) => {
                        items.push(val);
                    }
                    Value::Map(entries) => match state.last().unwrap() {
                        DecodeState::MapValue(_, key) => {
                            let inner_key = match key {
                                Value::Bytes(byts) => byts,
                                _ => todo!(),
                            };
                            entries.push((inner_key.clone(), val));
                        }
                        _ => todo!(),
                    },
                    _ => bail!("unsupported parent state: {:?}", state.last().unwrap()),
                }
            }
        }
        _ => state_buffer.push(*c),
    }
    return Ok(None);
}

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

        Value::Map(entries) => {
            let mut entries = entries.clone();
            entries.sort_by(|(a, _), (b, _)| a.cmp(b));

            let mut results = vec![vec!['d' as u8]];
            for (key, val) in entries {
                let res_key = encode(&Value::Bytes(key))?;
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
    fn test_encode_map() {
        // Encode map
        let num_0 = 1337;
        let val_0 = Value::Number(num_0);

        let string = "Some val";
        let val_1 = Value::Bytes(string.as_bytes().to_vec());

        let num_1 = -1337;
        let val_2 = Value::Number(num_1);

        let val = Value::Map(vec![
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
    fn test_decode_bytestr() {
        // Decode bytes
        let val = "8:Some val";
        let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
        assert_eq!(res, Value::Bytes(val[2..].as_bytes().to_vec()));
    }

    #[test]
    fn test_decode_number() {
        // Decode number
        {
            let val = "i1337e";
            let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(res, Value::Number(1337));
        }
        {
            let val = "i-1337e";
            let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(res, Value::Number(-1337));
        }
    }

    #[test]
    fn test_decode_list() {
        // Decode list
        {
            let val = "li1337e8:Some vali-1337ee";
            let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(
                res,
                Value::List(vec![
                    Value::Number(1337),
                    Value::Bytes("Some val".as_bytes().to_vec()),
                    Value::Number(-1337),
                ])
            );
        }
        {
            let val = "li1337el8:Some valei-1337ee";
            let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(
                res,
                Value::List(vec![
                    Value::Number(1337),
                    Value::List(vec![Value::Bytes("Some val".as_bytes().to_vec())]),
                    Value::Number(-1337),
                ])
            );
        }
    }

    #[test]
    fn test_decode_map() {
        // TODO: Decode map
        assert!(true);
    }
}
