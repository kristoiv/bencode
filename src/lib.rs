#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bytes(Vec<u8>),
    Number(i64),
    List(Vec<Value>),
    Map(Vec<(String, Value)>),
}

pub fn decode(buf: Vec<u8>) -> Result<Value, Box<dyn std::error::Error>> {
    #[derive(Debug, PartialEq)]
    enum State {
        Initial,
        BufferStringLength,
        BufferStringData(usize),
        Number,
        List(Option<Value>),
        MapKey(Option<Value>),
        MapValue(Option<Value>, Value),
    }

    let mut state: Vec<State> = vec![State::Initial];
    let mut state_buffer: Vec<u8> = vec![];
    let mut current_container_value: Option<Value> = None;

    for (idx, c) in buf.iter().enumerate() {
        let curr_state = state.last().unwrap();
        match curr_state {
            // Initial state
            State::Initial | State::List(..) | State::MapKey(..) | State::MapValue(..) => {
                match *c as char {
                    '0'..='9' => {
                        state.push(State::BufferStringLength);
                        state_buffer.push(*c);
                    }
                    'i' => state.push(State::Number),
                    'l' => {
                        state.push(State::List(current_container_value.clone()));
                        current_container_value = Some(Value::List(vec![]));
                    }
                    'd' => {
                        state.push(State::MapKey(current_container_value.clone()));
                        current_container_value = Some(Value::Map(vec![]));
                    }
                    'e' => match state.pop().unwrap() {
                        State::List(prev_container_value) => {
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
                        State::MapValue(prev_container_value, _) => {
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
                    _ => panic!("invalid format near {}", c),
                }
            }
            // Byte string state
            State::BufferStringLength => match *c as char {
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
                    state.push(State::BufferStringData(len));
                }
                _ => panic!("invalid format near {}", c),
            },
            // Byte string state
            State::BufferStringData(len) => {
                state_buffer.push(*c);
                if state_buffer.len() == *len {
                    // Done!
                    let val = Value::Bytes(state_buffer.clone());

                    state_buffer.clear();
                    state.pop();

                    if state.last().unwrap() == &State::Initial {
                        if (idx + 1) != buf.len() {
                            panic!(
                                "invalid bencode format, expected input to end after index={}",
                                idx
                            );
                        }
                        return Ok(val);
                    } else {
                        match current_container_value.as_mut().unwrap() {
                            Value::List(items) => {
                                items.push(val);
                            }
                            Value::Map(entries) => match state.last().unwrap() {
                                State::MapKey(..) => {
                                    let prev = match state.pop().unwrap() {
                                        State::MapKey(prev) => prev,
                                        _ => todo!(),
                                    };
                                    state.push(State::MapValue(prev, val));
                                }
                                State::MapValue(_, key) => {
                                    let inner_key = match key {
                                        Value::Bytes(byts) => byts,
                                        _ => todo!(),
                                    };
                                    entries
                                        .push((String::from_utf8(inner_key.clone()).unwrap(), val));
                                }
                                _ => todo!(),
                            },
                            _ => panic!("unsupported parent state: {:?}", state.last().unwrap()),
                        }
                    }
                }
            }
            // Number state
            State::Number => match *c as char {
                'e' => {
                    // Done!
                    let num = String::from_utf8(state_buffer.clone())?.parse::<i64>()?;
                    let val = Value::Number(num);

                    state_buffer.clear();
                    state.pop();

                    if state.last().unwrap() == &State::Initial {
                        if (idx + 1) != buf.len() {
                            panic!(
                                "invalid bencode format, expected input to end after index={}",
                                idx
                            );
                        }
                        return Ok(val);
                    } else {
                        match current_container_value.as_mut().unwrap() {
                            Value::List(items) => {
                                items.push(val);
                            }
                            Value::Map(entries) => match state.last().unwrap() {
                                State::MapValue(_, key) => {
                                    let inner_key = match key {
                                        Value::Bytes(byts) => byts,
                                        _ => todo!(),
                                    };
                                    entries
                                        .push((String::from_utf8(inner_key.clone()).unwrap(), val));
                                }
                                _ => todo!(),
                            },
                            _ => panic!("unsupported parent state: {:?}", state.last().unwrap()),
                        }
                    }
                }
                _ => state_buffer.push(*c),
            },
        }
    }

    Ok(Value::Number(-1))
}

pub fn encode(val: &Value) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
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
                let res_key = encode(&Value::Bytes(key.into_bytes()))?;
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
    fn test_encode() {
        // Encode bytes
        {
            let val = "Some val";
            let res =
                encode(&Value::Bytes(val.as_bytes().to_vec())).expect("encoding to be successful");
            let res_str = String::from_utf8(res).expect("parsable as utf-8");
            assert_eq!(res_str.as_str(), "8:Some val");
        }

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

        // Encode list
        {
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

        // Encode map
        {
            let num_0 = 1337;
            let val_0 = Value::Number(num_0);

            let string = "Some val";
            let val_1 = Value::Bytes(string.as_bytes().to_vec());

            let num_1 = -1337;
            let val_2 = Value::Number(num_1);

            let val = Value::Map(vec![
                ("foo".to_owned(), val_0),
                ("bar".to_owned(), val_1),
                ("hello".to_owned(), val_2),
            ]);

            let res = encode(&val).expect("encoding to be successful");
            let res_str = String::from_utf8(res).expect("parsable as utf-8");
            assert_eq!(
                res_str.as_str(),
                "d3:bar8:Some val3:fooi1337e5:helloi-1337ee"
            );
        }
    }

    #[test]
    fn test_decode() {
        // Decode bytes
        {
            let val = "8:Some val";
            let res = decode(val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(res, Value::Bytes(val[2..].as_bytes().to_vec()));
        }

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

        // TODO: Decode map
    }
}
