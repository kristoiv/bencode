use super::*;
use anyhow::{anyhow, bail, Context, Result};

pub fn decode(data: &Vec<u8>) -> Result<Value> {
    let mut decode_context = DecodeContext::new(data);
    loop {
        match decode_context.state() {
            DecodeState::Initial | DecodeState::ListEntry | DecodeState::MapData(..) => {
                decode_state_initial(&mut decode_context).context("decode_state_initial")?
            }
            DecodeState::BytesLength => decode_state_bytes_length(&mut decode_context)
                .context("decode_state_bytes_length")?,
            DecodeState::BytesData(..) => {
                let val = decode_state_bytes_data(&mut decode_context)
                    .context("decode_state_bytes_data")?;
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val),
                    DecodeState::ListEntry => {
                        decode_state_listentry_decoded(&mut decode_context, val)
                            .context("decode_state_listentry_decoded")?
                    }
                    DecodeState::Map(..) => {
                        let key = match val {
                            Value::Bytes(key) => key,
                            _ => panic!("value must be of type Bytes, was: {:?}", val),
                        };
                        decode_context.push_state(DecodeState::MapData(key));
                    }
                    DecodeState::MapData(key) => {
                        let key = key.clone();
                        decode_state_mapdata_decoded(&mut decode_context, &key, val)
                            .context("decode_state_mapdata_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading byte string data: {:?}",
                            decode_context.state()
                        )
                    }
                }
            }
            DecodeState::Number => {
                let val =
                    decode_state_number(&mut decode_context).context("decode_state_number")?;
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val),
                    DecodeState::ListEntry => {
                        decode_state_listentry_decoded(&mut decode_context, val)
                            .context("decode_state_listentry_decoded")?
                    }
                    DecodeState::MapData(key) => {
                        let key = key.clone();
                        decode_state_mapdata_decoded(&mut decode_context, &key, val)
                            .context("decode_state_mapdata_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading byte string data: {:?}",
                            decode_context.state()
                        )
                    }
                }
            }
            DecodeState::List(val) => {
                let val = val.clone();
                decode_context.pop_state();
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val.clone()),
                    DecodeState::ListEntry => {
                        decode_state_listentry_decoded(&mut decode_context, val)
                            .context("decode_state_listentry_decoded")?
                    }
                    DecodeState::MapData(key) => {
                        let key = key.clone();
                        decode_state_mapdata_decoded(&mut decode_context, &key, val)
                            .context("decode_state_mapdata_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after parsing map: {:?}",
                            decode_context.state()
                        )
                    }
                }
            }
            DecodeState::Map(val) => {
                let val = val.clone();
                decode_context.pop_state();
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val.clone()),
                    DecodeState::ListEntry => {
                        decode_state_listentry_decoded(&mut decode_context, val)
                            .context("decode_state_listentry_decoded")?
                    }
                    DecodeState::MapData(key) => {
                        let key = key.clone();
                        decode_state_mapdata_decoded(&mut decode_context, &key, val)
                            .context("decode_state_mapdata_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after parsing map: {:?}",
                            decode_context.state()
                        )
                    }
                }
            }
        }
    }
}

struct DecodeContext<'a> {
    state_vec: Vec<DecodeState>,
    state_buffer: Vec<u8>,
    data: &'a Vec<u8>,
    idx: usize,
}

impl<'a> DecodeContext<'a> {
    fn new(data: &'a Vec<u8>) -> Self {
        DecodeContext {
            state_buffer: vec![],
            state_vec: vec![DecodeState::Initial],
            data,
            idx: 0,
        }
    }
    fn state(&mut self) -> &mut DecodeState {
        self.state_vec
            .last_mut()
            .expect("there should always be decoding state in the decode context")
    }
    fn parent_state(&mut self) -> Option<&mut DecodeState> {
        let len = self.state_vec.len();
        if len < 2 {
            None
        } else {
            self.state_vec.get_mut(len - 2)
        }
    }
    fn push_state(&mut self, ds: DecodeState) {
        self.state_vec.push(ds);
    }
    fn pop_state(&mut self) -> DecodeState {
        self.state_vec
            .pop()
            .expect("there should always be decoding states in the decoding context")
    }
    fn replace_state(&mut self, ds: DecodeState) -> DecodeState {
        let prev = self.pop_state();
        self.push_state(ds);
        prev
    }
    fn peek_next(&self) -> Option<u8> {
        self.data.get(self.idx).map(|it| *it)
    }
    fn next(&mut self) -> Option<u8> {
        let next = self.peek_next()?;
        self.idx += 1;
        Some(next)
    }
}

#[derive(Debug, Clone)]
enum DecodeState {
    Initial,
    BytesLength,
    BytesData(usize),
    Number,
    List(Value),
    ListEntry,
    Map(Value),
    MapData(Vec<u8>),
}

fn decode_state_initial(decode_context: &mut DecodeContext) -> Result<()> {
    let cmd = decode_context
        .peek_next()
        .ok_or(anyhow!("unexpected end of data"))? as char;

    match cmd {
        '0'..='9' => decode_context.push_state(DecodeState::BytesLength),
        'i' => {
            decode_context.push_state(DecodeState::Number);
        }
        'l' => {
            decode_context.next(); // Throw away dict-opening cmd
            decode_context.push_state(DecodeState::List(Value::List(vec![])));
            decode_context.push_state(DecodeState::ListEntry);
        }
        'd' => {
            decode_context.next(); // Throw away dict-opening cmd
            decode_context.push_state(DecodeState::Map(Value::Map(vec![])));
            decode_context.push_state(DecodeState::BytesLength);
        }
        _ => bail!("unexpected input: {}", cmd),
    }

    Ok(())
}

fn decode_state_bytes_length(decode_context: &mut DecodeContext) -> Result<()> {
    while let Some(d) = decode_context.next() {
        match d as char {
            '0'..='9' => decode_context.state_buffer.push(d),
            ':' => {
                let len = String::from_utf8(decode_context.state_buffer.clone())
                    .context("decoding byte string length prefix")?
                    .parse::<usize>()
                    .context("parsing byte string length prefix to usize")?;

                if len == 0 {
                    bail!("byte string was unexpectedly zero length");
                }

                decode_context.state_buffer.clear();
                decode_context.replace_state(DecodeState::BytesData(len));
                return Ok(());
            }
            _ => bail!("unexpected data: {} ({:#0X})", d as char, d),
        }
    }
    bail!("unexpected end of data");
}

fn decode_state_bytes_data(decode_context: &mut DecodeContext) -> Result<Value> {
    let mut len = match decode_context.state() {
        DecodeState::BytesData(len) => *len,
        _ => panic!(
            "decode_state_bytes_data called from unexpected state: {:?}",
            decode_context.state()
        ),
    };

    while let Some(d) = decode_context.next() {
        decode_context.state_buffer.push(d);
        len -= 1;
        if len == 0 {
            let val = Value::Bytes(decode_context.state_buffer.clone());
            decode_context.state_buffer.clear();
            decode_context.pop_state();
            return Ok(val);
        }
    }

    bail!("unexpected end of data");
}

fn decode_state_number(decode_context: &mut DecodeContext) -> Result<Value> {
    decode_context.next(); // Throw away opening "i"
    while let Some(d) = decode_context.next() {
        match d as char {
            '-' | '0'..='9' => decode_context.state_buffer.push(d),
            'e' => {
                let num = String::from_utf8(decode_context.state_buffer.clone())
                    .context("decoding number as string")?
                    .parse::<i64>()
                    .context("decoding number as i64")?;

                decode_context.state_buffer.clear();
                decode_context.pop_state();
                return Ok(Value::Number(num));
            }
            _ => bail!("unexpected input: {} ({:#0X})", d, d),
        }
    }
    bail!("unexpected end of data during decoding of number");
}

fn decode_state_listentry_decoded(decode_context: &mut DecodeContext, val: Value) -> Result<()> {
    let mut list_state = decode_context
        .parent_state()
        .unwrap_or_else(|| panic!("should always be possible to get parent map state"));

    let map_value = match &mut list_state {
        &mut DecodeState::List(val) => val,
        _ => panic!("should always be able to unpack list_value"),
    };

    let items = match map_value {
        Value::List(items) => items,
        _ => panic!("list value must be of type List"),
    };

    items.push(val);

    // Check if there are more entries or a termination cmd
    let cmd = decode_context
        .peek_next()
        .context("unexpected end of data")? as char;

    if cmd == 'e' {
        decode_context.next(); // Consume "e"
        decode_context.pop_state();
    } else {
        // There are more entries, so we stay in current state
    }

    Ok(())
}

fn decode_state_mapdata_decoded(
    decode_context: &mut DecodeContext,
    key: &Vec<u8>,
    val: Value,
) -> Result<()> {
    let mut map_state = decode_context
        .parent_state()
        .unwrap_or_else(|| panic!("should always be possible to get parent map state"));

    let map_value = match &mut map_state {
        &mut DecodeState::Map(val) => val,
        _ => panic!("should always be able to unpack map_value"),
    };

    let entries = match map_value {
        Value::Map(entries) => entries,
        _ => panic!("map value must be of type map"),
    };

    // Maps must be sorted and keys unique
    if let Some((last_entry_key, _)) = entries.last() {
        if last_entry_key.eq(key) {
            bail!("duplicate key entries not allowed: {:?}", key);
        }
        if last_entry_key.gt(key) {
            bail!("map keys have to be sorted to be valid");
        }
    }

    entries.push((key.clone(), val));

    // Check if there are more entries or a termination cmd
    let cmd = decode_context
        .peek_next()
        .context("unexpected end of data")? as char;

    if cmd == 'e' {
        decode_context.next(); // Consume "e"
        decode_context.pop_state();
    } else {
        // There are more entries
        decode_context.push_state(DecodeState::BytesLength);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_bytestr() {
        // Decode bytes
        let val = "8:Some val";
        let res = decode(&val.as_bytes().to_vec()).expect("decoding failed");
        assert_eq!(res, Value::Bytes(val[2..].as_bytes().to_vec()));
    }

    #[test]
    fn test_decode_number() {
        // Decode number
        {
            let val = "i1337e";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(res, Value::Number(1337));
        }
        {
            let val = "i-1337e";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(res, Value::Number(-1337));
        }
    }

    #[test]
    fn test_decode_list() {
        // Decode list
        {
            let val = "li1337e8:Some vali-1337ee";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
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
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
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
        // Decode map
        {
            let val = "d8:Some val5:helloe";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(
                res,
                Value::Map(vec![(
                    "Some val".as_bytes().to_vec(),
                    Value::Bytes("hello".as_bytes().to_vec())
                )])
            );
        }
        {
            let val = "d8:Some vald3:foo3:baree";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(
                res,
                Value::Map(vec![(
                    "Some val".as_bytes().to_vec(),
                    Value::Map(vec![(
                        "foo".as_bytes().to_vec(),
                        Value::Bytes("bar".as_bytes().to_vec())
                    ),]),
                )])
            );
        }
    }

    #[test]
    fn test_decode_primitive_types() {
        let vu8: Vec<u8> = "i8e".as_bytes().to_vec();
        let vu16: Vec<u8> = "i16e".as_bytes().to_vec();
        let vu32: Vec<u8> = "i32e".as_bytes().to_vec();
        let vu64: Vec<u8> = "i64e".as_bytes().to_vec();

        assert_eq!(u8::from_bencode(&vu8).unwrap(), 8);
        assert_eq!(u16::from_bencode(&vu16).unwrap(), 16);
        assert_eq!(u32::from_bencode(&vu32).unwrap(), 32);
        assert_eq!(u64::from_bencode(&vu64).unwrap(), 64);

        let vi8: Vec<u8> = "i-8e".as_bytes().to_vec();
        let vi16: Vec<u8> = "i-16e".as_bytes().to_vec();
        let vi32: Vec<u8> = "i-32e".as_bytes().to_vec();
        let vi64: Vec<u8> = "i-64e".as_bytes().to_vec();

        assert_eq!(i8::from_bencode(&vi8).unwrap(), -8);
        assert_eq!(i16::from_bencode(&vi16).unwrap(), -16);
        assert_eq!(i32::from_bencode(&vi32).unwrap(), -32);
        assert_eq!(i64::from_bencode(&vi64).unwrap(), -64);
    }

    #[test]
    fn test_decode_to_vec_type() {
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

    #[test]
    #[should_panic]
    fn test_will_fail_to_decode_to_vec_if_multiple_types() {
        Vec::<u8>::from_bencode(&"li100e8:Some vale".as_bytes().to_vec()).unwrap();
    }

    #[test]
    fn test_decode_to_string() {
        assert_eq!(
            String::from_bencode(&"8:Some val".as_bytes().to_vec()).unwrap(),
            "Some val".to_owned()
        );
    }

    #[test]
    fn test_decode_to_hashmap() {
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
}
