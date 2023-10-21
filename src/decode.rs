use super::*;
use anyhow::{anyhow, bail, Context, Result};

/// Decode a bencoded vector of bytes into a Value (an intermediate format)
pub fn decode(data: &Vec<u8>) -> Result<Value> {
    let mut decode_context = DecodeContext::new(data);
    loop {
        match decode_context.state() {
            DecodeState::Initial | DecodeState::ListElement | DecodeState::MapEntry(..) => {
                decode_state_initial(&mut decode_context).context("decode_state_initial")?
            }
            DecodeState::Bytes => {
                let val = decode_state_bytes(&mut decode_context).context("decode_state_bytes")?;
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val),
                    DecodeState::ListElement => {
                        decode_state_list_element_decoded(&mut decode_context, val)
                            .context("decode_state_list_element_decoded")?
                    }
                    // MapFinished in these context means entry-key found, move on to entry
                    DecodeState::MapFinished(..) => {
                        let key = match val {
                            Value::Bytes(key) => key,
                            _ => panic!("value must be of type Value::Bytes, was: {:?}", val),
                        };
                        decode_context.push_state(DecodeState::MapEntry(key));
                    }
                    DecodeState::MapEntry(key) => {
                        let key = key.clone();
                        decode_state_map_entry_decoded(&mut decode_context, &key, val)
                            .context("decode_state_map_entry_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading bytes: {:?}",
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
                    DecodeState::ListElement => {
                        decode_state_list_element_decoded(&mut decode_context, val)
                            .context("decode_state_list_element_decoded")?
                    }
                    DecodeState::MapEntry(key) => {
                        let key = key.clone();
                        decode_state_map_entry_decoded(&mut decode_context, &key, val)
                            .context("decode_state_map_entry_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading number: {:?}",
                            decode_context.state(),
                        )
                    }
                }
            }
            DecodeState::ListFinished(val) => {
                let val = val.clone();
                decode_context.pop_state();
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val.clone()),
                    DecodeState::ListElement => {
                        decode_state_list_element_decoded(&mut decode_context, val)
                            .context("decode_state_list_element_decoded")?
                    }
                    DecodeState::MapEntry(key) => {
                        let key = key.clone();
                        decode_state_map_entry_decoded(&mut decode_context, &key, val)
                            .context("decode_state_map_entry_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading list: {:?}",
                            decode_context.state(),
                        )
                    }
                }
            }
            DecodeState::MapFinished(val) => {
                let val = val.clone();
                decode_context.pop_state();
                match decode_context.state() {
                    DecodeState::Initial => return Ok(val.clone()),
                    DecodeState::ListElement => {
                        decode_state_list_element_decoded(&mut decode_context, val)
                            .context("decode_state_list_element_decoded")?
                    }
                    DecodeState::MapEntry(key) => {
                        let key = key.clone();
                        decode_state_map_entry_decoded(&mut decode_context, &key, val)
                            .context("decode_state_map_entry_decoded")?
                    }
                    _ => {
                        panic!(
                            "unexpected state after reading map: {:?}",
                            decode_context.state(),
                        )
                    }
                }
            }
        }
    }
}

/// The decode context holds all the required state for the state machine to operate
struct DecodeContext<'a> {
    state_vec: Vec<DecodeState>,
    state_buffer: Vec<u8>,
    data: &'a Vec<u8>,
    idx: usize,
}

impl<'a> DecodeContext<'a> {
    /// Create the initial decode context
    fn new(data: &'a Vec<u8>) -> Self {
        DecodeContext {
            state_buffer: vec![],
            state_vec: vec![DecodeState::Initial],
            data,
            idx: 0,
        }
    }

    /// Get the current state of decoding
    fn state(&mut self) -> &mut DecodeState {
        self.state_vec
            .last_mut()
            .expect("there should always be a valid state set")
    }

    /// Get the parent decoding state of the current state, if it exists
    fn parent_state(&mut self) -> Option<&mut DecodeState> {
        let len = self.state_vec.len();
        if len < 2 {
            None
        } else {
            self.state_vec.get_mut(len - 2)
        }
    }

    /// Push a new decoding state, making it the current one
    fn push_state(&mut self, ds: DecodeState) {
        self.state_vec.push(ds);
    }

    /// Pop off the current decoding state
    fn pop_state(&mut self) -> DecodeState {
        self.state_vec
            .pop()
            .expect("there should always be a valid state set")
    }

    /// Peek at the next byte that will be decoded (if it exists), without moving the cursor
    fn peek_next(&self) -> Option<u8> {
        self.data.get(self.idx).map(|it| *it)
    }

    /// Retrieve the next byte to decode (if it exists)
    fn next(&mut self) -> Option<u8> {
        let next = self.peek_next()?;
        self.idx += 1;
        Some(next)
    }

    /// Retrieve the current offset of the cursor into the data we are decoding
    fn offset(&self) -> usize {
        self.idx
    }
}

/// The decode states are the different states of the state machine used for decoding
#[derive(Debug, Clone)]
enum DecodeState {
    /// The initial state: indicates where to start, and when we should return the final value
    Initial,

    /// Decode a length prefixed number of bytes
    Bytes,

    /// Decode a signed number (integer)
    Number,

    /// State called when all list elements have been decoded
    ListFinished(Value),

    /// State that indicates the returned value belongs to a parent list-value
    ListElement,

    /// State called when all map entries have been decoded
    MapFinished(Value),

    /// State that indicates the returned value belongs to a parent map-value
    MapEntry(Vec<u8>),
}

/// In the initial/list_entry/map_entry states this is where we figure out what to decode next
fn decode_state_initial(decode_context: &mut DecodeContext) -> Result<()> {
    let cmd = decode_context
        .peek_next()
        .ok_or(anyhow!("unexpected end of data"))? as char;

    match cmd {
        '0'..='9' => decode_context.push_state(DecodeState::Bytes),
        'i' => {
            decode_context.push_state(DecodeState::Number);
        }
        'l' => {
            decode_context.next(); // Throw away dict-opening cmd
            decode_context.push_state(DecodeState::ListFinished(Value::List(vec![])));
            decode_context.push_state(DecodeState::ListElement);
        }
        'd' => {
            decode_context.next(); // Throw away dict-opening cmd
            decode_context.push_state(DecodeState::MapFinished(Value::Map(vec![])));
            decode_context.push_state(DecodeState::Bytes);
        }
        _ => bail!(
            "invalid format at [{}]: {} ({:#0X})",
            decode_context.offset() + 1,
            cmd,
            cmd as u8,
        ),
    }

    Ok(())
}

/// Decoding length prefixed bytes
fn decode_state_bytes(decode_context: &mut DecodeContext) -> Result<Value> {
    while let Some(d) = decode_context.next() {
        match d as char {
            '0'..='9' => decode_context.state_buffer.push(d),
            ':' => {
                let mut len = String::from_utf8(decode_context.state_buffer.clone())
                    .context("decoding bytes length prefix")?
                    .parse::<usize>()
                    .context("parsing bytes length prefix to usize")?;

                if len == 0 {
                    bail!("bytes was unexpectedly zero length");
                }

                decode_context.state_buffer.clear();

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
            _ => bail!(
                "invalid format at [{}]: {} ({:#0X})",
                decode_context.offset(),
                d as char,
                d,
            ),
        }
    }
    bail!("unexpected end of data");
}

/// Decoding a signed number (integer)
fn decode_state_number(decode_context: &mut DecodeContext) -> Result<Value> {
    decode_context.next(); // Throw away opening "i"
    while let Some(d) = decode_context.next() {
        match d as char {
            '-' | '0'..='9' => decode_context.state_buffer.push(d),
            'e' => {
                let num = String::from_utf8(decode_context.state_buffer.clone())
                    .context("decoding number as string")?
                    .parse::<i64>()
                    .context("parsing number as i64")?;

                decode_context.state_buffer.clear();
                decode_context.pop_state();
                return Ok(Value::Number(num));
            }
            _ => bail!(
                "invalid format at [{}]: {} ({:#0X})",
                decode_context.offset(),
                d as char,
                d,
            ),
        }
    }
    bail!("unexpected end of data");
}

/// A list element has been decoded, store it to the parent list value and check if we are done or have more elements to decode
fn decode_state_list_element_decoded(decode_context: &mut DecodeContext, val: Value) -> Result<()> {
    let mut list_state = decode_context
        .parent_state()
        .unwrap_or_else(|| panic!("should always be possible to get the parent map state"));

    let list_value = match &mut list_state {
        &mut DecodeState::ListFinished(val) => val,
        _ => panic!("should always be able to unpack list value"),
    };

    let elements = match list_value {
        Value::List(elements) => elements,
        _ => panic!("list value must be of type Value::List"),
    };

    elements.push(val);

    // Check if there are more entries or a termination cmd
    let cmd = decode_context
        .peek_next()
        .context("unexpected end of data")? as char;

    if cmd == 'e' {
        decode_context.next(); // Consume "e"
        decode_context.pop_state();
    } else {
        // There are more elements, so we stay in current state
    }

    Ok(())
}

/// A map entry has been decoded, store it to the parent map value and check if we are done or have more entries to decode
fn decode_state_map_entry_decoded(
    decode_context: &mut DecodeContext,
    key: &Vec<u8>,
    val: Value,
) -> Result<()> {
    let mut map_state = decode_context
        .parent_state()
        .unwrap_or_else(|| panic!("should always be possible to get the parent map state"));

    let map_value = match &mut map_state {
        &mut DecodeState::MapFinished(val) => val,
        _ => panic!("should always be able to unpack map value"),
    };

    let entries = match map_value {
        Value::Map(entries) => entries,
        _ => panic!("map value must be of type Value::Map"),
    };

    // Maps must be sorted and keys unique
    if let Some((last_entry_key, _)) = entries.last() {
        if last_entry_key.eq(key) {
            bail!("duplicate key entries are not allowed: {:?}", key);
        }
        if last_entry_key.gt(key) {
            bail!(
                "map keys have to be sorted to be valid: previous_key={:?} > key={:?}",
                last_entry_key,
                key,
            );
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
        decode_context.push_state(DecodeState::Bytes);
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
