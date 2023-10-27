use super::*;
use anyhow::{anyhow, bail, Context, Result};

/// Decode a bencoded vector of bytes into a Value (an intermediate format)
pub fn decode(data: &Vec<u8>) -> Result<Value> {
    let mut ctx = Ctx::new(data);
    let mut ds = DS::default();
    ds.run(&mut ctx)
}

/// Decoding context to keep track of data, cursor and parent values
struct Ctx<'a> {
    data: &'a Vec<u8>,
    idx: usize,
    parent_stack: Vec<Parent>,
}

impl<'a> Ctx<'a> {
    /// Create new decoding context with a given data buffer
    fn new(data: &'a Vec<u8>) -> Self {
        Self {
            data,
            idx: 0,
            parent_stack: vec![Parent::None],
        }
    }

    /// Peek at next byte to be decoded
    fn peek(&self) -> Option<u8> {
        self.data.get(self.idx).copied()
    }

    /// Get next byte to be decoded and advance cursor
    fn next(&mut self) -> Option<u8> {
        let n = self.peek()?;
        self.idx += 1;
        Some(n)
    }

    /// Get the current cursor offset from the start of the data buffer
    fn offset(&self) -> usize {
        self.idx
    }

    /// Get a reference to the current Parent value
    fn parent(&mut self) -> &mut Parent {
        self.parent_stack
            .last_mut()
            .expect("there should always be a parent")
    }

    /// Push a new current Parent value
    fn push_parent(&mut self, p: Parent) {
        self.parent_stack.push(p);
    }

    /// Pop out the current Parent value
    fn pop_parent(&mut self) -> Parent {
        self.parent_stack
            .pop()
            .expect("there should always be a parent")
    }
}

/// Parent value types
enum Parent {
    /// Parent is a list type
    List { container: Value },

    /// Parent is a dictionary type
    Dict {
        container: Value,
        next_key: Option<Value>,
    },

    /// There is no parent
    None,
}

/// Decoder states of the finite state machine
enum DS {
    /// Discover next value type
    DecodeNext,

    /// Decode a length prefixed byte array
    Bytes,

    /// Decode a number
    Number,

    /// Decode a list of values
    ListStart,

    /// Decoding of a list of values completed
    ListEnd,

    /// Decode a dict of values
    DictStart,

    /// Decoding of a dict of values completed
    DictEnd,

    /// Value found, finished!
    Finished(Value),
}

impl Default for DS {
    /// Create a default decoder state
    fn default() -> Self {
        Self::DecodeNext
    }
}

/// Possible state transitions for the "DecodeNext" state
enum AfterDecodeNext {
    Bytes,
    Number,
    ListStart,
    ListEnd,
    DictStart,
    DictEnd,
}

/// Possible state transitions for the "Bytes" state
enum AfterBytes {
    DecodeNext,
    Finished(Value),
}

/// Possible state transitions for the "Number" state
enum AfterNumber {
    DecodeNext,
    Finished(Value),
}

/// Possible state transitions for the "ListStart" state
enum AfterListStart {
    DecodeNext,
}

/// Possible state transitions for the "ListEnd" state
enum AfterListEnd {
    DecodeNext,
    Finished(Value),
}

/// Possible state transitions for the "DictStart" state
enum AfterDictStart {
    Bytes,
}

/// Possible state transitions for the "DictEnd" state
enum AfterDictEnd {
    DecodeNext,
    Finished(Value),
}

/// Decoder state handlers that must be implemented
trait DSHandlers {
    fn decode_next(&self, ctx: &mut Ctx) -> Result<AfterDecodeNext>;
    fn bytes(&self, ctx: &mut Ctx) -> Result<AfterBytes>;
    fn number(&self, ctx: &mut Ctx) -> Result<AfterNumber>;
    fn list_start(&self, ctx: &mut Ctx) -> Result<AfterListStart>;
    fn list_end(&self, ctx: &mut Ctx) -> Result<AfterListEnd>;
    fn dict_start(&self, ctx: &mut Ctx) -> Result<AfterDictStart>;
    fn dict_end(&self, ctx: &mut Ctx) -> Result<AfterDictEnd>;
}

impl DSHandlers for DS {
    /// Decode next state
    fn decode_next(&self, ctx: &mut Ctx) -> Result<AfterDecodeNext> {
        let cmd = ctx
            .peek()
            .ok_or_else(|| anyhow!("unexpected end of input"))? as char;

        match cmd {
            '0'..='9' => Ok(AfterDecodeNext::Bytes),
            'i' => Ok(AfterDecodeNext::Number),
            'l' => Ok(AfterDecodeNext::ListStart),
            'd' => Ok(AfterDecodeNext::DictStart),
            'e' => match ctx.parent() {
                Parent::List { .. } => Ok(AfterDecodeNext::ListEnd),
                Parent::Dict { .. } => Ok(AfterDecodeNext::DictEnd),
                Parent::None => todo!(),
            },
            _ => Err(anyhow!(
                "unexpected cmd: {} ({:#0X}, offset={})",
                cmd,
                cmd as u8,
                ctx.offset(),
            )),
        }
    }

    /// Bytes state
    fn bytes(&self, ctx: &mut Ctx) -> Result<AfterBytes> {
        let mut buf = vec![];

        while let Some(n) = ctx.next() {
            match n as char {
                '0'..='9' => buf.push(n),
                ':' => break,
                _ => bail!(
                    "unexpected input while parsing length prefix of bytes: {:#0X} (offset={})",
                    n,
                    ctx.offset(),
                ),
            }
        }

        let mut len = String::from_utf8(buf)
            .context("decode length prefix of byte array as utf-8 string")?
            .parse::<usize>()
            .context("parsing decoded length prefix of byte array as usize")?;

        let mut buf = vec![];
        while len > 0 {
            buf.push(ctx.next().context(format!(
                "unexpected end of data while reading byte array data, expecting {} more byte(s)",
                len,
            ))?);
            len -= 1;
        }

        let val = Value::Bytes(buf);

        match ctx.parent() {
            Parent::List { container } => {
                list_entry_handler(container, val);
                Ok(AfterBytes::DecodeNext)
            }
            Parent::Dict {
                container,
                next_key,
            } => {
                dict_entry_handler(container, next_key, val);
                Ok(AfterBytes::DecodeNext)
            }
            Parent::None => Ok(AfterBytes::Finished(val)),
        }
    }

    /// Number state
    fn number(&self, ctx: &mut Ctx) -> Result<AfterNumber> {
        ctx.next(); // discard 'i'

        let mut buf = vec![];
        while let Some(n) = ctx.next() {
            match n as char {
                '-' | '0'..='9' => buf.push(n),
                'e' => break,
                _ => bail!(
                    "unexpected input while parsing number: {:#0X} (offset={})",
                    n,
                    ctx.offset(),
                ),
            }
        }

        let num = String::from_utf8(buf)
            .context("decoding number into utf-8 encoded string")?
            .parse::<i64>()
            .context("parsing decoded number as i64")?;

        let val = Value::Number(num);

        match ctx.parent() {
            Parent::List { container } => {
                list_entry_handler(container, val);
                Ok(AfterNumber::DecodeNext)
            }
            Parent::Dict {
                container,
                next_key,
            } => {
                dict_entry_handler(container, next_key, val);
                Ok(AfterNumber::DecodeNext)
            }
            Parent::None => Ok(AfterNumber::Finished(val)),
        }
    }

    /// List start state
    fn list_start(&self, ctx: &mut Ctx) -> Result<AfterListStart> {
        ctx.next(); // discard 'l'
        ctx.push_parent(Parent::List {
            container: Value::List(vec![]),
        });
        Ok(AfterListStart::DecodeNext)
    }

    /// List end state
    fn list_end(&self, ctx: &mut Ctx) -> Result<AfterListEnd> {
        ctx.next(); // discard 'e'

        let val = match ctx.pop_parent() {
            Parent::List { container } => container,
            _ => panic!("parent value must be Parent::List"),
        };

        match ctx.parent() {
            Parent::List { container } => {
                list_entry_handler(container, val);
                Ok(AfterListEnd::DecodeNext)
            }
            Parent::Dict {
                container,
                next_key,
            } => {
                dict_entry_handler(container, next_key, val);
                Ok(AfterListEnd::DecodeNext)
            }
            Parent::None => Ok(AfterListEnd::Finished(val)),
        }
    }

    /// Dict start state
    fn dict_start(&self, ctx: &mut Ctx) -> Result<AfterDictStart> {
        ctx.next(); // discard 'd'
        ctx.push_parent(Parent::Dict {
            container: Value::Dict(vec![]),
            next_key: None,
        });
        Ok(AfterDictStart::Bytes)
    }

    /// Dict end state
    fn dict_end(&self, ctx: &mut Ctx) -> Result<AfterDictEnd> {
        ctx.next(); // discard 'e'

        let val = match ctx.pop_parent() {
            Parent::Dict { container, .. } => container,
            _ => panic!("parent value must be Parent::Dict"),
        };

        match ctx.parent() {
            Parent::List { container } => {
                list_entry_handler(container, val);
                Ok(AfterDictEnd::DecodeNext)
            }
            Parent::Dict {
                container,
                next_key,
            } => {
                dict_entry_handler(container, next_key, val);
                Ok(AfterDictEnd::DecodeNext)
            }
            Parent::None => Ok(AfterDictEnd::Finished(val)),
        }
    }
}

/// Helper function for pushing list entries onto the parent list value
fn list_entry_handler(container: &mut Value, val: Value) {
    match container {
        Value::List(e) => e.push(val),
        _ => panic!("parent value's container value must be Value::List"),
    }
}

/// Helper function for pushing dict entries onto the parent dict value
fn dict_entry_handler(container: &mut Value, next_key: &mut Option<Value>, val: Value) {
    if next_key.is_none() {
        *next_key = Some(val);
    } else {
        let key = match next_key.as_ref().unwrap().clone() {
            Value::Bytes(b) => b,
            _ => panic!("dict entries can only have byte arrays as keys"),
        };
        match container {
            Value::Dict(e) => e.push((key, val)),
            _ => panic!("parent value's container value must be Value::Dict"),
        }
    }
}

impl DS {
    /// Run the decoding through the state machine
    fn run(&mut self, ctx: &mut Ctx) -> Result<Value> {
        loop {
            *self = match self {
                Self::DecodeNext => match self.decode_next(ctx)? {
                    AfterDecodeNext::Bytes => Self::Bytes,
                    AfterDecodeNext::Number => Self::Number,
                    AfterDecodeNext::ListStart => Self::ListStart,
                    AfterDecodeNext::ListEnd => Self::ListEnd,
                    AfterDecodeNext::DictStart => Self::DictStart,
                    AfterDecodeNext::DictEnd => Self::DictEnd,
                },

                Self::Bytes => match self.bytes(ctx)? {
                    AfterBytes::DecodeNext => Self::DecodeNext,
                    AfterBytes::Finished(val) => Self::Finished(val),
                },

                Self::Number => match self.number(ctx)? {
                    AfterNumber::DecodeNext => Self::DecodeNext,
                    AfterNumber::Finished(val) => Self::Finished(val),
                },

                Self::ListStart => match self.list_start(ctx)? {
                    AfterListStart::DecodeNext => Self::DecodeNext,
                },

                Self::ListEnd => match self.list_end(ctx)? {
                    AfterListEnd::DecodeNext => Self::DecodeNext,
                    AfterListEnd::Finished(val) => Self::Finished(val),
                },

                Self::DictStart => match self.dict_start(ctx)? {
                    AfterDictStart::Bytes => Self::Bytes,
                },

                Self::DictEnd => match self.dict_end(ctx)? {
                    AfterDictEnd::DecodeNext => Self::DecodeNext,
                    AfterDictEnd::Finished(val) => Self::Finished(val),
                },

                Self::Finished(val) => return Ok(val.clone()),
            };
        }
    }
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
    fn test_decode_dict() {
        // Decode dict
        {
            let val = "d8:Some val5:helloe";
            let res = decode(&val.as_bytes().to_vec()).expect("decoding to be successful");
            assert_eq!(
                res,
                Value::Dict(vec![(
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
                Value::Dict(vec![(
                    "Some val".as_bytes().to_vec(),
                    Value::Dict(vec![(
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
