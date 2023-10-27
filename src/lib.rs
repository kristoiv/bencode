use std::collections::HashMap;

use anyhow::{anyhow, Result};

mod decode;
mod encode;

pub use decode::*;
pub use encode::*;

/// An intermediate value format that can be encoded or decoded
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// A length prefixed list of bytes
    Bytes(Vec<u8>),

    /// A signed number (integer)
    Number(i64),

    /// A list of other values of any type
    List(Vec<Value>),

    /// A dict of other values of any type, with keys represented as a length prefixed list of bytes
    Dict(Vec<(Vec<u8>, Value)>),
}

/// Bencode encoder trait
pub trait BencodeEncode {
    fn bencode_encode(&self) -> Result<Vec<u8>>;
}

/// Generic Bencode encoder implementation for any type that can be transformed to our intermediate Value type
impl<T> BencodeEncode for T
where
    T: Into<Value> + Clone,
{
    fn bencode_encode(&self) -> Result<Vec<u8>> {
        let val: Value = self.clone().into();
        encode(&val)
    }
}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        Value::Number(value as i64)
    }
}

impl From<u16> for Value {
    fn from(value: u16) -> Self {
        Value::Number(value as i64)
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Value::Number(value as i64)
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Value::Number(value as i64)
    }
}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        Value::Number(value as i64)
    }
}

impl From<i16> for Value {
    fn from(value: i16) -> Self {
        Value::Number(value as i64)
    }
}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        Value::Number(value as i64)
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::Number(value as i64)
    }
}

impl<T: Into<Value> + Clone> From<Vec<T>> for Value {
    fn from(value: Vec<T>) -> Self {
        Value::List(
            value
                .iter()
                .map(|it| it.clone().into())
                .collect::<Vec<Value>>(),
        )
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Value::Bytes(value.as_bytes().to_vec())
    }
}

impl<T> From<HashMap<String, T>> for Value
where
    T: Into<Value>,
{
    fn from(value: HashMap<String, T>) -> Self {
        let mut entries = vec![];
        for (key, val) in value {
            let key = key.as_bytes().to_vec();
            let val: Value = val.into();
            entries.push((key, val));
        }
        Value::Dict(entries)
    }
}

/// Bencode decoder trait
pub trait BencodeDecode<T>
where
    Self: Sized,
    T: TryFrom<Value>,
{
    fn from_bencode(val: &Vec<u8>) -> Result<Self>;
}

/// Generic Bencode decoder implementation for any type that can be transformed into from our intermediate Value type
impl<T> BencodeDecode<T> for T
where
    T: TryFrom<Value>,
    anyhow::Error: From<T::Error>,
{
    fn from_bencode(bytes: &Vec<u8>) -> Result<T> {
        let val = decode(bytes)?;
        let res: T = val.try_into()?;
        Ok(res)
    }
}

impl TryFrom<Value> for u8 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for u16 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for u32 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for u64 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for i8 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for i16 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for i32 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for i64 {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(num) => Ok(num as Self),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl<T> TryFrom<Value> for Vec<T>
where
    T: TryFrom<Value>,
    anyhow::Error: From<T::Error>,
{
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::List(items) => {
                let mut res = vec![];
                for item in items {
                    let t: T = item.try_into()?;
                    res.push(t);
                }
                Ok(res)
            }
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl TryFrom<Value> for String {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Bytes(bytes) => Ok(String::from_utf8(bytes)?),
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}

impl<T> TryFrom<Value> for HashMap<String, T>
where
    T: TryFrom<Value>,
    anyhow::Error: From<T::Error>,
{
    type Error = anyhow::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Dict(entries) => {
                let mut res = HashMap::new();
                for (key, val) in entries {
                    let key = String::from_utf8(key)?;
                    let val: T = val.try_into()?;
                    res.insert(key, val);
                }
                Ok(res)
            }
            _ => Err(anyhow!("decoded value had unexpected type: {:?}", value).into()),
        }
    }
}
