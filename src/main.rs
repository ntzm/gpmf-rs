extern crate nom;

use chrono::{DateTime, TimeZone, Utc};
use img_parts::jpeg::markers::APP6;
use img_parts::jpeg::Jpeg;
use nom::bytes::complete::{take, take_while_m_n};
use nom::lib::std::fmt::Formatter;
use nom::multi::{count, many0, many_m_n};
use nom::number::complete::{
    be_f32, be_f64, be_i16, be_i32, be_i64, be_i8, be_u128, be_u16, be_u32, be_u64, be_u8,
};
use nom::sequence::tuple;
use nom::{IResult, Offset};

// todo: multiple axis sensor data https://github.com/gopro/gpmf-parser#multiple-axis-sensor-data
//       for more data types
// todo: typedef/complex https://github.com/gopro/gpmf-parser#modifiers-supported
// todo: Q numbers
// todo: make type P in KP instead of Vec<Type>
// todo: read MP4
// todo: move extraction logic to different library

#[derive(Debug, PartialEq)]
struct KP<'a>(&'a [u8], Vec<Type<'a>>);

impl KP<'_> {
    fn pretty_print(&self, depth: usize) {
        println!();

        println!(
            "{}{}",
            " ".repeat(depth),
            std::str::from_utf8(self.0).unwrap()
        );

        for t in &self.1 {
            match t {
                Type::Nested(pairs) => {
                    for p in pairs {
                        p.pretty_print(depth + 1);
                    }
                }
                _ => print!("{}{:?}", " ".repeat(depth + 1), t),
            }
        }
    }
}

#[derive(Debug, PartialEq)]
enum Type<'a> {
    SignedByte(i8),
    UnsignedByte(u8),
    Char(char),
    Double(f64),
    Float(f32),
    Key(&'a [u8]),
    ID(u128),
    Signed64(i64),
    Unsigned64(u64),
    Signed32(i32),
    Unsigned32(u32),
    Q32, // todo
    Q64, // todo
    Signed16(i16),
    Unsigned16(u16),
    DateTime(DateTime<Utc>),
    Nested(Vec<KP<'a>>),
    Multi(Vec<Type<'a>>), // is this the best way to handle multiple values?
    Complex,              // todo
}

fn key(i: &[u8]) -> IResult<&[u8], &[u8]> {
    take(4u8)(i)
}

fn typ(i: &[u8]) -> IResult<&[u8], u8> {
    be_u8(i)
}

fn padding(i: &[u8], offset: usize) -> IResult<&[u8], &[u8]> {
    let mut remaining = 4 - offset % 4;

    // todo: probably a better way of doing this
    if remaining == 4 {
        remaining = 0;
    }

    take_while_m_n(remaining, remaining, |b| b == b'\0')(i)
}

fn size(i: &[u8]) -> IResult<&[u8], u8> {
    be_u8(i)
}

fn repeat(i: &[u8]) -> IResult<&[u8], u16> {
    be_u16(i)
}

fn val(i: &[u8], t: u8, size: u8) -> IResult<&[u8], Type> {
    Ok(match t {
        b'b' if size == 1 => {
            let (i, v) = be_i8(i)?;
            (i, Type::SignedByte(v))
        }
        b'B' if size == 1 => {
            let (i, v) = be_u8(i)?;
            (i, Type::UnsignedByte(v))
        }
        b'c' if size == 1 => {
            let (i, v) = be_u8(i)?;
            (i, Type::Char(v as char))
        }
        b'c' => {
            let (i, v) = many_m_n(size as usize, size as usize, be_u8)(i)?;
            (
                i,
                Type::Multi(v.into_iter().map(|v| Type::Char(v as char)).collect()),
            )
        }
        b'd' if size == 8 => {
            let (i, v) = be_f64(i)?;
            (i, Type::Double(v))
        }
        b'f' if size == 4 => {
            let (i, v) = be_f32(i)?;
            (i, Type::Float(v))
        }
        b'f' => {
            let (i, v) = many_m_n(size as usize / 4, size as usize / 4, be_f32)(i)?;
            (i, Type::Multi(v.into_iter().map(Type::Float).collect()))
        }
        b'F' if size == 4 => {
            let (i, v) = take(4u8)(i)?;
            (i, Type::Key(v))
        }
        b'G' => {
            let (i, v) = be_u128(i)?;
            (i, Type::ID(v))
        } // todo
        b'j' if size == 8 => {
            let (i, v) = be_i64(i)?;
            (i, Type::Signed64(v))
        }
        b'J' if size == 8 => {
            let (i, v) = be_u64(i)?;
            (i, Type::Unsigned64(v))
        }
        b'l' if size == 4 => {
            let (i, v) = be_i32(i)?;
            (i, Type::Signed32(v))
        }
        b'l' => {
            let (i, v) = many_m_n(size as usize / 4, size as usize / 4, be_i32)(i)?;
            (i, Type::Multi(v.into_iter().map(Type::Signed32).collect()))
        }
        b'L' if size == 4 => {
            let (i, v) = be_u32(i)?;
            (i, Type::Unsigned32(v))
        }
        b'q' => {
            println!("{} {:?}", size, i);
            (i, Type::Q32)
        } // todo
        b'Q' => {
            println!("{} {:?}", size, i);
            (i, Type::Q64)
        } // todo
        b's' if size == 2 => {
            let (i, v) = be_i16(i)?;
            (i, Type::Signed16(v))
        }
        b's' => {
            let (i, v) = many_m_n(size as usize / 2, size as usize / 2, be_i16)(i)?;
            (i, Type::Multi(v.into_iter().map(Type::Signed16).collect()))
        }
        b'S' if size == 2 => {
            let (i, v) = be_u16(i)?;
            (i, Type::Unsigned16(v))
        }
        b'U' if size == 16 => {
            let (i, v) = take(16u8)(i)?;
            let dt = Utc
                .datetime_from_str(std::str::from_utf8(v).unwrap(), "%y%m%d%H%M%S%.3f")
                .unwrap();
            (i, Type::DateTime(dt))
        }
        b'\0' => {
            let (i, v) = parse(i)?;
            (i, Type::Nested(v))
        }
        b'?' => {
            // skip complex for now
            let (i, _) = take(size)(i)?;
            (i, Type::Complex)
        } // todo
        _ => panic!(format!("Unknown type {} with size {}", t as char, size)),
    })
}

// format:
// key (four ASCII chars (u8))
//   can be anything
// type (one char)
//   see `Type` enum
// size (unsigned 8bit int)
//   if size does not match the size of the type (e.g. 4 bytes for a 16 bit int), then there are multiple
//   samples (e.g. 2 lots of 16 bit ints)
// repeat (unsigned 16bit int)
//   how many times data of `size` length is repeated
// data (type of `type`, length of `size x repeat`)
// padding (pads with null bytes to nearest 32 bits)

fn kv(inp: &[u8]) -> IResult<&[u8], KP> {
    let (i, (key, typ, size, repeat)) = tuple((key, typ, size, repeat))(inp)?;
    let (i, v) = count(|i| val(i, typ, size), repeat as usize)(i)?;
    let (i, _) = padding(i, inp.offset(i))?;

    Ok((i, KP(key, v)))
}

fn parse(i: &[u8]) -> IResult<&[u8], Vec<KP>> {
    many0(kv)(i)
}

#[derive(Debug)]
enum JpgExtractError {
    Io(std::io::Error),
    FromBytes(img_parts::Error),
    MissingApp6,
    InvalidApp6,
}

impl std::error::Error for JpgExtractError {}

impl std::fmt::Display for JpgExtractError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            JpgExtractError::Io(e) => e.fmt(f),
            JpgExtractError::FromBytes(e) => e.fmt(f),
            JpgExtractError::MissingApp6 => write!(f, "Missing APP6"),
            JpgExtractError::InvalidApp6 => write!(f, "Invalid APP6"),
        }
    }
}

impl From<img_parts::Error> for JpgExtractError {
    fn from(e: img_parts::Error) -> Self {
        JpgExtractError::FromBytes(e)
    }
}

impl From<std::io::Error> for JpgExtractError {
    fn from(e: std::io::Error) -> Self {
        JpgExtractError::Io(e)
    }
}

fn extract_from_jpg<P: AsRef<std::path::Path>>(path: P) -> Result<Vec<u8>, JpgExtractError> {
    let input = std::fs::read(path)?;
    let jpg = Jpeg::from_bytes(input.into())?;
    let bytes = jpg
        .segment_by_marker(APP6)
        .ok_or(JpgExtractError::MissingApp6)?
        .contents();

    if &bytes[..6] != b"GoPro\0" {
        return Err(JpgExtractError::InvalidApp6);
    }

    Ok(bytes[6..].to_owned())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let b = extract_from_jpg(args.get(1).unwrap()).unwrap();

    let (_, pairs) = parse(&b).unwrap();

    for p in pairs {
        p.pretty_print(0);
    }
}

#[cfg(test)]
mod tests {
    use crate::{parse, Type, KP};
    use chrono::{TimeZone, Utc};

    #[test]
    fn it_reads_empty() {
        assert_eq!(parse(&b""[..]), Ok((&b""[..], vec![])))
    }

    #[test]
    fn it_reads_signed_byte() {
        assert_eq!(
            parse(&b"DEMOb\x01\x00\x01\xf2\0\0\0"[..]),
            Ok((
                &b""[..],
                vec![KP(&b"DEMO"[..], vec![Type::SignedByte(-14i8)])]
            ))
        )
    }

    #[test]
    fn it_reads_unsigned_byte() {
        assert_eq!(
            parse(&b"DEMOB\x01\x00\x01\xff\0\0\0"[..]),
            Ok((
                &b""[..],
                vec![KP(&b"DEMO"[..], vec![Type::UnsignedByte(255u8)])]
            ))
        )
    }

    #[test]
    fn it_reads_char() {
        assert_eq!(
            parse(&b"DEMOc\x01\x00\x01a\0\0\0"[..]),
            Ok((&b""[..], vec![KP(&b"DEMO"[..], vec![Type::Char('a')])]))
        )
    }

    #[test]
    fn it_reads_date_time() {
        assert_eq!(
            parse(&b"DEMOU\x10\x00\x01210309140223.123"[..]),
            Ok((
                &b""[..],
                vec![KP(
                    &b"DEMO"[..],
                    vec![Type::DateTime(
                        Utc.ymd(2021, 3, 9).and_hms_milli(14, 2, 23, 123)
                    )]
                )]
            ))
        )
    }

    #[test]
    fn it_reads_multiple_axes() {
        assert_eq!(
            parse(&b"GYROs\x06\x00\x01\xf1\xe7\xf6\x1a\xfa\xcc\0\0"[..]),
            Ok((
                &b""[..],
                vec![KP(
                    &b"GYRO"[..],
                    vec![Type::Multi(vec![
                        Type::Signed16(-3609),
                        Type::Signed16(-2534),
                        Type::Signed16(-1332)
                    ])]
                )]
            ))
        )
    }
}
