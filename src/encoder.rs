use crate::types::{OscBundle, OscPacket, OscType, Result};

use byteorder::{BigEndian, ByteOrder};

use byteorder::{WriteBytesExt};

/// Takes a reference to an OSC packet and returns
/// a byte vector on success. If the packet was invalid
/// an `OscError` is returned.
///
/// # Example
///
/// ```
/// use rosc::{OscPacket,OscMessage,OscType};
/// use rosc::encoder;
///
/// let packet = OscPacket::Message(OscMessage{
///         addr: "/greet/me".to_string(),
///         args: vec![OscType::String("hi!".to_string())]
///     }
/// );
/// assert!(encoder::encode(&packet).is_ok())
/// ```
pub fn encode(packet: &OscPacket) -> Result<Vec<u8>> {
    match *packet {
        OscPacket::Message(ref msg) => encode_message(&msg.addr, &msg.args),
        OscPacket::Bundle(ref bundle) => encode_bundle(bundle),
    }
}

pub fn encode_message(addr: &str, args: &[OscType]) -> Result<Vec<u8>> {
    let mut msg_bytes: Vec<u8> = Vec::new();

    msg_bytes.extend(addr.as_bytes());
    msg_bytes.push(0u8);
    pad_bytes(&mut msg_bytes);
    msg_bytes.push(b',');
    let mut arg_bytes: Vec<u8> = Vec::new();

    for arg in args {
        encode_arg_to_vecs(arg, &mut msg_bytes, &mut arg_bytes)?;
    }

    msg_bytes.push(0u8);
    pad_bytes(&mut msg_bytes);

    msg_bytes.extend(arg_bytes);
    
    Ok(msg_bytes)
}

fn encode_bundle(bundle: &OscBundle) -> Result<Vec<u8>> {
    let mut bundle_bytes: Vec<u8> = Vec::new();
    bundle_bytes.extend(encode_string("#bundle".to_string()).into_iter());

    let (x, y) = bundle.timetag;
    bundle_bytes.extend(encode_time_tag(x, y));


    if bundle.content.is_empty() {
        return Ok(bundle_bytes);
    }

    for packet in &bundle.content {
        match *packet {
            OscPacket::Message(ref m) => {
                let msg = encode_message(&m.addr, &m.args)?;
                let mut msg_size = vec![0u8; 4];
                BigEndian::write_u32(&mut msg_size, msg.len() as u32);
                bundle_bytes.extend(msg_size.into_iter().chain(msg.into_iter()));
            }
            OscPacket::Bundle(ref b) => {
                let bdl = encode_bundle(b)?;
                let mut bdl_size = vec![0u8; 4];
                BigEndian::write_u32(&mut bdl_size, bdl.len() as u32);
                bundle_bytes.extend(bdl_size.into_iter().chain(bdl.into_iter()));
            }
        }
    }

    Ok(bundle_bytes)
}

fn encode_arg_to_vecs(arg: &OscType, mut type_tags: &mut Vec<u8>, mut msg_bytes: &mut Vec<u8>) -> Result<()> {
    match *arg {
        OscType::Int(ref x) => {
            msg_bytes.write_i32::<BigEndian>(*x).unwrap();
            type_tags.push(b'i');
            Ok(())
        }
        OscType::Long(ref x) => {
            msg_bytes.write_i64::<BigEndian>(*x).unwrap();
            type_tags.push(b'h');
            Ok(())
        }
        OscType::Float(ref x) => {
            msg_bytes.write_f32::<BigEndian>(*x).unwrap();
            type_tags.push(b'f');
            Ok(())
        }
        OscType::Double(ref x) => {
            msg_bytes.write_f64::<BigEndian>(*x).unwrap();
            type_tags.push(b'd');
            Ok(())
        }
        OscType::Char(ref x) => {
            msg_bytes.write_u32::<BigEndian>(*x as u32).unwrap();
            type_tags.push(b'c');
            Ok(())
        }
        OscType::String(ref x) => {
            msg_bytes.extend(encode_string(x));
            type_tags.push(b's');
            Ok(())
        }
        OscType::Blob(ref x) => {
            let padded_blob_length: usize = pad(x.len() as u64) as usize;
            let mut bytes = vec![0u8; 4 + padded_blob_length];
            // write length
            BigEndian::write_i32(&mut bytes[..4], x.len() as i32);
            for (i, v) in x.iter().enumerate() {
                bytes[i + 4] = *v;
            }
            msg_bytes.extend(bytes);
            type_tags.push(b'b');
            Ok(())
        }
        OscType::Time((ref x, ref y)) => {
            msg_bytes.extend(encode_time_tag(*x, *y));
            type_tags.push(b't');
            Ok(())
        }
        OscType::Midi(ref x) => {
            msg_bytes.extend(&[x.port, x.status, x.data1, x.data2]);
            type_tags.push(b'm');
            Ok(())
        }
        OscType::Color(ref x) => {
            type_tags.push(b'r');
            msg_bytes.extend(&[x.red, x.green, x.blue, x.alpha]);
            Ok(())}
        OscType::Bool(ref x) => {
            if *x {
                type_tags.push(b'T'); Ok(())
            } else {
                type_tags.push(b'F'); Ok(())
            }
        }
        OscType::Nil => {type_tags.push(b'N'); Ok(())},
        OscType::Inf => {type_tags.push(b'I'); Ok(())},
        OscType::Array(ref x) => {
            type_tags.push(b'[');
            for v in x.content.iter() {
                encode_arg_to_vecs(v, &mut type_tags, &mut msg_bytes)?
            }
            type_tags.push(b']');
            Ok(())
        }
    }
}

/// Null terminates the byte representation of string `s` and
/// adds null bytes until the length of the result is a
/// multiple of 4.
pub fn encode_string<S: Into<String>>(s: S) -> Vec<u8> {
    let mut bytes: Vec<u8> = s.into().as_bytes().into();
    bytes.push(0u8);
    pad_bytes(&mut bytes);
    bytes
}

fn pad_bytes(bytes: &mut Vec<u8>) {
    let padded_length = pad(bytes.len() as u64);
    while bytes.len() < padded_length as usize {
        bytes.push(0u8)
    }
}

/// Returns the position padded to 4 bytes.
///
/// # Example
///
/// ```
/// use rosc::encoder;
///
/// let pos: u64 = 10;
/// assert_eq!(12u64, encoder::pad(pos))
/// ```
pub fn pad(pos: u64) -> u64 {
    match pos % 4 {
        0 => pos,
        d => pos + (4 - d),
    }
}

fn encode_time_tag(sec: u32, frac: u32) -> Vec<u8> {
    let mut bytes = vec![0u8; 8];
    BigEndian::write_u32(&mut bytes[..4], sec);
    BigEndian::write_u32(&mut bytes[4..], frac);
    bytes
}

#[test]
fn test_pad() {
    assert_eq!(4, pad(4));
    assert_eq!(8, pad(5));
    assert_eq!(8, pad(6));
    assert_eq!(8, pad(7));
}
