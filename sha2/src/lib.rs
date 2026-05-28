#![no_std]
#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs, unreachable_pub)]
#![allow(clippy::needless_range_loop)]

#[rustfmt::skip]
mod consts;

#[cfg(any(feature = "sha256", feature = "sha256_224"))]
mod sha256;

#[cfg(all(feature = "compress", any(feature = "sha256", feature = "sha256_224")))]
#[cfg_attr(docsrs, doc(cfg(feature = "compress")))]
pub use sha256::compress256;

#[cfg(any(
    feature = "sha512",
    feature = "sha512_224",
    feature = "sha512_256",
    feature = "sha512_384"
))]
mod sha512;

#[cfg(all(
    feature = "compress",
    any(
        feature = "sha512",
        feature = "sha512_224",
        feature = "sha512_256",
        feature = "sha512_384"
    )
))]
#[cfg_attr(docsrs, doc(cfg(feature = "compress")))]
pub use sha512::compress512;

// ---------------------------------------------------------------------------
// Inner helpers
// ---------------------------------------------------------------------------

#[cfg(any(feature = "sha256", feature = "sha256_224"))]
fn sha256_inner(iv: [u32; 8], data: &[u8]) -> [u8; 32] {
    let mut state = iv;
    let blocks: usize = data.len() >> 6;
    let remaining: usize = data.len() & 63;

    // Process complete blocks
    for i in 0..blocks {
        let block: &[u8; 64] = data[i * 64..][..64].try_into().unwrap();
        sha256::compress256(&mut state, &[*block]);
    }

    // Process final block with padding
    let total_bits = (data.len() as u64) << 3;
    let mut final_block: [u8; 64] = [0u8; 64];
    final_block[..remaining].copy_from_slice(&data[blocks * 64..]);
    final_block[remaining] = 0x80;

    // If we don't have room for the length, we need two blocks
    if remaining >= 56 {
        sha256::compress256(&mut state, &[final_block]);
        final_block = [0u8; 64];
    }

    // Append length in bits as big-endian u64
    final_block[56..64].copy_from_slice(&total_bits.to_be_bytes());
    sha256::compress256(&mut state, &[final_block]);

    // Convert state to output bytes
    let mut out = [0u8; 32];
    for i in 0..8 {
        let bytes = state[i].to_be_bytes();
        out[i * 4] = bytes[0];
        out[i * 4 + 1] = bytes[1];
        out[i * 4 + 2] = bytes[2];
        out[i * 4 + 3] = bytes[3];
    }
    out
}

#[cfg(any(
    feature = "sha512",
    feature = "sha512_224",
    feature = "sha512_256",
    feature = "sha512_384"
))]
fn sha512_inner(iv: [u64; 8], data: &[u8]) -> [u8; 64] {
    let mut state = iv;
    let blocks: usize = data.len() >> 7;
    let remaining: usize = data.len() & 127;

    // Process complete blocks
    for i in 0..blocks {
        let block: &[u8; 128] = data[i * 128..][..128].try_into().unwrap();
        sha512::compress512(&mut state, &[*block]);
    }

    // Process final block with padding
    let total_bits = (data.len() as u128) << 3;
    let mut final_block: [u8; 128] = [0u8; 128];
    final_block[..remaining].copy_from_slice(&data[blocks * 128..]);
    final_block[remaining] = 0x80;

    // If we don't have room for the length, we need two blocks
    if remaining >= 112 {
        sha512::compress512(&mut state, &[final_block]);
        final_block = [0u8; 128];
    }

    // Append length in bits as big-endian u128
    final_block[112..128].copy_from_slice(&total_bits.to_be_bytes());
    sha512::compress512(&mut state, &[final_block]);

    // Convert state to output bytes
    let mut out = [0u8; 64];
    for i in 0..8 {
        let bytes = state[i].to_be_bytes();
        out[i * 8] = bytes[0];
        out[i * 8 + 1] = bytes[1];
        out[i * 8 + 2] = bytes[2];
        out[i * 8 + 3] = bytes[3];
        out[i * 8 + 4] = bytes[4];
        out[i * 8 + 5] = bytes[5];
        out[i * 8 + 6] = bytes[6];
        out[i * 8 + 7] = bytes[7];
    }
    out
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compute the SHA-256 hash of `data`, returning a 32-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha256;
/// use hex_literal::hex;
///
/// let hash = sha256(b"hello world");
/// assert_eq!(hash, hex!("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"));
/// ```
#[cfg(feature = "sha256")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha256")))]
#[must_use]
pub fn sha256(data: &[u8]) -> [u8; 32] {
    sha256_inner(consts::H256_256, data)
}

/// Compute the SHA-224 hash of `data`, returning a 28-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha224;
/// use hex_literal::hex;
///
/// let hash = sha224(b"abc");
/// assert_eq!(hash, hex!("23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"));
/// ```
#[cfg(feature = "sha256_224")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha256_224")))]
#[must_use]
pub fn sha224(data: &[u8]) -> [u8; 28] {
    let out = sha256_inner(consts::H256_224, data);
    out[..28].try_into().unwrap()
}

/// Compute the SHA-512 hash of `data`, returning a 64-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha512;
/// use hex_literal::hex;
///
/// let hash = sha512(b"hello world");
/// assert_eq!(hash, hex!(
///     "309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f"
///     "989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f"
/// ));
/// ```
#[cfg(feature = "sha512")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha512")))]
#[must_use]
pub fn sha512(data: &[u8]) -> [u8; 64] {
    sha512_inner(consts::H512_512, data)
}

/// Compute the SHA-512/224 hash of `data`, returning a 28-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha512_224;
/// use hex_literal::hex;
///
/// let hash = sha512_224(b"abc");
/// assert_eq!(hash, hex!("4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa"));
/// ```
#[cfg(feature = "sha512_224")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha512_224")))]
#[must_use]
pub fn sha512_224(data: &[u8]) -> [u8; 28] {
    let out = sha512_inner(consts::H512_224, data);
    out[..28].try_into().unwrap()
}

/// Compute the SHA-512/256 hash of `data`, returning a 32-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha512_256;
/// use hex_literal::hex;
///
/// let hash = sha512_256(b"abc");
/// assert_eq!(hash, hex!("53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"));
/// ```
#[cfg(feature = "sha512_256")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha512_256")))]
#[must_use]
pub fn sha512_256(data: &[u8]) -> [u8; 32] {
    let out = sha512_inner(consts::H512_256, data);
    out[..32].try_into().unwrap()
}

/// Compute the SHA-384 hash of `data`, returning a 48-byte digest.
///
/// # Examples
///
/// ```
/// use sha2::sha384;
/// use hex_literal::hex;
///
/// let hash = sha384(b"abc");
/// assert_eq!(hash, hex!(
///     "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed"
///     "8086072ba1e7cc2358baeca134c825a7"
/// ));
/// ```
#[cfg(feature = "sha512_384")]
#[cfg_attr(docsrs, doc(cfg(feature = "sha512_384")))]
#[must_use]
pub fn sha384(data: &[u8]) -> [u8; 48] {
    let out = sha512_inner(consts::H512_384, data);
    out[..48].try_into().unwrap()
}
