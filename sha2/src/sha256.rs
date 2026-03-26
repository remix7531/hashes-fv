#[path = "sha256/soft/compact.rs"]
mod soft_compact;
use soft_compact::compress;

#[inline(always)]
fn to_u32s(block: &[u8; 64]) -> [u32; 16] {
    core::array::from_fn(|i| {
        let chunk = block[4 * i..][..4].try_into().unwrap();
        u32::from_be_bytes(chunk)
    })
}

/// Raw SHA-256 compression function.
///
/// This is a low-level "hazmat" API which provides direct access to the core
/// functionality of SHA-256.
#[cfg_attr(not(feature = "compress"), allow(unreachable_pub))]
pub fn compress256(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    compress(state, blocks)
}
