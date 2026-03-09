#[path = "sha512/soft/compact.rs"]
mod soft_compact;
use soft_compact::compress;

#[inline(always)]
fn to_u64s(block: &[u8; 128]) -> [u64; 16] {
    core::array::from_fn(|i| {
        let chunk = block[8 * i..][..8].try_into().unwrap();
        u64::from_be_bytes(chunk)
    })
}

/// Raw SHA-512 compression function.
///
/// This is a low-level "hazmat" API which provides direct access to the core
/// functionality of SHA-512.
pub(crate) fn compress512(state: &mut [u64; 8], blocks: &[[u8; 128]]) {
    compress(state, blocks)
}
