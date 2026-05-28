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

/// Raw SHA-256 compression function (hazmat).
///
/// Applies the SHA-256 compression function to the 32-bit `state` for each
/// 64-byte block in `blocks`, updating `state` in place. This is the bare
/// FIPS 180-4 Sec. 6.2 transformation, with no padding, length encoding, or
/// finalisation.
///
/// # Contract
///
/// Callers are responsible for the parts of SHA-256 that this function does
/// *not* perform:
///
/// * Padding the input per FIPS 180-4 Sec. 5.1.1 (append `0x80`, zero-fill
///   to a 56-mod-64-byte boundary, append the 64-bit big-endian bit length).
/// * Splitting the padded message into 64-byte blocks before calling.
/// * Initialising `state` to the SHA-256 IV `H0_256` (or to a midstream value
///   from a previous call) before the first invocation.
/// * Emitting the final digest as the big-endian byte serialisation of
///   `state` after the last call.
///
/// Misuse (skipped padding, wrong IV, etc.) silently produces a non-FIPS
/// output. The verification proofs target [`crate::sha256`] etc., which
/// internally do all of the above and call this function as a building block.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "compress")] {
/// // A correctly padded one-block message ("abc" with FIPS padding):
/// let mut block = [0u8; 64];
/// block[..3].copy_from_slice(b"abc");
/// block[3] = 0x80;
/// block[63] = 24; // 24-bit message length
/// let mut state = [
///     0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
///     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
/// ];
/// sha2::compress256(&mut state, &[block]);
/// assert_eq!(state[0], 0xba7816bf);
/// # }
/// ```
#[cfg_attr(not(feature = "compress"), allow(unreachable_pub))]
pub fn compress256(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    compress(state, blocks)
}
