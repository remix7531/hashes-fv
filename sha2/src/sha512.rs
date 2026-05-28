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

/// Raw SHA-512 compression function (hazmat).
///
/// Applies the SHA-512 compression function to the 64-bit `state` for each
/// 128-byte block in `blocks`, updating `state` in place. This is the bare
/// FIPS 180-4 Sec. 6.4 transformation, with no padding, length encoding, or
/// finalisation.
///
/// # Contract
///
/// Callers are responsible for the parts of SHA-512 that this function does
/// *not* perform:
///
/// * Padding the input per FIPS 180-4 Sec. 5.1.2 (append `0x80`, zero-fill
///   to a 112-mod-128-byte boundary, append the 128-bit big-endian bit
///   length).
/// * Splitting the padded message into 128-byte blocks before calling.
/// * Initialising `state` to the SHA-512 IV `H0_512` (or to a midstream
///   value from a previous call) before the first invocation.
/// * Emitting the final digest as the big-endian byte serialisation of
///   `state` after the last call.
///
/// Misuse (skipped padding, wrong IV, etc.) silently produces a non-FIPS
/// output. The verification proofs target [`crate::sha512`] etc., which
/// internally do all of the above and call this function as a building
/// block.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "compress")] {
/// // A correctly padded one-block message ("abc" with FIPS padding):
/// let mut block = [0u8; 128];
/// block[..3].copy_from_slice(b"abc");
/// block[3] = 0x80;
/// block[127] = 24; // 24-bit message length
/// let mut state = [
///     0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
///     0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
///     0x510e527fade682d1, 0x9b05688c2b3e6c1f,
///     0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
/// ];
/// sha2::compress512(&mut state, &[block]);
/// assert_eq!(state[0], 0xddaf35a193617aba);
/// # }
/// ```
#[cfg_attr(not(feature = "compress"), allow(unreachable_pub))]
pub fn compress512(state: &mut [u64; 8], blocks: &[[u8; 128]]) {
    compress(state, blocks)
}
