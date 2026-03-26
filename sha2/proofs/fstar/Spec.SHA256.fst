module Spec.SHA256

(**
  SHA-256 Specification following NIST FIPS 180-4
  
  This specification closely mirrors the structure of FIPS 180-4:
  - Section 4.1.2: SHA-256 Functions
  - Section 4.2.2: SHA-256 Constants  
  - Section 5.3.3: SHA-256 Initial Hash Value
  - Section 6.2.2: SHA-256 Hash Computation
  
  Reference: https://doi.org/10.6028/NIST.FIPS.180-4
*)

open FStar.Mul
open FStar.Seq

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(** ============================================================================
    Types and Notation (FIPS 180-4, Section 2)
    ============================================================================ *)

(** A word for SHA-256 is a 32-bit unsigned integer *)
let word = U32.t

(** Word addition modulo 2^32 (FIPS 180-4, Section 2.2.1) *)
let ( +. ) (x y: word) : word = U32.add_mod x y

(** Bitwise AND *)
let ( &. ) (x y: word) : word = U32.logand x y

(** Bitwise OR *)
let ( |. ) (x y: word) : word = U32.logor x y

(** Bitwise XOR *)
let ( ^. ) (x y: word) : word = U32.logxor x y

(** Bitwise complement *)
let ( ~. ) (x: word) : word = U32.lognot x

(** Right shift by n bits (FIPS 180-4, Section 2.2.2: SHR^n(x)) *)
let shr (n: U32.t{U32.v n < 32}) (x: word) : word = U32.shift_right x n

(** Circular right rotation by n bits (FIPS 180-4, Section 2.2.2: ROTR^n(x)) *)
let rotr (n: U32.t{0 < U32.v n /\ U32.v n < 32}) (x: word) : word = 
  (U32.shift_right x n) |. (U32.shift_left x (U32.sub 32ul n))

(** ============================================================================
    Type Definitions
    ============================================================================ *)

(** Hash state is 8 words: H_0^(0), H_1^(0), ..., H_7^(0) *)
let hash_state = s:seq word{Seq.length s = 8}

(** A message block is 16 words = 64 bytes = 512 bits *)
let block = b:seq word{Seq.length b = 16}

(** A message schedule is 64 words *)
let message_schedule = w:seq word{Seq.length w = 64}

(** Working variables: a, b, c, d, e, f, g, h *)
let working_vars = v:seq word{Seq.length v = 8}

(** ============================================================================
    SHA-256 Constants (FIPS 180-4, Section 4.2.2)
    
    These words represent the first thirty-two bits of the fractional parts 
    of the cube roots of the first sixty-four prime numbers.
    ============================================================================ *)

[@"opaque_to_smt"]
let k: s:seq word{Seq.length s = 64} =
  [@inline_let]
  let l = [
    0x428a2f98ul; 0x71374491ul; 0xb5c0fbcful; 0xe9b5dba5ul;
    0x3956c25bul; 0x59f111f1ul; 0x923f82a4ul; 0xab1c5ed5ul;
    0xd807aa98ul; 0x12835b01ul; 0x243185beul; 0x550c7dc3ul;
    0x72be5d74ul; 0x80deb1feul; 0x9bdc06a7ul; 0xc19bf174ul;
    0xe49b69c1ul; 0xefbe4786ul; 0x0fc19dc6ul; 0x240ca1ccul;
    0x2de92c6ful; 0x4a7484aaul; 0x5cb0a9dcul; 0x76f988daul;
    0x983e5152ul; 0xa831c66dul; 0xb00327c8ul; 0xbf597fc7ul;
    0xc6e00bf3ul; 0xd5a79147ul; 0x06ca6351ul; 0x14292967ul;
    0x27b70a85ul; 0x2e1b2138ul; 0x4d2c6dfcul; 0x53380d13ul;
    0x650a7354ul; 0x766a0abbul; 0x81c2c92eul; 0x92722c85ul;
    0xa2bfe8a1ul; 0xa81a664bul; 0xc24b8b70ul; 0xc76c51a3ul;
    0xd192e819ul; 0xd6990624ul; 0xf40e3585ul; 0x106aa070ul;
    0x19a4c116ul; 0x1e376c08ul; 0x2748774cul; 0x34b0bcb5ul;
    0x391c0cb3ul; 0x4ed8aa4aul; 0x5b9cca4ful; 0x682e6ff3ul;
    0x748f82eeul; 0x78a5636ful; 0x84c87814ul; 0x8cc70208ul;
    0x90befffaul; 0xa4506cebul; 0xbef9a3f7ul; 0xc67178f2ul
  ] in
  assert_norm (List.Tot.length l = 64);
  Seq.seq_of_list l

(** ============================================================================
    SHA-256 Initial Hash Value (FIPS 180-4, Section 5.3.3)
    
    These words were obtained by taking the first thirty-two bits of the 
    fractional parts of the square roots of the first eight prime numbers.
    ============================================================================ *)

[@"opaque_to_smt"]
let h_init: hash_state =
  [@inline_let]
  let l = [
    0x6a09e667ul;  (* H_0^(0) *)
    0xbb67ae85ul;  (* H_1^(0) *)
    0x3c6ef372ul;  (* H_2^(0) *)
    0xa54ff53aul;  (* H_3^(0) *)
    0x510e527ful;  (* H_4^(0) *)
    0x9b05688cul;  (* H_5^(0) *)
    0x1f83d9abul;  (* H_6^(0) *)
    0x5be0cd19ul   (* H_7^(0) *)
  ] in
  assert_norm (List.Tot.length l = 8);
  Seq.seq_of_list l

(** ============================================================================
    SHA-256 Functions (FIPS 180-4, Section 4.1.2)
    ============================================================================ *)

(** Ch(x, y, z) = (x AND y) XOR ((NOT x) AND z) *)
let ch (x y z: word) : word = (x &. y) ^. ((~. x) &. z)

(** Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) *)
let maj (x y z: word) : word = (x &. y) ^. (x &. z) ^. (y &. z)

(** SIGMA_0^{256}(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x) *)
let sigma_0 (x: word) : word = (rotr 2ul x) ^. (rotr 13ul x) ^. (rotr 22ul x)

(** SIGMA_1^{256}(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) *)
let sigma_1 (x: word) : word = (rotr 6ul x) ^. (rotr 11ul x) ^. (rotr 25ul x)

(** sigma_0^{256}(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) *)
let lsigma_0 (x: word) : word = (rotr 7ul x) ^. (rotr 18ul x) ^. (shr 3ul x)

(** sigma_1^{256}(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) *)
let lsigma_1 (x: word) : word = (rotr 17ul x) ^. (rotr 19ul x) ^. (shr 10ul x)

(** ============================================================================
    Message Schedule (FIPS 180-4, Section 6.2.2, Step 1)
    
    W_t = M_t^(i)                                                    for  0 <= t <= 15
    W_t = sigma_1(W_{t-2}) + W_{t-7} + sigma_0(W_{t-15}) + W_{t-16}  for 16 <= t <= 63
    ============================================================================ *)

(** Compute one word of the message schedule for t >= 16 *)
let ws_step (w: seq word) (t: nat{16 <= t /\ t < 64 /\ t <= Seq.length w}) : word =
  let w_t_2  = Seq.index w (t - 2) in
  let w_t_7  = Seq.index w (t - 7) in
  let w_t_15 = Seq.index w (t - 15) in
  let w_t_16 = Seq.index w (t - 16) in
  (lsigma_1 w_t_2) +. w_t_7 +. (lsigma_0 w_t_15) +. w_t_16

(** Build the message schedule from a message block.
    For t = 0..15: W_t = M_t
    For t = 16..63: W_t = sigma_1(W_{t-2}) + W_{t-7} + sigma_0(W_{t-15}) + W_{t-16} *)
let rec ws_aux (m: block) (t: nat{t <= 64}) : w:seq word{Seq.length w = t} =
  if t = 0 then Seq.empty
  else if t <= 16 then
    (* For t <= 16, take the first t words from the message block *)
    Seq.slice m 0 t
  else begin
    let w_prev = ws_aux m (t - 1) in
    let w_new = ws_step w_prev (t - 1) in
    Seq.snoc w_prev w_new
  end

let ws (m: block) : message_schedule = ws_aux m 64

(** ============================================================================
    SHA-256 Compression Function (FIPS 180-4, Section 6.2.2, Steps 2-4)
    ============================================================================ *)

(** Extract all working variables from sequence *)
let get_vars (v: working_vars) : (word & word & word & word & word & word & word & word) =
  (Seq.index v 0, Seq.index v 1, Seq.index v 2, Seq.index v 3,
   Seq.index v 4, Seq.index v 5, Seq.index v 6, Seq.index v 7)

(** One round of the compression function (FIPS 180-4, Section 6.2.2, Step 3)

    T_1 = h + SIGMA_1(e) + Ch(e,f,g) + K_t + W_t
    T_2 = SIGMA_0(a) + Maj(a,b,c)
    h = g
    g = f
    f = e
    e = d + T_1
    d = c
    c = b
    b = a
    a = T_1 + T_2
*)
let compress_round (v: working_vars) (k_t w_t: word) : working_vars =
  let (a, b, c, d, e, f, g, h) = get_vars v in
  
  let t1 = h +. (sigma_1 e) +. (ch e f g) +. k_t +. w_t in
  let t2 = (sigma_0 a) +. (maj a b c) in
  
  let l = [
    t1 +. t2;  (* new a *)
    a;         (* new b *)
    b;         (* new c *)
    c;         (* new d *)
    d +. t1;   (* new e *)
    e;         (* new f *)
    f;         (* new g *)
    g          (* new h *)
  ] in
  assert_norm (List.Tot.length l = 8);
  Seq.seq_of_list l

(** Run all 64 rounds of the compression function (Step 3) *)
let rec compress_rounds (v: working_vars) (ws: message_schedule) (t: nat{t <= 64}) 
  : working_vars =
  if t = 0 then v
  else
    let v' = compress_rounds v ws (t - 1) in
    let k_t = Seq.index k (t - 1) in
    let w_t = Seq.index ws (t - 1) in
    compress_round v' k_t w_t

(** Add working variables to intermediate hash (Step 4)
    H_0^(i) = a + H_0^(i-1)
    H_1^(i) = b + H_1^(i-1)
    ...
    H_7^(i) = h + H_7^(i-1)
*)
let add_hash (h: hash_state) (v: working_vars) : hash_state =
  let l = [
    (Seq.index h 0) +. (Seq.index v 0);
    (Seq.index h 1) +. (Seq.index v 1);
    (Seq.index h 2) +. (Seq.index v 2);
    (Seq.index h 3) +. (Seq.index v 3);
    (Seq.index h 4) +. (Seq.index v 4);
    (Seq.index h 5) +. (Seq.index v 5);
    (Seq.index h 6) +. (Seq.index v 6);
    (Seq.index h 7) +. (Seq.index v 7)
  ] in
  assert_norm (List.Tot.length l = 8);
  Seq.seq_of_list l

(** Process one message block (FIPS 180-4, Section 6.2.2)
    1. Prepare the message schedule W
    2. Initialize working variables a,b,c,d,e,f,g,h with previous hash
    3. Run 64 rounds
    4. Compute new intermediate hash value
*)
let compress (h: hash_state) (m: block) : hash_state =
  let w = ws m in                        (* Step 1: Message schedule *)
  let v = compress_rounds h w 64 in      (* Steps 2-3: Initialize and run rounds *)
  add_hash h v                           (* Step 4: Add to hash *)

(** ============================================================================
    Message Padding (FIPS 180-4, Section 5.1.1)
    
    Suppose the length of the message M is l bits. Append bit "1" to the end,
    then k zero bits where k is the smallest non-negative solution to:
      l + 1 + k = 448 (mod 512)
    Then append the 64-bit block that is equal to l expressed as binary.
    ============================================================================ *)

(** Pad message according to FIPS 180-4 Section 5.1.1 *)
let pad_message (msg: seq U8.t{Seq.length msg < pow2 61})
  : s:seq U8.t{Seq.length s % 64 = 0 /\ Seq.length s > 0} =
  let msg_len = Seq.length msg in
  let msg_bits = msg_len * 8 in
  
  (* Calculate padding: message + 0x80 + zeros + 8-byte length *)
  let after_one = msg_len + 1 in (* message + the 0x80 byte *)
  let remainder = after_one % 64 in
  let padding_zeros = 
    if remainder <= 56 then 56 - remainder
    else (64 + 56) - remainder
  in
  let padded_len = after_one + padding_zeros + 8 in
  
  (* Build padded message *)
  Seq.init padded_len (fun i ->
    if i < msg_len then Seq.index msg i
    else if i = msg_len then 0x80uy (* append bit "1" as 0x80 byte *)
    else if i < msg_len + 1 + padding_zeros then 0x00uy (* zeros *)
    else (* last 8 bytes: message length in bits as big-endian u64 *)
      let offset = i - (msg_len + 1 + padding_zeros) in
      U8.uint_to_t ((msg_bits / (pow2 ((7 - offset) * 8))) % 256)
  )

(** Convert 8 bytes to a word (big-endian) *)
let bytes_to_word (b: seq U8.t{Seq.length b = 4}) : word =
  let open U8 in
  let b0 = U32.uint_to_t (v (Seq.index b 0)) in
  let b1 = U32.uint_to_t (v (Seq.index b 1)) in
  let b2 = U32.uint_to_t (v (Seq.index b 2)) in
  let b3 = U32.uint_to_t (v (Seq.index b 3)) in
  U32.logor (U32.shift_left b0 24ul)
    (U32.logor (U32.shift_left b1 16ul)
      (U32.logor (U32.shift_left b2 8ul) b3))

(** Convert a word to 4 bytes (big-endian) *)
let word_to_bytes (w: word) : s:seq U8.t{Seq.length s = 4} =
  let open U8 in
  Seq.seq_of_list [
    uint_to_t (U32.v (U32.shift_right w 24ul) % 256);
    uint_to_t (U32.v (U32.shift_right w 16ul) % 256);
    uint_to_t (U32.v (U32.shift_right w 8ul) % 256);
    uint_to_t (U32.v w % 256)
  ]

(** Convert 64 bytes to a block of 16 words (big-endian) *)
let bytes_to_block (b: seq U8.t{Seq.length b = 64}) : block =
  let word_at (i: nat{i < 16}) : word =
    bytes_to_word (Seq.slice b (4 * i) (4 * i + 4))
  in
  Seq.init 16 word_at

(** Convert hash state (8 words) to 32 bytes (big-endian) - helper *)
let rec hash_to_bytes_aux (h: hash_state) (i: nat{i <= 8}) 
  : Tot (s:seq U8.t{Seq.length s = 4 * i}) (decreases i) =
  if i = 0 then Seq.empty
  else Seq.append (hash_to_bytes_aux h (i - 1)) (word_to_bytes (Seq.index h (i - 1)))

(** Convert hash state (8 words) to 32 bytes (big-endian) *)
let hash_to_bytes (h: hash_state) : s:seq U8.t{Seq.length s = 32} =
  hash_to_bytes_aux h 8

(** ============================================================================
    High-Level SHA-256 Hash Function (FIPS 180-4, Section 6.2)
    
    This is the main specification function that computes SHA-256 hash.
    It processes the message in 512-bit (64-byte) blocks after padding.
    ============================================================================ *)

(** Process multiple blocks *)
let rec hash_blocks (h: hash_state) (blocks: seq block) 
  : Tot hash_state (decreases (Seq.length blocks)) =
  if Seq.length blocks = 0 then h
  else
    let h' = compress h (Seq.head blocks) in
    hash_blocks h' (Seq.tail blocks)

(** SHA-256 hash function
    
    Takes arbitrary-length byte sequence (up to 2^61 bytes = 2^64 bits)
    and returns 32-byte hash.
    
    Automatically pads the message according to FIPS 180-4 Section 5.1.1.
*)
let sha256 (msg: seq U8.t{Seq.length msg < pow2 61}) 
  : s:seq U8.t{Seq.length s = 32} =
  let padded_msg = pad_message msg in
  let num_blocks = Seq.length padded_msg / 64 in
  let blocks = Seq.init num_blocks (fun i -> 
    bytes_to_block (Seq.slice padded_msg (i * 64) (i * 64 + 64))
  ) in
  let final_hash = hash_blocks h_init blocks in
  hash_to_bytes final_hash
