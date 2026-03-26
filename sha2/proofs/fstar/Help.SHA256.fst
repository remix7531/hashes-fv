module Help.SHA256

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always --query_stats"

open FStar.Mul
open FStar.Seq
open Core_models
module S = Spec.SHA256
module E = Sha2.Sha256.Soft_proof
module U32 = FStar.UInt32
module UInt = FStar.UInt
module RI = Rust_primitives.Integers

let from_uint32 = RI.from_uint32
let to_uint32 = RI.to_uint32

let lemma_3_xor_associative (#n: pos) (a b c: UInt.uint_t n)
  : Lemma (UInt.logxor #n (UInt.logxor #n a b) c == 
           UInt.logxor #n a (UInt.logxor #n b c) /\ 
           UInt.logxor #n a (UInt.logxor #n b c) == 
           UInt.logxor #n (UInt.logxor #n a b) c) =
  UInt.logxor_associative #n a b c

let lemma_3_u32_logxor_associative (a b c: U32.t)
  : Lemma (U32.logxor (U32.logxor a b) c == U32.logxor a (U32.logxor b c) /\
           U32.logxor a (U32.logxor b c) == U32.logxor (U32.logxor a b) c) =
  lemma_3_xor_associative #32 (U32.v a) (U32.v b) (U32.v c)

val lemma_ch_equiv (x y z: U32.t)
  : Lemma (to_uint32 (E.ch (from_uint32 x) (from_uint32 y) (from_uint32 z)) == S.ch x y z)

val lemma_maj_equiv (x y z: U32.t)
  : Lemma (to_uint32 (E.maj (from_uint32 x) (from_uint32 y) (from_uint32 z)) == S.maj x y z)

val lemma_sigma_0_equiv (x: U32.t)
  : Lemma (to_uint32 (E.sigma_0_ (from_uint32 x)) == S.sigma_0 x)

val lemma_sigma_1_equiv (x: U32.t)
  : Lemma (to_uint32 (E.sigma_1_ (from_uint32 x)) == S.sigma_1 x)

val lemma_lsigma_0_equiv (x: U32.t)
  : Lemma (to_uint32 (E.lsigma_0_ (from_uint32 x)) == S.lsigma_0 x)

val lemma_lsigma_1_equiv (x: U32.t)
  : Lemma (to_uint32 (E.lsigma_1_ (from_uint32 x)) == S.lsigma_1 x)
