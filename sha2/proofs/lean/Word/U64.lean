import Extraction
import impl.SHA512
import Common.U8
import Common.U64
import Mathlib.Tactic.IntervalCases

/-!
# Type bridge: Aeneas `Std.U64` ↔ Lean core `UInt64` (SHA-512 width)

Mirrors `U32.lean` at 64-bit width.  The basic `toUInt64`/`fromUInt64`
scalar conversions live in `Common/U64.lean` (shared between SHA-256's
`u64` length-tag emit and SHA-512's state words); this module adds the
SHA-512-specific BE 8-byte decode bridge, `arrayU64ToVec` view-level
lemmas, and the `K64` / `H0_512*` constant-table equivalences against
the upstream `Impl.{K64, H0_512, H0_384, H0_512_256, H0_512_224}`.
-/

open Aeneas Aeneas.Std

/-! ## Pointwise operation preservation -/

@[simp] theorem toUInt64_xor (x y : U64) :
    toUInt64 (x ^^^ y) = toUInt64 x ^^^ toUInt64 y := rfl

@[simp] theorem toUInt64_and (x y : U64) :
    toUInt64 (x &&& y) = toUInt64 x &&& toUInt64 y := rfl

@[simp] theorem toUInt64_or (x y : U64) :
    toUInt64 (x ||| y) = toUInt64 x ||| toUInt64 y := rfl

@[simp] theorem toUInt64_not (x : U64) :
    toUInt64 (~~~ x) = ~~~ (toUInt64 x) := rfl

/-- Aeneas `wrapping_add` is `BitVec` addition; matches `UInt64.add`. -/
@[simp] theorem toUInt64_wrapping_add (x y : U64) :
    toUInt64 (UScalar.wrapping_add x y) = toUInt64 x + toUInt64 y := rfl

/-- Aeneas `rotate_right` ↔ `Impl.UInt64.rotr`.  Aeneas's `UScalar.rotate_right`
takes shift counts at the `U32` width (Rust's `u32::rotate_right(u32)` /
`u64::rotate_right(u32)` convention); the Impl side `UInt64.rotr` takes
`UInt64`. We pass the shift through `BitVec.ofNat 64 n.val` so the
two sides agree at the bit level for `0 < n < 64` (which every SHA-512
callsite — literal 1/6/7/8/14/18/19/28/34/39/41/61 — satisfies). -/
theorem toUInt64_rotate_right (x : U64) (n : U32) (hn : 0 < n.val) (hn2 : n.val < 64) :
    toUInt64 (UScalar.rotate_right x n) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) ⟨BitVec.ofNat 64 n.val⟩ := by
  apply UInt64.toBitVec_inj.mp
  unfold UScalar.rotate_right SHS.SHA512.Impl.UInt64.rotr
  show x.bv.rotateRight n.val = _
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn2]
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt, hn2]
  congr 2
  have h : (18446744073709551616 : Nat) = 64 * 288230376151711744 := by norm_num
  omega

/-! ## `Array Std.U64 N` ↔ `Vector UInt64 N` -/

@[inline] def arrayU64ToVec {N : Usize} (a : Array U64 N) : Vector UInt64 N.val :=
  ⟨(a.val.map toUInt64).toArray, by simp [a.property]⟩

@[simp] theorem arrayU64ToVec_size {N : Usize} (a : Array U64 N) :
    (arrayU64ToVec a).size = N.val := by simp [arrayU64ToVec]

/-! ## Big-endian 8-byte decode bridge -/

open SHS.SHA512 in
/-- The eight-byte BE decoder in Aeneas's stdlib equals the shift-or chain
that `Impl.beU64` materializes. -/
theorem toUInt64_from_be_bytes (a : Array U8 8#usize) :
    toUInt64 (core.num.U64.from_be_bytes a) =
      ((toUInt8 a.val[0]!).toUInt64 <<< 56) |||
      ((toUInt8 a.val[1]!).toUInt64 <<< 48) |||
      ((toUInt8 a.val[2]!).toUInt64 <<< 40) |||
      ((toUInt8 a.val[3]!).toUInt64 <<< 32) |||
      ((toUInt8 a.val[4]!).toUInt64 <<< 24) |||
      ((toUInt8 a.val[5]!).toUInt64 <<< 16) |||
      ((toUInt8 a.val[6]!).toUInt64 <<< 8) |||
      (toUInt8 a.val[7]!).toUInt64 := by
  rcases a with ⟨l, hl⟩
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    apply UInt64.toBitVec_inj.mp
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    show
      ((BitVec.cast (by simp : 64 = UScalarTy.U64.numBits)
          (BitVec.cast (by simp : 8 * [b0.bv, b1.bv, b2.bv, b3.bv,
                                         b4.bv, b5.bv, b6.bv, b7.bv].length = 64)
            (BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv,
                                  b4.bv, b5.bv, b6.bv, b7.bv])))
        : BitVec UScalarTy.U64.numBits)
        = ((⟨b0.bv⟩ : UInt8).toUInt64 <<< 56
            ||| (⟨b1.bv⟩ : UInt8).toUInt64 <<< 48
            ||| (⟨b2.bv⟩ : UInt8).toUInt64 <<< 40
            ||| (⟨b3.bv⟩ : UInt8).toUInt64 <<< 32
            ||| (⟨b4.bv⟩ : UInt8).toUInt64 <<< 24
            ||| (⟨b5.bv⟩ : UInt8).toUInt64 <<< 16
            ||| (⟨b6.bv⟩ : UInt8).toUInt64 <<< 8
            ||| (⟨b7.bv⟩ : UInt8).toUInt64).toBitVec
    have h8 : BitVec.fromLEBytes [b7.bv, b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 64 b7.bv
          ||| ((BitVec.fromLEBytes [b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 64 <<< 8) := rfl
    have h7 : BitVec.fromLEBytes [b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 56 b6.bv
          ||| ((BitVec.fromLEBytes [b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 56 <<< 8) := rfl
    have h6 : BitVec.fromLEBytes [b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 48 b5.bv
          ||| ((BitVec.fromLEBytes [b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 48 <<< 8) := rfl
    have h5 : BitVec.fromLEBytes [b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 40 b4.bv
          ||| ((BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 40 <<< 8) := rfl
    have h4 : BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 32 b3.bv
          ||| ((BitVec.fromLEBytes [b2.bv, b1.bv, b0.bv]).setWidth 32 <<< 8) := rfl
    have h3 : BitVec.fromLEBytes [b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 24 b2.bv
          ||| ((BitVec.fromLEBytes [b1.bv, b0.bv]).setWidth 24 <<< 8) := rfl
    have h2 : BitVec.fromLEBytes [b1.bv, b0.bv]
        = BitVec.setWidth 16 b1.bv
          ||| ((BitVec.fromLEBytes [b0.bv]).setWidth 16 <<< 8) := rfl
    have h1 : BitVec.fromLEBytes [b0.bv]
        = BitVec.setWidth 8 b0.bv
          ||| ((BitVec.fromLEBytes ([] : List _)).setWidth 8 <<< 8) := rfl
    have h0 : BitVec.fromLEBytes ([] : List _) = BitVec.ofNat 0 0 := rfl
    have hBE : BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv,
                                    b4.bv, b5.bv, b6.bv, b7.bv]
        = BitVec.cast (by simp)
            (BitVec.fromLEBytes [b7.bv, b6.bv, b5.bv, b4.bv,
                                  b3.bv, b2.bv, b1.bv, b0.bv]) := rfl
    simp only [hBE, h8, h7, h6, h5, h4, h3, h2, h1, h0,
      UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
    simp [BitVec.setWidth_setWidth]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases i <;> simp

open SHS.SHA512 in
/-- Corollary linking `core.num.U64.from_be_bytes` directly to
`Impl.beU64 (arrayU8ToVec block) ⟨j, hj⟩`, given that `chunk` is the
8-byte slice `[block[8j], block[8j+1], …, block[8j+7]]`.
The hypothesis is what the calling site materializes from the
`to_u64s` extracted closure. -/
theorem toUInt64_from_be_bytes_eq_beU64
    (block : Array U8 128#usize) (chunk : Array U8 8#usize)
    (j : Nat) (hj : j < 16)
    (hchunk : chunk.val = [block.val[8 * j]!, block.val[8 * j + 1]!,
                           block.val[8 * j + 2]!, block.val[8 * j + 3]!,
                           block.val[8 * j + 4]!, block.val[8 * j + 5]!,
                           block.val[8 * j + 6]!, block.val[8 * j + 7]!]) :
    toUInt64 (core.num.U64.from_be_bytes chunk) =
      Impl.beU64 (arrayU8ToVec block) ⟨j, hj⟩ := by
  rw [toUInt64_from_be_bytes, hchunk]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  unfold Impl.beU64
  have hlen : block.val.length = 128 := block.property
  have hidx : ∀ (i : Nat) (hi : i < 128),
      (arrayU8ToVec block)[i]'(by simp; omega)
        = toUInt8 (block.val[i]!) := by
    intro i hi
    show (List.map toUInt8 block.val).toArray[i]'(by simp; omega) = _
    simp [getElem!_pos, hi, hlen]
  rw [← hidx (8 * j) (by omega), ← hidx (8 * j + 1) (by omega),
      ← hidx (8 * j + 2) (by omega), ← hidx (8 * j + 3) (by omega),
      ← hidx (8 * j + 4) (by omega), ← hidx (8 * j + 5) (by omega),
      ← hidx (8 * j + 6) (by omega), ← hidx (8 * j + 7) (by omega)]
  rfl

/-! ## Vector indexing through `arrayU64ToVec` -/

@[simp] theorem arrayU64ToVec_getElem
    {N : Usize} (block : Array U64 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU64ToVec block).size := by simp [arrayU64ToVec]; omega) :
    (arrayU64ToVec block)[i]'h' =
      toUInt64 (block.val[i]'(by simpa [block.property] using h)) := by
  show ((block.val.map toUInt64).toArray)[i]'(by simpa [arrayU64ToVec] using h') = _
  simp

/-- The underlying `toList` of `arrayU64ToVec block` is `block.val.map toUInt64`. -/
@[simp] theorem arrayU64ToVec_toList {N : Usize} (block : Array U64 N) :
    (arrayU64ToVec block).toList = block.val.map toUInt64 := by
  simp [arrayU64ToVec]

/-- `getElem!`-form of `arrayU64ToVec` indexing. -/
@[simp] theorem arrayU64ToVec_getElem!
    {N : Usize} (block : Array U64 N) (i : Nat) :
    (arrayU64ToVec block).toList[i]! = toUInt64 (block.val[i]!) := by
  rw [arrayU64ToVec_toList]
  by_cases h : i < N.val
  · simp [block.property, h]
  · simp [block.property, h]; rfl

/-! ## `arrayU64ToVec` of `Array.set` (used by SHA-512 schedule writes) -/

theorem arrayU64ToVec_set_toList
    {N : Usize} (block : Array U64 N) (i : Usize) (v : U64) :
    (arrayU64ToVec (block.set i v)).toList =
      (block.val.map toUInt64).set i.val (toUInt64 v) := by
  simp [arrayU64ToVec, Aeneas.Std.Array.set, List.map_set]

theorem arrayU64ToVec_set
    {N : Usize} (block : Array U64 N) (i : Usize) (v : U64)
    (hi : i.val < (arrayU64ToVec block).size) :
    arrayU64ToVec (block.set i v) =
      (arrayU64ToVec block).set i.val (toUInt64 v) hi := by
  apply Vector.toList_inj.mp
  rw [arrayU64ToVec_set_toList, Vector.toList_set, arrayU64ToVec_toList]

/-! ## SHA-512 round-constant table equivalence -/

/-- Unfold the Aeneas-extracted `K64` constants table to a literal list. -/
private theorem sha2_K64_val :
    (Extraction.consts.K64 : Array U64 80#usize).val =
      [4794697086780616226#u64, 8158064640168781261#u64, 13096744586834688815#u64,
       16840607885511220156#u64, 4131703408338449720#u64, 6480981068601479193#u64,
       10538285296894168987#u64, 12329834152419229976#u64,
       15566598209576043074#u64, 1334009975649890238#u64, 2608012711638119052#u64,
       6128411473006802146#u64, 8268148722764581231#u64, 9286055187155687089#u64,
       11230858885718282805#u64, 13951009754708518548#u64,
       16472876342353939154#u64, 17275323862435702243#u64,
       1135362057144423861#u64, 2597628984639134821#u64, 3308224258029322869#u64,
       5365058923640841347#u64, 6679025012923562964#u64, 8573033837759648693#u64,
       10970295158949994411#u64, 12119686244451234320#u64,
       12683024718118986047#u64, 13788192230050041572#u64,
       14330467153632333762#u64, 15395433587784984357#u64, 489312712824947311#u64,
       1452737877330783856#u64, 2861767655752347644#u64, 3322285676063803686#u64,
       5560940570517711597#u64, 5996557281743188959#u64, 7280758554555802590#u64,
       8532644243296465576#u64, 9350256976987008742#u64, 10552545826968843579#u64,
       11727347734174303076#u64, 12113106623233404929#u64,
       14000437183269869457#u64, 14369950271660146224#u64,
       15101387698204529176#u64, 15463397548674623760#u64,
       17586052441742319658#u64, 1182934255886127544#u64, 1847814050463011016#u64,
       2177327727835720531#u64, 2830643537854262169#u64, 3796741975233480872#u64,
       4115178125766777443#u64, 5681478168544905931#u64, 6601373596472566643#u64,
       7507060721942968483#u64, 8399075790359081724#u64, 8693463985226723168#u64,
       9568029438360202098#u64, 10144078919501101548#u64,
       10430055236837252648#u64, 11840083180663258601#u64,
       13761210420658862357#u64, 14299343276471374635#u64,
       14566680578165727644#u64, 15097957966210449927#u64,
       16922976911328602910#u64, 17689382322260857208#u64, 500013540394364858#u64,
       748580250866718886#u64, 1242879168328830382#u64, 1977374033974150939#u64,
       2944078676154940804#u64, 3659926193048069267#u64, 4368137639120453308#u64,
       4836135668995329356#u64, 5532061633213252278#u64, 6448918945643986474#u64,
       6902733635092675308#u64, 7801388544844847127#u64] := by
  unfold Extraction.consts.K64
  rfl

/-- Entry-wise equivalence between the Aeneas-extracted round constants
and the FIPS-spec `Impl.K64` table. -/
theorem K64_eq (i : Nat) (hi : i < 80) :
    toUInt64 ((Extraction.consts.K64 : Array U64 80#usize).val[i]!) =
      SHS.SHA512.Impl.K64[i]'(by simpa using hi) := by
  rw [sha2_K64_val]
  revert hi
  revert i
  decide

/-! ## SHA-512 IV table equivalences -/

private theorem sha2_H512_512_val :
    (Extraction.consts.H512_512 : Array U64 8#usize).val =
      [7640891576956012808#u64, 13503953896175478587#u64, 4354685564936845355#u64,
       11912009170470909681#u64, 5840696475078001361#u64,
       11170449401992604703#u64, 2270897969802886507#u64, 6620516959819538809#u64] := by
  unfold Extraction.consts.H512_512
  rfl

theorem H512_512_eq :
    arrayU64ToVec Extraction.consts.H512_512 = SHS.SHA512.Impl.H0_512 := by
  apply Vector.toList_inj.mp
  rw [arrayU64ToVec_toList, sha2_H512_512_val]
  decide

private theorem sha2_H512_384_val :
    (Extraction.consts.H512_384 : Array U64 8#usize).val =
      [14680500436340154072#u64, 7105036623409894663#u64,
       10473403895298186519#u64, 1526699215303891257#u64, 7436329637833083697#u64,
       10282925794625328401#u64, 15784041429090275239#u64, 5167115440072839076#u64] := by
  unfold Extraction.consts.H512_384
  rfl

theorem H512_384_eq :
    arrayU64ToVec Extraction.consts.H512_384 = SHS.SHA512.Impl.H0_384 := by
  apply Vector.toList_inj.mp
  rw [arrayU64ToVec_toList, sha2_H512_384_val]
  decide

private theorem sha2_H512_256_val :
    (Extraction.consts.H512_256 : Array U64 8#usize).val =
      [2463787394917988140#u64, 11481187982095705282#u64, 2563595384472711505#u64,
       10824532655140301501#u64, 10819967247969091555#u64,
       13717434660681038226#u64, 3098927326965381290#u64, 1060366662362279074#u64] := by
  unfold Extraction.consts.H512_256
  rfl

theorem H512_256_eq :
    arrayU64ToVec Extraction.consts.H512_256 = SHS.SHA512.Impl.H0_512_256 := by
  apply Vector.toList_inj.mp
  rw [arrayU64ToVec_toList, sha2_H512_256_val]
  decide

private theorem sha2_H512_224_val :
    (Extraction.consts.H512_224 : Array U64 8#usize).val =
      [10105294471447203234#u64, 8350123849800275158#u64, 2160240930085379202#u64,
       7466358040605728719#u64, 1111592415079452072#u64, 8638871050018654530#u64,
       4583966954114332360#u64, 1230299281376055969#u64] := by
  unfold Extraction.consts.H512_224
  rfl

theorem H512_224_eq :
    arrayU64ToVec Extraction.consts.H512_224 = SHS.SHA512.Impl.H0_512_224 := by
  apply Vector.toList_inj.mp
  rw [arrayU64ToVec_toList, sha2_H512_224_val]
  decide
