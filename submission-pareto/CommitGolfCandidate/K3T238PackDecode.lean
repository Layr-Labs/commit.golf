import CommitGolfCandidate.K3T238ArmCodec
import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.K3OpenPack238

/-! # Decoding the T238 packed sibling block (reader side)

A packed block at `base` is GQ's `Quartet.packEight nodes` (238 bytes): slot `k < 7` is the 30
little-endian bytes of `low238 nodes[k]` with bits `224+2k, 225+2k` of `nodes[7]` in bits 238, 239;
bytes `210..237` are the low 28 bytes of `nodes[7]`. `packedNodeAt state base k` reads node `k` back
as `pad238 nodes[k]` (`packed_node_of_bytes`); the loop's `packedSibling` is `packedNodeAt` at the
record's packed block (`packed_sibling_eq_node`), so `packed_sibling_of_bytes` follows. No hypothesis
on the high bits of the nodes is needed. -/

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- Bits 238..239 of the 30-byte slot at `slot`. -/
def packedSpareAt (state : MachineState) (slot : Nat) : BitVec 2 := (readBuffer state slot 30).extractLsb' 238 2
/-- Node k < 8 of a packed block at `base`. -/
def packedNodeAt (state : MachineState) (base k : Nat) : Digest :=
  if k = 7 then (0 : BitVec 18) ++ ((packedSpareAt state (base+180) ++ packedSpareAt state (base+150) ++
    packedSpareAt state (base+120) ++ packedSpareAt state (base+90) ++ packedSpareAt state (base+60) ++
    packedSpareAt state (base+30) ++ packedSpareAt state base) ++ readBuffer state (base+210) 28)
  else (0 : BitVec 18) ++ (readBuffer state (base+30*k) 30).extractLsb' 0 238

/-- The 256-bit word whose low 30 bytes form `Quartet.packedSlot x c`. -/
private def slotWord (x : BitVec 256) (c : BitVec 2) : BitVec 256 :=
  (0 : BitVec 16) ++ (c ++ x.extractLsb' 0 238)

private theorem slot_word_bit (x : BitVec 256) (c : BitVec 2) (i : Nat) :
    (slotWord x c).getLsbD i =
      if i < 238 then x.getLsbD i else if i < 240 then c.getLsbD (i - 238) else false :=
  TwoPermutationPrototype.GroupedOpening.slot_getLsbD c x i

/-- Byte `j < 30` of a packed slot. -/
private theorem slot_byte (x : BitVec 256) (c : BitVec 2) (j : Nat) (small : j < 30) :
    (Quartet.packedSlot x c)[j]! = (slotWord x c).extractLsb' (8*j) 8 := by
  have word : Quartet.packedSlot x c = (digestBytes (slotWord x c)).take 30 := rfl
  have fits : j < 32 := by omega
  rw [word, List.getElem!_eq_getElem?_getD, List.getElem?_take, if_pos small, digestBytes,
    List.getElem?_ofFn, dif_pos fits]
  rfl

/-- 30 bytes in memory that spell a packed slot read back as the low 240 bits of its word. -/
private theorem slot_read (state : MachineState) (slot : Nat) (x : BitVec 256) (c : BitVec 2)
    (bytes : ∀ j < 30, state.getByte (BitVec.ofNat 64 (slot+j)) = (Quartet.packedSlot x c)[j]!) :
    readBuffer state slot 30 = (slotWord x c).extractLsb' (8*0) (8*30) := by
  apply read_serialized_slice
  intro j small
  rw [bytes j small, slot_byte x c j small, Nat.zero_add]

private theorem low_of_word (x : BitVec 256) (c : BitVec 2) :
    ((slotWord x c).extractLsb' (8*0) (8*30)).extractLsb' 0 238 = x.extractLsb' 0 238 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i small
  have below : i < 240 := by omega
  simp only [BitVec.getLsbD_extractLsb', slot_word_bit]
  simp [small, below]

private theorem spare_of_word (x : BitVec 256) (c : BitVec 2) :
    ((slotWord x c).extractLsb' (8*0) (8*30)).extractLsb' 238 2 = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro j small
  simp only [BitVec.getLsbD_extractLsb', slot_word_bit]
  interval_cases j <;> simp

/-- Byte `30k+i` of a concatenation of 30-byte lists is byte `i` of list `k`. -/
private theorem flat_slot (f : Nat → List Byte) (width : ∀ k, (f k).length = 30) :
    ∀ n k i, k < n → i < 30 → ((List.range n).flatMap f)[30*k+i]? = (f k)[i]? := by
  intro n
  induction n with
  | zero => intro k i hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro k i hk hi
    have len : ((List.range n).flatMap f).length = 30*n := by
      simp [List.length_flatMap, width, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append]
    by_cases lt : k < n
    · have inside : 30*k+i < ((List.range n).flatMap f).length := by rw [len]; omega
      rw [List.getElem?_append_left inside]
      exact ih k i lt hi
    · have same : k = n := by omega
      rw [same]
      have beyond : ((List.range n).flatMap f).length ≤ 30*n+i := by rw [len]; omega
      rw [List.getElem?_append_right beyond, len, Nat.add_sub_cancel_left]
      simp

/-- Byte `30k+i` of `packEight` (`k < 7`, `i < 30`) is byte `i` of slot `k`. -/
private theorem pack_eight_slot (nodes : List (BitVec 256)) (k i : Nat) (hk : k < 7) (hi : i < 30) :
    (Quartet.packEight nodes)[30*k+i]! =
      (Quartet.packedSlot (nodes.getD k 0) ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))[i]! := by
  have flat := flat_slot (fun k => Quartet.packedSlot (nodes.getD k 0) ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))
    (fun k => Quartet.packed_slot_length _ _) 7 k i hk hi
  have len : ((List.range 7).flatMap (fun k => Quartet.packedSlot (nodes.getD k 0)
      ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))).length = 210 := by
    simp [List.length_flatMap, Quartet.packed_slot_length]
  have inside : 30*k+i < ((List.range 7).flatMap (fun k => Quartet.packedSlot (nodes.getD k 0)
      ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))).length := by rw [len]; omega
  simp only [Quartet.packEight]
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left inside, flat]

/-- Byte `210+i` of `packEight` (`i < 28`) is byte `i` of the last node. -/
private theorem pack_eight_last (nodes : List (BitVec 256)) (i : Nat) (hi : i < 28) :
    (Quartet.packEight nodes)[210+i]! = (nodes.getD 7 0).extractLsb' (8*i) 8 := by
  have len : ((List.range 7).flatMap (fun k => Quartet.packedSlot (nodes.getD k 0)
      ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))).length = 210 := by
    simp [List.length_flatMap, Quartet.packed_slot_length]
  have beyond : ((List.range 7).flatMap (fun k => Quartet.packedSlot (nodes.getD k 0)
      ((nodes.getD 7 0).extractLsb' (224 + 2*k) 2))).length ≤ 210+i := by rw [len]; omega
  have fits : i < 32 := by omega
  simp only [Quartet.packEight]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right beyond, len, Nat.add_sub_cancel_left,
    List.getElem?_take, if_pos hi, digestBytes, List.getElem?_ofFn, dif_pos fits]
  rfl

/-- A plain 30-byte slot (zero spare bits) reads back as the zero-extended low 238 bits. -/
theorem packed_slot_of_bytes (state : MachineState) (slot : Nat) (x : BitVec 256)
    (bytes : ∀ j < 30, state.getByte (BitVec.ofNat 64 (slot+j)) = (Quartet.packedSlot x 0)[j]!) :
    (0 : BitVec 18) ++ (readBuffer state slot 30).extractLsb' 0 238 = pad238 x := by
  rw [slot_read state slot x 0 bytes, low_of_word]
  rfl

/-- Node `k < 8` of a packed block written as `Quartet.packEight nodes` reads back as `pad238 nodes[k]`. -/
theorem packed_node_of_bytes (state : MachineState) (base : Nat) (nodes : List (BitVec 256)) (size : nodes.length = 8)
    (bytes : ∀ j < 238, state.getByte (BitVec.ofNat 64 (base+j)) = (Quartet.packEight nodes)[j]!) (k : Nat) (small : k < 8) :
    packedNodeAt state base k = pad238 (nodes[k]!) := by
  have inList : k < nodes.length := by omega
  have entry : nodes[k]! = nodes.getD k 0 := by
    rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inList]
    rfl
  have slotAt : ∀ m < 7, readBuffer state (base + 30*m) 30 =
      (slotWord (nodes.getD m 0) ((nodes.getD 7 0).extractLsb' (224 + 2*m) 2)).extractLsb' (8*0) (8*30) := by
    intro m hm
    apply slot_read
    intro j hj
    have addr : base + 30*m + j = base + (30*m+j) := by omega
    have lt : 30*m+j < 238 := by omega
    rw [addr, bytes (30*m+j) lt, pack_eight_slot nodes m j hm hj]
  unfold packedNodeAt
  by_cases last : k = 7
  · rw [if_pos last]
    have spare : ∀ m < 7, packedSpareAt state (base + 30*m) = (nodes.getD 7 0).extractLsb' (224 + 2*m) 2 := by
      intro m hm
      unfold packedSpareAt
      rw [slotAt m hm, spare_of_word]
    have e6 : packedSpareAt state (base+180) = (nodes.getD 7 0).extractLsb' 236 2 := spare 6 (by decide)
    have e5 : packedSpareAt state (base+150) = (nodes.getD 7 0).extractLsb' 234 2 := spare 5 (by decide)
    have e4 : packedSpareAt state (base+120) = (nodes.getD 7 0).extractLsb' 232 2 := spare 4 (by decide)
    have e3 : packedSpareAt state (base+90) = (nodes.getD 7 0).extractLsb' 230 2 := spare 3 (by decide)
    have e2 : packedSpareAt state (base+60) = (nodes.getD 7 0).extractLsb' 228 2 := spare 2 (by decide)
    have e1 : packedSpareAt state (base+30) = (nodes.getD 7 0).extractLsb' 226 2 := spare 1 (by decide)
    have e0 : packedSpareAt state base = (nodes.getD 7 0).extractLsb' 224 2 := spare 0 (by decide)
    have tail : readBuffer state (base+210) 28 = (nodes.getD 7 0).extractLsb' (8*0) (8*28) := by
      apply read_serialized_slice
      intro j hj
      have addr : base + 210 + j = base + (210+j) := by omega
      have lt : 210 + j < 238 := by omega
      rw [addr, bytes (210+j) lt, pack_eight_last nodes j hj, Nat.zero_add]
    have whole : (packedSpareAt state (base+180) ++ packedSpareAt state (base+150) ++
        packedSpareAt state (base+120) ++ packedSpareAt state (base+90) ++ packedSpareAt state (base+60) ++
        packedSpareAt state (base+30) ++ packedSpareAt state base) ++ readBuffer state (base+210) 28 =
        (nodes.getD 7 0).extractLsb' 0 238 := by
      rw [e6, e5, e4, e3, e2, e1, e0, tail]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases lowPart : i < 224
      · have below : i < 238 := by omega
        simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
        simp [lowPart, below]
      · obtain ⟨t, rfl⟩ : ∃ t, i = 224 + t := ⟨i - 224, by omega⟩
        have ht : t < 14 := by omega
        simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
        interval_cases t <;> simp
    rw [entry, last]
    unfold pad238
    exact congrArg (fun y : BitVec 238 => (0 : BitVec 18) ++ y) whole
  · have hk : k < 7 := by omega
    rw [if_neg last, entry, slotAt k hk, low_of_word]
    rfl

/-- The loop's packed sibling of level `6..13` is node `level-6` of the record's packed block. -/
theorem packed_sibling_eq_node (state : MachineState) (ordinal level : Nat) (low : 6 ≤ level) (high : level < 14) :
    packedSibling state ordinal level = packedNodeAt state (lowerProofByte ordinal 6) (level-6) := by
  have addr : ∀ m ≤ 7, lowerProofByte ordinal (6+m) = lowerProofByte ordinal 6 + 30*m := by
    intro m hm
    have eq := packed_slot_byte ordinal (6+m) (by omega) (by omega)
    omega
  unfold packedSibling packedNodeAt
  by_cases last : level = 13
  · have last' : level - 6 = 7 := by omega
    rw [if_pos last, if_pos last']
    have spare : ∀ m ≤ 6, packedSpare state ordinal m = packedSpareAt state (lowerProofByte ordinal 6 + 30*m) := by
      intro m hm
      unfold packedSpare packedSpareAt
      rw [addr m (by omega)]
    have last13 : lowerProofByte ordinal 13 = lowerProofByte ordinal 6 + 210 := by
      have eq := packed_slot_byte ordinal 13 (by decide) (by decide)
      omega
    unfold packedTail
    rw [spare 6 (by decide), spare 5 (by decide), spare 4 (by decide), spare 3 (by decide), spare 2 (by decide),
      spare 1 (by decide), spare 0 (by decide), last13]
    rfl
  · have notLast : ¬ level - 6 = 7 := by omega
    have top : level ≤ 13 := by omega
    rw [if_neg last, if_neg notLast, packed_slot_byte ordinal level low top]

/-- C2's form: the packed sibling of loop level `6..13` decodes GQ's `packEight` block. -/
theorem packed_sibling_of_bytes (state : MachineState) (ordinal : Nat) (nodes : List (BitVec 256)) (size : nodes.length = 8)
    (bytes : ∀ j < 238, state.getByte (BitVec.ofNat 64 (lowerProofByte ordinal 6 + j)) = (Quartet.packEight nodes)[j]!)
    (level : Nat) (low : 6 ≤ level) (high : level < 14) :
    packedSibling state ordinal level = pad238 (nodes[level-6]!) := by
  have small : level - 6 < 8 := by omega
  rw [packed_sibling_eq_node state ordinal level low high]
  exact packed_node_of_bytes state (lowerProofByte ordinal 6) nodes size bytes (level-6) small

end TwoPermutationPrototype.Packed.Checker
