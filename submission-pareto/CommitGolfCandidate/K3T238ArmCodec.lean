import CommitGolfCandidate.K3CLowerFormat
import CommitGolfCandidate.TwoPermutationPackedInputFrame

/-! # The packed siblings of loop levels 6..13 (T238)

Loop levels `L = 6..13` (tree depths 16..9) read 238-bit siblings from the record's packed block at
`lowerProofByte ordinal 6`: slot `k = L-6 < 7` is 30 bytes holding the sibling in bits `0..237` and, in bits
`238..239`, bits `2k, 2k+1` of `t`, the last sibling's bits `224..237`; the last slot (`L = 13`) is the last
sibling's low 28 bytes. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

/-- Bits `238..239` of the 30-byte slot of loop level `6+k` (`k < 7`). -/
def packedSpare (state : MachineState) (ordinal k : Nat) : BitVec 2 :=
  (readBuffer state (lowerProofByte ordinal (6+k)) 30).extractLsb' 238 2

/-- The last packed sibling's bits `224..237`: the spare pair of slot `k` in bits `2k, 2k+1`. -/
def packedTail (state : MachineState) (ordinal : Nat) : BitVec 14 :=
  packedSpare state ordinal 6 ++ packedSpare state ordinal 5 ++ packedSpare state ordinal 4 ++
    packedSpare state ordinal 3 ++ packedSpare state ordinal 2 ++ packedSpare state ordinal 1 ++
    packedSpare state ordinal 0

/-- The 238-bit sibling of loop level `level ∈ 6..13`, zero-extended. -/
def packedSibling (state : MachineState) (ordinal level : Nat) : Digest :=
  if level = 13 then (0 : BitVec 18) ++ (packedTail state ordinal ++ readBuffer state (lowerProofByte ordinal 13) 28)
  else (0 : BitVec 18) ++ (readBuffer state (lowerProofByte ordinal level) 30).extractLsb' 0 238

theorem packed_slot_byte (ordinal level : Nat) (low : 6 ≤ level) (high : level ≤ 13) :
    lowerProofByte ordinal level = lowerProofByte ordinal 6 + 30*(level-6) := by
  unfold lowerProofByte
  split_ifs <;> omega

/-- A packed sibling depends only on the 238 bytes of the packed block. -/
theorem packed_sibling_frame (before after : MachineState) (ordinal level : Nat)
    (low : 6 ≤ level) (high : level < 14)
    (frame : ∀ j < 238, memoryView after ((lowerProofByte ordinal 6+j)/8) =
      memoryView before ((lowerProofByte ordinal 6+j)/8)) :
    packedSibling after ordinal level = packedSibling before ordinal level := by
  have slot (l n : Nat) (lo : 6 ≤ l) (hi : l ≤ 13) (fits : 30*(l-6)+n ≤ 238) :
      readBuffer after (lowerProofByte ordinal l) n = readBuffer before (lowerProofByte ordinal l) n := by
    apply buffer_byte_frame
    intro j inside
    rw [packed_slot_byte ordinal l lo hi, Nat.add_assoc]
    exact frame _ (by omega)
  have spare (k : Nat) (small : k ≤ 6) : packedSpare after ordinal k = packedSpare before ordinal k := by
    unfold packedSpare
    rw [slot (6+k) 30 (by omega) (by omega) (by omega)]
  unfold packedSibling
  split
  · unfold packedTail
    rw [spare 0 (by decide), spare 1 (by decide), spare 2 (by decide), spare 3 (by decide), spare 4 (by decide),
      spare 5 (by decide), spare 6 (by decide), slot 13 28 (by decide) (by decide) (by decide)]
  · next last =>
    rw [slot level 30 low (by omega) (by omega)]

end TwoPermutationPrototype.Packed.Checker
