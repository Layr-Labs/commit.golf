import CommitGolfCandidate.PairSuffix
import CommitGolfCandidate.PairFormat
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 400000

abbrev outBase : Nat := 10871707680
abbrev indexBase : Nat := 6442455072
def childAddress (u : Nat) := 4294971424 + heapOffset ((256+u) ^^^ 1)

theorem fixedSource : ∀ u : Fin 256, srcOf (BitVec.ofNat 64 u.val) =
    BitVec.ofNat 64 (childAddress u.val) := by decide
theorem fixedDestination : ∀ u : Fin 256, dstOf (BitVec.ofNat 64 u.val) =
    BitVec.ofNat 64 (outBase + 32*(u.val/2)) := by decide
theorem childBounds : ∀ u : Fin 256,
    childAddress u.val % 8 = 0 ∧ childAddress u.val + 32 ≤ outBase := by decide

theorem cursor_dec (s : MachineState) {n : Nat} (f : Frame s (n+1)) :
    s.getReg .x24 + signExtend12 4088 = BitVec.ofNat 64 (indexBase + 8*n) := by
  rw [f.cursor, show 6442455072+8*(n+1) = (6442455072+8*n)+8 by omega, BitVec.ofNat_add,
    BitVec.add_assoc, show BitVec.ofNat 64 8 + signExtend12 4088 = 0 by decide]
  exact BitVec.add_zero _

theorem lane (s : MachineState) {n i : Nat} (f : Frame s (n+1)) (bi : i < 2^24)
    (loaded : s.getMem (BitVec.ofNat 64 (indexBase+8*n)) = BitVec.ofNat 64 i) :
    leafBucket s = BitVec.ofNat 64 (i/65536) := by
  unfold leafBucket
  rw [cursor_dec s f,loaded]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2^64)]
  change i / 65536 &&& (2^8-1) = (i/65536) % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem locations (s : MachineState) {n i : Nat} (f : Frame s (n+1)) (bi : i < 2^24)
    (loaded : s.getMem (BitVec.ofNat 64 (indexBase+8*n)) = BitVec.ofNat 64 i) :
    (headState s).getReg .x23 = BitVec.ofNat 64 (childAddress (i/65536)) ∧
    (headState s).getReg .x25 = BitVec.ofNat 64 (outBase+32*(i/131072)) := by
  rw [head_source, head_destination, srcAddr, dstAddr, f.slots, f.children, lane s f bi loaded]
  let u : Fin 256 := ⟨i/65536, by omega⟩
  exact ⟨fixedSource u, (fixedDestination u).trans (by rw [show u.val/2 = i/131072 by dsimp [u]; omega])⟩

end CommitGolfCandidate.PairCap
