import CommitGolfCandidate.ParentSequence

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem slot_pc_add (start : Word) (index : Nat) :
    start+12+BitVec.ofNat 64 (12*index)=start+BitVec.ofNat 64 (12*(index+1)) := by
  rw [BitVec.add_assoc]
  congr 1
  change BitVec.ofNat 64 12+BitVec.ofNat 64 (12*index)=BitVec.ofNat 64 (12*(index+1))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem parent_sequence_slots (image : Image) (start : Word) (count : Nat)
    (slots : ∀ index<count, ParentTripleFetched image (start+BitVec.ofNat 64 (12*index))) :
    ParentSequenceFetched image start count := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
    constructor
    · simpa using slots 0 (by omega)
    · apply ih (start+12)
      intro index bounded
      rw [slot_pc_add]
      exact slots (index+1) (by omega)

end CommitGolfCandidate
