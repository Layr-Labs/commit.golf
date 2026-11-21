import CommitGolfCandidate.ChainedCommitCode

/-! Concrete call edges, register setup and schedule of the parent routine. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def parentLevelPrefix (s : MachineState) (h : Height) (count : Nat) : MachineState :=
  ((parentLevelOps h).take count).foldl execInstrBr s

theorem level_height (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 5).getReg .x17 = BitVec.ofNat 64 h.val := by
  fin_cases h <;> rfl

theorem level_mask (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 5).getReg .x16 = BitVec.ofNat 64 (2^(width h-192)-1) := by
  change (BitVec.ofNat 64 0+signExtend12 4095) >>>
    (BitVec.ofNat 6 (256-width h)).toNat = _
  fin_cases h <;> decide

theorem level_remaining (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 7).getReg .x18 = BitVec.ofNat 64 (calls h-1) := by
  fin_cases h <;> rfl

theorem level_boundary (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 5).getReg .x15 = s.getReg .x9+s.getReg .x4-32 := by
  fin_cases h <;>
    change s.getReg .x9+s.getReg .x4+signExtend12 4064 = _ <;>
    rw [BitVec.sub_eq_add_neg] <;> rfl

theorem level_hash_target (base : Word) (h : Height) :
    base+BitVec.ofNat 64 (4*(12+20*h.val))+
        signExtend21 (BitVec.ofNat 21 (1936-80*h.val)) = base+1984 := by
  fin_cases h <;> rw [BitVec.add_assoc] <;> rfl

theorem level_back_target (base : Word) (h : Height) :
    base+BitVec.ofNat 64 (4*(23+20*h.val))+signExtend13 8140 =
      base+BitVec.ofNat 64 (4*(10+20*h.val)) := by
  fin_cases h <;> rw [BitVec.add_assoc] <;> rfl

theorem hash_pack_target (base : Word) : base+1984+signExtend21 16 = base+2000 := by
  rw [BitVec.add_assoc]
  rfl

theorem hash_continuation_target (base : Word) : base+1996+signExtend21 128 = base+2124 := by
  rw [BitVec.add_assoc]
  rfl

def parentNodeSteps (h : Height) : Nat := 49+continuationInstructions (calls h-1)

def parentNodeCycles (h : Height) : Nat := 56+continuationCycles (calls h-1)

theorem parent_node_charge : ∀ h : Height, parentNodeCycles h = parentNodeSteps h+7*calls h := by
  decide +kernel

theorem parent_schedule_totals :
    (∑ h : Height, parentNodeSteps h*2^(23-h.val))+160 = 1343338090 ∧
    (∑ h : Height, parentNodeCycles h*2^(23-h.val))+160 = 1814456675 := by
  decide +kernel

end CommitGolfCandidate.Chained.Native
