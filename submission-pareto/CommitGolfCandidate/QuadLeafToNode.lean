import CommitGolfCandidate.QuadRecordLeafBlock
import CommitGolfCandidate.QuadNodeBlock

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
@[local simp] private theorem leaf_node_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

/-- The two unchanged words between the pinned leaf and quad entry. -/
def leafToQuad (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x21 .x21 16)) (.ADD .x6 .x6 .x20)

theorem leaf_to_quad_hop (s : MachineState) (pc : s.pc=4328) : GroupHop s (leafToQuad s) 2 := by
  let middle := execInstrBr s (.ADDI .x21 .x21 16)
  have pcM : middle.pc=4332 := by simp [middle,execInstrBr,pc]
  have first : GroupHop s middle 1 := by
    intro fuel
    have fetched := fetch_at s 58 (.ADDI .x21 .x21 16) (by decide) pc rfl
    have step : ordinaryStep s (.base (.ADDI .x21 .x21 16))=some middle := rfl
    rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
    rfl
  have last : GroupHop middle (leafToQuad s) 1 := by
    intro fuel
    have fetched := fetch_at middle 59 (.ADD .x6 .x6 .x20) (by decide) pcM rfl
    have step : ordinaryStep middle (.base (.ADD .x6 .x6 .x20))=some (leafToQuad s) := rfl
    rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
    rfl
  exact first.thenDo last

theorem leaf_to_quad_post (s : MachineState) (pc : s.pc=4328) :
    (leafToQuad s).pc=4336 ∧ (leafToQuad s).getReg .x21=s.getReg .x21+16 ∧
      (leafToQuad s).getReg .x6=s.getReg .x6+s.getReg .x20 ∧ (leafToQuad s).mem=s.mem := by
  simp [leafToQuad,execInstrBr,signExtend12,pc] <;> rfl

theorem leaf_to_quad_saved (s : MachineState) (r : Reg) (a : r≠.x21) (b : r≠.x6) :
    (leafToQuad s).getReg r=s.getReg r := by
  simp [leafToQuad,execInstrBr,Ne.symm a,Ne.symm b]

theorem quad_opened_slot (index : Index) :
    BitVec.ofNat 64 (LENGTH+index.val) &&& 3#64=BitVec.ofNat 64 (index.val%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  change ((16777216+index.val)%2^64) &&& (2^2-1)=(index.val%4)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

end TwoPermutationPrototype.Quad.Checker
