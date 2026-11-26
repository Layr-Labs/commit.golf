import CommitGolfCandidate.TwoPermutationPackedZeroLeaves
import CommitGolfCandidate.TwoPermutationPackedSetup

/-! The leaf phase ends at word 45128, which now jumps straight to word 45683. The five
parent-setup words there run on the raw leaf heap; the height-0 parents mask the leaves. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def skipJump : Instr := .JAL .x0 2220
def skipEntry (s : MachineState) : MachineState := parentSetup (execInstrBr s skipJump) 5
def skipEntryCost : Nat := 6

private theorem skip_decode_jump : Manifest.decodeBase (packed_wideCodeWord 45128) = some skipJump := by
  decide +kernel
private theorem skip_decode_setup : ∀ j : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (45683+j.val)) = some ((parentSetupOps[j.val]?).getD .EBREAK) := by
  decide +kernel

private def skipAt (s : MachineState) (i : Nat) : MachineState :=
  if i=0 then s else parentSetup (execInstrBr s skipJump) (i-1)

private theorem skip_jump_pc (s : MachineState) (atLeaves : s.pc=184608) :
    (execInstrBr s skipJump).pc=BitVec.ofNat 64 (4096+4*45683) := by
  unfold skipJump;rw [jal_pc,atLeaves];rfl

attribute [local irreducible] execute packedWideCommitImage in
theorem skip_entry_execute (s : MachineState) (atLeaves : s.pc=184608) (fuel : Nat) :
    execute packedWideCommitImage (skipEntryCost+fuel) s true =
      (do let result ← execute packedWideCommitImage fuel (skipEntry s) true
          return result.charge skipEntryCost 0) := by
  have jp:=skip_jump_pc s atLeaves
  have setPC (j : Nat) (h : j<5) : (parentSetup (execInstrBr s skipJump) j).pc=BitVec.ofNat 64 (4096+4*(45683+j)) := by
    interval_cases j <;> simp only [parentSetup,parentSetupOps,List.take,List.foldl,addi_pc,sub_pc,jp] <;> rfl
  have setStep (j : Nat) (h : j<5) : ordinaryStep (parentSetup (execInstrBr s skipJump) j)
      (.base ((parentSetupOps[j]?).getD .EBREAK)) = some (parentSetup (execInstrBr s skipJump) (j+1)) := by
    interval_cases j <;>
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,parentSetupOps,parentSetup,List.take,
        List.foldl,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,ite_true]
  have run:=CommitGolfCandidate.execute_unit_steps packedWideCommitImage 6 fuel (skipAt s) true (by
    intro i inside
    by_cases i0 : i=0
    · subst i0
      refine ⟨.base skipJump,zero_fetch 45128 _ skip_decode_jump (by decide) s (by rw [atLeaves];rfl),?_,rfl⟩
      simp only [skipAt,if_true,show (0+1=0)=False by simp,if_false,Nat.add_sub_cancel]
      rfl
    · obtain ⟨j,rfl⟩ : ∃ j, i=j+1 := ⟨i-1,by omega⟩
      have jl : j<5 := by omega
      refine ⟨_,zero_fetch (45683+j) _ (skip_decode_setup ⟨j,jl⟩) (by omega) _ ?_,?_,?_⟩
      · simp only [skipAt,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel];exact setPC j jl
      · simp only [skipAt,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel];exact setStep j jl
      · interval_cases j <;> rfl)
  exact run

theorem skip_entry_ready (state : MachineState) (atLeaves : state.pc=184608)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (skipEntry state) (2^24-1) ∧ (skipEntry state).pc=186848 ∧
      (skipEntry state).getReg .x8=state.getReg .x8 ∧ (skipEntry state).getReg .x19=state.getReg .x19 ∧
      (skipEntry state).mem=state.mem := by
  refine ⟨⟨?_,?_,selector,rfl,rfl,heap⟩,?_,rfl,rfl,rfl⟩
  · change state.getReg .x21+signExtend12 4032=_
    rw [stop]
    rfl
  · change state.getReg .x21-state.getReg .x19+signExtend12 4064=_
    rw [stop,stride]
    rfl
  · change (execInstrBr state skipJump).pc+4+4+4+4+4=_
    rw [skip_jump_pc state atLeaves]
    rfl

end TwoPermutationPrototype.RV64
