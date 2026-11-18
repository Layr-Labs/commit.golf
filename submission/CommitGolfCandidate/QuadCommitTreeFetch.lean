import CommitGolfCandidate.QuadCommitFetch
import CommitGolfCandidate.QuadCommitParentControl

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image leafCode quadCode parentCode decodeInstruction

def parentPrefix := quadPrefix++quadCode++quadLatchWords++parentSetupWords

theorem parent_prefix_length : parentPrefix.length=94375 := by
  unfold parentPrefix
  simp only [List.length_append]
  rw [quad_prefix_length,quad_code_length]
  rfl

theorem parent_code_length : parentCode.length=62836 := by
  simp only [parentCode,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

theorem fetch_parent (slot : Fin 15709) (part : Fin 4) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(94375+4*slot.val+part.val))) :
    fetch image s=some (.base (if part.val=0 then .ECALL else if part.val=1 then .SH .x12 .x0 30
      else if part.val=2 then .ADDI .x10 .x10 4032 else .ADDI .x12 .x12 4064)) := by
  apply fetch_code_index s (94375+4*slot.val+part.val) (by have := slot.isLt;have := part.isLt;omega) pc
  have atIndex := code_segment_at parentPrefix parentCode (parentLatchWords++rootWords)
    (by unfold image parentPrefix quadPrefix;simp only [List.append_assoc]) (4*slot.val+part.val)
    (by rw [parent_code_length];have := slot.isLt;have := part.isLt;omega)
  rw [parent_prefix_length] at atIndex
  simp only [←Nat.add_assoc] at atIndex
  rw [atIndex]
  unfold parentCode
  have repeated := repeated_code_at parentWords 15709 slot.val part.val slot.isLt part.isLt
  change ((List.replicate 15709 parentWords).flatten)[4*slot.val+part.val]?=parentWords[part.val]? at repeated
  rw [repeated]
  fin_cases part <;> change decodeInstruction _=some (.base _) <;> unfold decodeInstruction <;> rfl

theorem parent_words (i : Nat) (hi : i<15709) : PackedParentWordsAt image (packedParentPC 381596 i) := by
  have pc (s : MachineState) (k : Fin 4) (h : s.pc=packedParentPC 381596 i+BitVec.ofNat 64 (4*k.val)) :
      s.pc=BitVec.ofNat 64 (4096+4*(94375+4*i+k.val)) := by
    rw [h,packedParentPC]
    change BitVec.ofNat 64 381596+BitVec.ofNat 64 (16*i)+BitVec.ofNat 64 (4*k.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro s h;exact fetch_parent ⟨i,hi⟩ ⟨0,by decide⟩ s (pc s ⟨0,by decide⟩ (by simpa using h))
  · intro s h;exact fetch_parent ⟨i,hi⟩ ⟨1,by decide⟩ s (pc s ⟨1,by decide⟩ h)
  · intro s h;exact fetch_parent ⟨i,hi⟩ ⟨2,by decide⟩ s (pc s ⟨2,by decide⟩ h)
  · intro s h;exact fetch_parent ⟨i,hi⟩ ⟨3,by decide⟩ s (pc s ⟨3,by decide⟩ h)

private theorem fetch_parent_latch (part : Fin 2) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (632940+4*part.val)) :
    fetch image s=some (.base (if part.val=0 then .BEQ .x12 .x21 8 else .JAL .x0 1845804)) := by
  apply fetch_code_index s (157211+part.val) (by have := part.isLt;omega)
    (by rw [pc];congr 1;omega)
  have atIndex := code_segment_at (parentPrefix++parentCode) parentLatchWords rootWords
    (by unfold image parentPrefix quadPrefix;simp only [List.append_assoc]) part.val part.isLt
  rw [List.length_append,parent_prefix_length,parent_code_length] at atIndex
  change image.code[157211+part.val]?=_ at atIndex
  rw [atIndex]
  fin_cases part <;> change decodeInstruction _=some (.base _) <;> unfold decodeInstruction <;> rfl

def parent_control : Parents.Control image 381596 15709 where
  backOffset := 1845804
  backTarget := by decide
  branch s pc := fetch_parent_latch ⟨0,by decide⟩ s pc
  jump s pc := fetch_parent_latch ⟨1,by decide⟩ s pc

end TwoPermutationPrototype.Quad.Commit
