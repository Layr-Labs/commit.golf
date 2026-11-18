import CommitGolfCandidate.QuadCommitLeafControlFetch

/-! Fetch helpers for the fixed prologue/latches and repeated quad/parent bodies. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Leaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image leafCode quadCode parentCode decodeInstruction

theorem repeated_code_at {α : Type} (chunk : List α) (n j k : Nat) (hj : j<n) (hk : k<chunk.length) :
    ((List.replicate n chunk).flatten)[chunk.length*j+k]?=chunk[k]? := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons]
    cases j with
    | zero => simpa only [Nat.mul_zero,Nat.zero_add] using (List.getElem?_append_left hk)
    | succ j =>
      rw [Nat.mul_succ]
      rw [List.getElem?_append_right (by omega)]
      rw [show chunk.length*j+chunk.length+k-chunk.length=chunk.length*j+k by omega]
      exact ih j (by omega)

theorem fetch_code_index (s : MachineState) (index : Nat) (bounded : index<2^32)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*index)) (instruction : Instr)
    (decoded : (image.code[index]?).bind decodeInstruction=some (.base instruction)) :
    fetch image s=some (.base instruction) := by
  have numeric : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rw [fetch,numeric,if_pos (by omega),show (4096+4*index-4096)/4=index by omega]
  cases result : image.code[index]? with
  | none => simp [result] at decoded
  | some w => simpa [result] using decoded

theorem code_segment_at (head chunk suffix : List (BitVec 32))
    (code : image.code=head++chunk++suffix) (j : Nat) (inside : j<chunk.length) :
    image.code[head.length+j]?=chunk[j]? := by
  rw [code,List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact List.getElem?_append_left inside

def leafLatchPrefix := setupWords++leafCode
def leafLatchSuffix := quadSetupWords++quadCode++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords

theorem leaf_latch_prefix_length : leafLatchPrefix.length=45185 := by
  unfold leafLatchPrefix
  rw [List.length_append,leaf_code_word_count]
  rfl

theorem fetch_leaf_latch (s : MachineState) (pc : s.pc=184836) :
    fetch image s=some (.base (.BEQ .x10 .x8 72)) := by
  apply fetch_code_index s 45185 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 0 (by decide)
  rw [leaf_latch_prefix_length,Nat.add_zero] at atIndex
  rw [atIndex]
  change decodeInstruction 0x04850463=some (.base (.BEQ .x10 .x8 72))
  unfold decodeInstruction
  rfl

theorem fetch_leaf_jump (s : MachineState) (pc : s.pc=184840) :
    fetch image s=some (.base (.JAL .x0 1916484)) := by
  apply fetch_code_index s 45186 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 1 (by decide)
  rw [leaf_latch_prefix_length] at atIndex
  rw [atIndex]
  change decodeInstruction 0xe45d306f=some (.base (.JAL .x0 1916484))
  unfold decodeInstruction
  rfl

def quadPrefix := setupWords++leafCode++leafLatchWords++quadSetupWords
def quadSuffix := quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords

def quadPC (slot part : Nat) : Word := BitVec.ofNat 64 (4096+4*(45212+3*slot+part))
def quadInstr (part : Nat) : Instr := if part=0 then .ECALL else if part=1 then .ADDI .x10 .x10 368 else .ADDI .x12 .x12 32

theorem quad_prefix_length : quadPrefix.length=45212 := by
  unfold quadPrefix
  simp only [List.length_append]
  rw [leaf_code_word_count]
  rfl

theorem quad_code_length : quadCode.length=49152 := by
  simp only [quadCode,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

theorem fetch_quad (slot : Fin 16384) (part : Fin 3) (s : MachineState)
    (pc : s.pc=quadPC slot.val part.val) : fetch image s=some (.base (quadInstr part.val)) := by
  apply fetch_code_index s (45212+3*slot.val+part.val) (by have := slot.isLt;have := part.isLt;omega) pc
  have atIndex := code_segment_at quadPrefix quadCode quadSuffix
    (by unfold image quadPrefix quadSuffix;simp only [List.append_assoc]) (3*slot.val+part.val)
    (by rw [quad_code_length];have := slot.isLt;have := part.isLt;omega)
  rw [quad_prefix_length] at atIndex
  simp only [←Nat.add_assoc] at atIndex
  rw [atIndex]
  unfold quadCode
  have repeated := repeated_code_at quadWords 16384 slot.val part.val slot.isLt part.isLt
  change ((List.replicate 16384 quadWords).flatten)[3*slot.val+part.val]?=quadWords[part.val]? at repeated
  rw [repeated]
  fin_cases part <;> change decodeInstruction _=some (.base _) <;> unfold quadInstr decodeInstruction <;> rfl


end TwoPermutationPrototype.Quad.Commit
