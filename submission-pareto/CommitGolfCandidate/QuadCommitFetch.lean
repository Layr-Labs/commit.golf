import CommitGolfCandidate.QuadCommitLeafControlFetch

/-! Fetch helpers for the fixed prologue/latches and repeated quad/parent bodies. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Leaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image leafCode quadCode quad2Code quad3Code parentCode decodeInstruction

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
def leafLatchSuffix := quadSetupWords++quadCode++quadLatchWords++quad2SetupWords++quad2Code++quadLatchWords++
  quad3SetupWords++quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords

theorem leaf_latch_prefix_length : leafLatchPrefix.length=45201 := by
  unfold leafLatchPrefix
  rw [List.length_append,leaf_code_word_count]
  rfl

theorem fetch_leaf_latch (s : MachineState) (pc : s.pc=184900) :
    fetch image s=some (.base (.BEQ .x10 .x8 8)) := by
  apply fetch_code_index s 45201 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 0 (by decide)
  rw [leaf_latch_prefix_length,Nat.add_zero] at atIndex
  rw [atIndex]
  change decodeInstruction 0x00850463=some (.base (.BEQ .x10 .x8 8))
  unfold decodeInstruction
  rfl

theorem fetch_leaf_jump (s : MachineState) (pc : s.pc=184904) :
    fetch image s=some (.base (.JAL .x0 1916420)) := by
  apply fetch_code_index s 45202 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 1 (by decide)
  rw [leaf_latch_prefix_length] at atIndex
  rw [atIndex]
  change decodeInstruction 0xe05d306f=some (.base (.JAL .x0 1916420))
  unfold decodeInstruction
  rfl

def quadPrefix := setupWords++leafCode++leafLatchWords++quadSetupWords
def quadSuffix := quadLatchWords++quad2SetupWords++quad2Code++quadLatchWords++
  quad3SetupWords++quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords

/-- Level-1 node `slot` of the unrolled body (`r = slot % 4` selects the destination stride). -/
def quadPC (slot part : Nat) : Word := BitVec.ofNat 64 (4096+4*(45212+3*slot+part))
def quadStride (r : Nat) : BitVec 12 := if r=3 then 272 else 32
def quadInstr (r part : Nat) : Instr :=
  if part=0 then .ECALL else if part=1 then .ADDI .x10 .x10 368
  else .ADDI .x12 .x12 (quadStride r)

theorem quad_prefix_length : quadPrefix.length=45212 := by
  unfold quadPrefix
  simp only [List.length_append]
  rw [leaf_code_word_count]
  rfl

theorem quad_code_length : quadCode.length=49152 := by
  simp only [quadCode,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

theorem quad_group_decoded : ∀ r : Fin 4, ∀ part : Fin 3,
    (quadGroupWords[3*r.val+part.val]?).bind decodeInstruction=some (.base (quadInstr r.val part.val)) := by
  decide +kernel

theorem fetch_quad (slot : Fin 16384) (part : Fin 3) (s : MachineState)
    (pc : s.pc=quadPC slot.val part.val) : fetch image s=some (.base (quadInstr (slot.val%4) part.val)) := by
  apply fetch_code_index s (45212+3*slot.val+part.val) (by have := slot.isLt;have := part.isLt;omega) pc
  have atIndex := code_segment_at quadPrefix quadCode quadSuffix
    (by unfold image quadPrefix quadSuffix;simp only [List.append_assoc]) (3*slot.val+part.val)
    (by rw [quad_code_length];have := slot.isLt;have := part.isLt;omega)
  rw [quad_prefix_length] at atIndex
  simp only [←Nat.add_assoc] at atIndex
  rw [atIndex]
  unfold quadCode
  have r4 := Nat.mod_lt slot.val (by decide : 0<4)
  have repeated := repeated_code_at quadGroupWords 4096 (slot.val/4) (3*(slot.val%4)+part.val)
    (by have := slot.isLt;omega) (by have := part.isLt;change _<12;omega)
  change ((List.replicate 4096 quadGroupWords).flatten)[12*(slot.val/4)+(3*(slot.val%4)+part.val)]?=_ at repeated
  rw [show 3*slot.val+part.val=12*(slot.val/4)+(3*(slot.val%4)+part.val) by omega,repeated]
  exact quad_group_decoded ⟨slot.val%4,r4⟩ part

def quad2Prefix := quadPrefix++quadCode++quadLatchWords++quad2SetupWords
def quad2Suffix := quadLatchWords++quad3SetupWords++quad3Code++quadLatchWords++
  parentSetupWords++parentCode++parentLatchWords++rootWords

/-- Level-2 node `slot` of the unrolled body (same 12-word groups as level 1). -/
def quad2PC (slot part : Nat) : Word := BitVec.ofNat 64 (4096+4*(94375+3*slot+part))

theorem quad2_prefix_length : quad2Prefix.length=94375 := by
  unfold quad2Prefix
  simp only [List.length_append]
  rw [quad_prefix_length,quad_code_length]
  rfl

theorem quad2_code_length : quad2Code.length=49152 := by
  simp only [quad2Code,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

theorem fetch_quad2 (slot : Fin 16384) (part : Fin 3) (s : MachineState)
    (pc : s.pc=quad2PC slot.val part.val) : fetch image s=some (.base (quadInstr (slot.val%4) part.val)) := by
  apply fetch_code_index s (94375+3*slot.val+part.val) (by have := slot.isLt;have := part.isLt;omega) pc
  have atIndex := code_segment_at quad2Prefix quad2Code quad2Suffix
    (by unfold image quad2Prefix quadPrefix quad2Suffix;simp only [List.append_assoc]) (3*slot.val+part.val)
    (by rw [quad2_code_length];have := slot.isLt;have := part.isLt;omega)
  rw [quad2_prefix_length] at atIndex
  simp only [←Nat.add_assoc] at atIndex
  rw [atIndex]
  unfold quad2Code
  have r4 := Nat.mod_lt slot.val (by decide : 0<4)
  have repeated := repeated_code_at quadGroupWords 4096 (slot.val/4) (3*(slot.val%4)+part.val)
    (by have := slot.isLt;omega) (by have := part.isLt;change _<12;omega)
  change ((List.replicate 4096 quadGroupWords).flatten)[12*(slot.val/4)+(3*(slot.val%4)+part.val)]?=_ at repeated
  rw [show 3*slot.val+part.val=12*(slot.val/4)+(3*(slot.val%4)+part.val) by omega,repeated]
  exact quad_group_decoded ⟨slot.val%4,r4⟩ part

def quad3Prefix := quad2Prefix++quad2Code++quadLatchWords++quad3SetupWords
def quad3Suffix := quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords

def quad3PC (slot part : Nat) : Word := BitVec.ofNat 64 (4096+4*(143538+3*slot+part))
def quad3Instr (part : Nat) : Instr := if part=0 then .ECALL else if part=1 then .ADDI .x10 .x10 368 else .ADDI .x12 .x12 32

theorem quad3_prefix_length : quad3Prefix.length=143538 := by
  unfold quad3Prefix
  simp only [List.length_append]
  rw [quad2_prefix_length,quad2_code_length]
  rfl

theorem quad3_code_length : quad3Code.length=49152 := by
  simp only [quad3Code,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

theorem fetch_quad3 (slot : Fin 16384) (part : Fin 3) (s : MachineState)
    (pc : s.pc=quad3PC slot.val part.val) : fetch image s=some (.base (quad3Instr part.val)) := by
  apply fetch_code_index s (143538+3*slot.val+part.val) (by have := slot.isLt;have := part.isLt;omega) pc
  have atIndex := code_segment_at quad3Prefix quad3Code quad3Suffix
    (by unfold image quad3Prefix quad2Prefix quadPrefix quad3Suffix;simp only [List.append_assoc]) (3*slot.val+part.val)
    (by rw [quad3_code_length];have := slot.isLt;have := part.isLt;omega)
  rw [quad3_prefix_length] at atIndex
  simp only [←Nat.add_assoc] at atIndex
  rw [atIndex]
  unfold quad3Code
  have repeated := repeated_code_at quadWords 16384 slot.val part.val slot.isLt part.isLt
  change ((List.replicate 16384 quadWords).flatten)[3*slot.val+part.val]?=quadWords[part.val]? at repeated
  rw [repeated]
  fin_cases part <;> change decodeInstruction _=some (.base _) <;> unfold quad3Instr decodeInstruction <;> rfl


end TwoPermutationPrototype.Quad.Commit
