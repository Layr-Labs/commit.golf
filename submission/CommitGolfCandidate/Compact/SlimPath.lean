import CommitGolfCandidate.Compact.FastOpeningPath
/-! Thirteen instructions copy one sibling and move to its parent. The path
counter remains fixed; the result equals the existing reference path state with
its counter restored and its physical program counter relocated. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def slimPathInstructions : List Instr :=
  [.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7,
   .LD .x6 .x23 0,.SD .x25 .x6 0,.LD .x6 .x23 8,.SD .x25 .x6 8,
   .LD .x6 .x23 16,.SD .x25 .x6 16,.LD .x6 .x23 24,.SD .x25 .x6 24,
   .ADDI .x25 .x25 32,.SRLI .x20 .x20 1]

def slimPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (slimPathInstructions.take count).foldl execInstrBr state

private theorem slim_reg_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

private theorem slim_restore (s : MachineState) (a b pc next : Word) :
    (((s.setReg .x28 a).setPC pc).setReg .x28 b).setPC next=
      (s.setReg .x28 b).setPC next := by
  cases s
  simp [MachineState.setReg,MachineState.setPC]
  funext reg
  cases reg <;> rfl

private theorem slim_own (s : MachineState) : s.setReg .x28 (s.getReg .x28)=s := by
  cases s
  simp [MachineState.setReg,MachineState.getReg]
  funext reg
  cases reg <;> rfl

theorem slim_path_same (state : MachineState) :
    slimPathPrefix state 13 = ((openingPathState state).setReg .x28 (state.getReg .x28)).setPC (state.pc+52) := by
  let t := slimPathPrefix state 13
  have counter : t.getReg .x28=state.getReg .x28 := by
    simp [t,slimPathPrefix,slimPathInstructions,execInstrBr,
      MachineState.getReg_setPC,slim_reg_mem,MachineState.getReg_setReg_ne]
  have pc : t.pc=state.pc+52 := by
    simp [t,slimPathPrefix,slimPathInstructions,execInstrBr,MachineState.setPC,BitVec.add_assoc]
  have fourteen : unrolledPathPrefix state 14=
      (t.setReg .x28 (t.getReg .x28-1)).setPC (t.pc+4) := by
    change execInstrBr t (.ADDI .x28 .x28 (-1))=_
    simp [execInstrBr,signExtend12,BitVec.sub_eq_add_neg]
  have restored : (t.setReg .x28 (state.getReg .x28)).setPC (state.pc+52)=t := by
    rw [←counter,slim_own,←pc]
    cases t
    rfl
  have same := congrArg (fun t : MachineState =>
    (t.setReg .x28 (state.getReg .x28)).setPC (state.pc+52)) (unrolled_path_same state)
  rw [fourteen,slim_restore,restored] at same
  exact same.trans (by rfl)

def SlimPathFetched (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Nat), i<13 → s.pc=base+BitVec.ofNat 64 (4*i) →
    fetch image s=some (.base ((slimPathInstructions[i]?).getD .EBREAK))

theorem slim_path_execute (image : Image) (base : Word)
    (fetched : SlimPathFetched image base) (state : MachineState) (pc : state.pc=base)
    (sourceValid : ∀ word : Fin 4,accessValid
      (state.getReg .x9+((state.getReg .x20 ^^^ 1)<<<5)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (state.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute image (13+fuel) state coins=
      (do let result ← execute image fuel
            (((openingPathState state).setReg .x28 (state.getReg .x28)).setPC (state.pc+52)) coins
          return result.charge 13 0) := by
  rw [←slim_path_same]
  apply execute_unit_steps (states := slimPathPrefix state)
  intro i hi
  refine ⟨.base ((slimPathInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [slimPathPrefix,slimPathInstructions,execInstrBr,
        MachineState.setPC,pc,BitVec.add_assoc]
  · have destination (j : Nat) (hj : j≤11) :
        (slimPathPrefix state j).getReg .x25=state.getReg .x25 := by
      interval_cases j <;>
        simp [slimPathPrefix,slimPathInstructions,execInstrBr,
          MachineState.getReg_setPC,slim_reg_mem,MachineState.getReg_setReg_ne]
    have source (j : Nat) (hj : 3≤j ∧ j≤11) :
        (slimPathPrefix state j).getReg .x23=
          state.getReg .x9+((state.getReg .x20 ^^^ 1)<<<5) := by
      obtain ⟨lower,upper⟩ := hj
      interval_cases j <;>
        simp [slimPathPrefix,slimPathInstructions,execInstrBr,signExtend12,
          MachineState.getReg_setPC,slim_reg_mem,MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
    have s0 := sourceValid ⟨0,by decide⟩
    have s1 := sourceValid ⟨1,by decide⟩
    have s2 := sourceValid ⟨2,by decide⟩
    have s3 := sourceValid ⟨3,by decide⟩
    have d0 := destinationValid ⟨0,by decide⟩
    have d1 := destinationValid ⟨1,by decide⟩
    have d2 := destinationValid ⟨2,by decide⟩
    have d3 := destinationValid ⟨3,by decide⟩
    have valid : memoryArgumentsValid (slimPathPrefix state i)
        ((slimPathInstructions[i]?).getD .EBREAK)=true := by
      interval_cases i <;>
        simp only [slimPathInstructions,List.getElem?_cons_zero,
          List.getElem?_cons_succ,Option.getD_some,memoryArgumentsValid,memAccess,
          signExtend12,
          source 3 (by decide),source 5 (by decide),source 7 (by decide),source 9 (by decide),
          destination 4 (by decide),destination 6 (by decide),
          destination 8 (by decide),destination 10 (by decide)] <;>
        first | rfl | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [slimPathInstructions,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep,valid,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl
end CommitGolfCandidate.Compact
