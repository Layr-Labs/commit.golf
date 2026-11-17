import CommitGolfCandidate.Compact.Opening
/-! A branch-free fourteen-instruction path step. The reference state has the same
registers and memory; only its physical program counter is relocated. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def unrolledPathInstructions : List Instr :=
  [.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7,
   .LD .x6 .x23 0,.SD .x25 .x6 0,.LD .x6 .x23 8,.SD .x25 .x6 8,
   .LD .x6 .x23 16,.SD .x25 .x6 16,.LD .x6 .x23 24,.SD .x25 .x6 24,
   .ADDI .x25 .x25 32,.SRLI .x20 .x20 1,.ADDI .x28 .x28 (-1)]

def unrolledPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (unrolledPathInstructions.take count).foldl execInstrBr state

theorem unrolled_path_same (state : MachineState) :
    unrolledPathPrefix state 14 = (openingPathState state).setPC (state.pc+56) := by
  have prepared (s : MachineState) : openingPathPreparedState s =
      ([.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7] : List Instr).foldl execInstrBr s := rfl
  unfold openingPathState openingLatchState openingPathAdvancedState
  rw [opening_copy_expansion,prepared]
  simp [unrolledPathPrefix,unrolledPathInstructions,execInstrBr,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,
    MachineState.setMem,MachineState.getMem,BitVec.add_assoc,signExtend12,
    BitVec.sub_eq_add_neg]

private theorem fast_reg_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

def UnrolledPathFetched (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Nat), i<14 → s.pc=base+BitVec.ofNat 64 (4*i) →
    fetch image s=some (.base ((unrolledPathInstructions[i]?).getD .EBREAK))

theorem unrolled_path_execute (image : Image) (base : Word)
    (fetched : UnrolledPathFetched image base) (state : MachineState) (pc : state.pc=base)
    (sourceValid : ∀ word : Fin 4,accessValid
      (state.getReg .x9+((state.getReg .x20 ^^^ 1)<<<5)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (state.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute image (14+fuel) state coins=
      (do let result ← execute image fuel
            ((openingPathState state).setPC (state.pc+56)) coins
          return result.charge 14 0) := by
  rw [←unrolled_path_same]
  apply execute_unit_steps (states := unrolledPathPrefix state)
  intro i hi
  refine ⟨.base ((unrolledPathInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [unrolledPathPrefix,unrolledPathInstructions,execInstrBr,
        MachineState.setPC,pc,BitVec.add_assoc]
  · have destination (j : Nat) (hj : j≤11) :
        (unrolledPathPrefix state j).getReg .x25=state.getReg .x25 := by
      interval_cases j <;>
        simp [unrolledPathPrefix,unrolledPathInstructions,execInstrBr,
          MachineState.getReg_setPC,fast_reg_mem,MachineState.getReg_setReg_ne]
    have source (j : Nat) (hj : 3≤j ∧ j≤11) :
        (unrolledPathPrefix state j).getReg .x23=
          state.getReg .x9+((state.getReg .x20 ^^^ 1)<<<5) := by
      obtain ⟨lower,upper⟩ := hj
      interval_cases j <;>
        simp [unrolledPathPrefix,unrolledPathInstructions,execInstrBr,signExtend12,
          MachineState.getReg_setPC,fast_reg_mem,MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
    have s0 := sourceValid ⟨0,by decide⟩
    have s1 := sourceValid ⟨1,by decide⟩
    have s2 := sourceValid ⟨2,by decide⟩
    have s3 := sourceValid ⟨3,by decide⟩
    have d0 := destinationValid ⟨0,by decide⟩
    have d1 := destinationValid ⟨1,by decide⟩
    have d2 := destinationValid ⟨2,by decide⟩
    have d3 := destinationValid ⟨3,by decide⟩
    have valid : memoryArgumentsValid (unrolledPathPrefix state i)
        ((unrolledPathInstructions[i]?).getD .EBREAK)=true := by
      interval_cases i <;>
        simp only [unrolledPathInstructions,List.getElem?_cons_zero,
          List.getElem?_cons_succ,Option.getD_some,memoryArgumentsValid,memAccess,
          signExtend12,
          source 3 (by decide),source 5 (by decide),source 7 (by decide),source 9 (by decide),
          destination 4 (by decide),destination 6 (by decide),
          destination 8 (by decide),destination 10 (by decide)] <;>
        first | rfl | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [unrolledPathInstructions,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep,valid,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl
end CommitGolfCandidate.Compact
