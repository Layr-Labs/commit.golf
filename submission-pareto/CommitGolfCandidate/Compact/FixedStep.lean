import CommitGolfCandidate.Compact.FixedImage
/-! Each relocated twelve-instruction body is executed by the actual image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
attribute [local irreducible] execute
private theorem reg_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

private theorem immediate_offset (level word : Nat) (bound : level<24) (inside : word<4) :
    signExtend12 (BitVec.ofNat 12 (32*level+8*word))=
      BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word) := by
  interval_cases level <;> interval_cases word <;> rfl

theorem fixed_step_execute (level : Nat) (bound : level<24) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4232+48*level))
    (sourceValid : ∀ word : Fin 4,accessValid
      (s.getReg .x9+((s.getReg .x20 ^^^ 1)<<<5)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (s.getReg .x25+BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fixedImage (12+fuel) s coins=
      (do let result ← execute fixedImage fuel (fixedPathPrefix s level 12) coins
          return result.charge 12 0) := by
  apply execute_unit_steps (states := fixedPathPrefix s level)
  intro i hi
  refine ⟨.base (((fixedPathInstructions level)[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fixed_path_fetched level i bound hi
    have currentPC : (fixedPathPrefix s level i).pc=s.pc+BitVec.ofNat 64 (4*i) := by
      interval_cases i <;>
        simp [fixedPathPrefix,fixedPathInstructions,execInstrBr,MachineState.setPC,
          BitVec.add_assoc]
    rw [currentPC,pc,←BitVec.ofNat_add]
  · have destination (j : Nat) (hj : j≤11) :
        (fixedPathPrefix s level j).getReg .x25=s.getReg .x25 := by
      interval_cases j <;>
        simp [fixedPathPrefix,fixedPathInstructions,execInstrBr,
          MachineState.getReg_setPC,reg_mem,MachineState.getReg_setReg_ne]
    have source (j : Nat) (hj : 3≤j ∧ j≤11) :
        (fixedPathPrefix s level j).getReg .x23=
          s.getReg .x9+((s.getReg .x20 ^^^ 1)<<<5) := by
      obtain ⟨lower,upper⟩ := hj
      interval_cases j <;>
        simp [fixedPathPrefix,fixedPathInstructions,execInstrBr,signExtend12,
          MachineState.getReg_setPC,reg_mem,MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
    have s0 := sourceValid ⟨0,by decide⟩
    have s1 := sourceValid ⟨1,by decide⟩
    have s2 := sourceValid ⟨2,by decide⟩
    have s3 := sourceValid ⟨3,by decide⟩
    have d0 := destinationValid ⟨0,by decide⟩
    have d1 := destinationValid ⟨1,by decide⟩
    have d2 := destinationValid ⟨2,by decide⟩
    have d3 := destinationValid ⟨3,by decide⟩
    have off0 := immediate_offset level 0 bound (by decide)
    have off1 := immediate_offset level 1 bound (by decide)
    have off2 := immediate_offset level 2 bound (by decide)
    have off3 := immediate_offset level 3 bound (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at off0 off1 off2 off3
    have valid : memoryArgumentsValid (fixedPathPrefix s level i)
        (((fixedPathInstructions level)[i]?).getD .EBREAK)=true := by
      interval_cases i <;>
        simp only [fixedPathInstructions,List.getElem?_cons_zero,
          List.getElem?_cons_succ,Option.getD_some,memoryArgumentsValid,memAccess,
          source 3 (by decide),source 5 (by decide),source 7 (by decide),source 9 (by decide),
          destination 4 (by decide),destination 6 (by decide),
          destination 8 (by decide),destination 10 (by decide)] <;>
        (try simp only [off0,off1,off2,off3]) <;>
        (try simp only [show signExtend12 0=(0#64) by decide,
          show signExtend12 8=(8#64) by decide,
          show signExtend12 16=(16#64) by decide,
          show signExtend12 24=(24#64) by decide,BitVec.add_assoc]) <;>
        first | rfl | (simpa only [BitVec.add_assoc] using s0) |
          (simpa only [BitVec.add_assoc] using s1) |
          (simpa only [BitVec.add_assoc] using s2) |
          (simpa only [BitVec.add_assoc] using s3) |
          (simpa only [BitVec.add_assoc] using d0) |
          (simpa only [BitVec.add_assoc] using d1) |
          (simpa only [BitVec.add_assoc] using d2) |
          (simpa only [BitVec.add_assoc] using d3)
    interval_cases i <;>
      simp only [fixedPathInstructions,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep,valid,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl
end CommitGolfCandidate.Compact
