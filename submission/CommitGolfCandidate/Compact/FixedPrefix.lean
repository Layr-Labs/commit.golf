import CommitGolfCandidate.Compact.FixedImage
import CommitGolfCandidate.Compact.SlimPrefix
/-! Fourteen-cycle index, nonce-copy and salt-address prefix. The path follows directly; only the physical PC differs from the reference path state. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def fixedPrepareInstructions : List Instr :=
  [.LD .x20 .x24 0,.SLLI .x6 .x20 1,.ADD .x6 .x6 .x20,
   .SLLI .x6 .x6 3,.ADD .x23 .x18 .x6]
def fixedPreparePrefix (s : MachineState) (count : Nat) : MachineState :=
  (fixedPrepareInstructions.take count).foldl execInstrBr s

theorem fixed_prepare_same (s : MachineState) :
    fixedPreparePrefix s 5=openingPositionPreparedState s := rfl

theorem fixed_prepare (s : MachineState) (pc : s.pc=4176)
    (indexValid : accessValid (s.getReg .x24) 8=true) (fuel : Nat) (coins : Bool) :
    execute fixedImage (5+fuel) s coins=
      (do let result ← execute fixedImage fuel (openingPositionPreparedState s) coins
          return result.charge 5 0) := by
  rw [←fixed_prepare_same]
  apply execute_unit_steps (states := fixedPreparePrefix s)
  intro i hi
  refine ⟨.base ((fixedPrepareInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have currentPC : (fixedPreparePrefix s i).pc=BitVec.ofNat 64 (4176+4*i) := by
      interval_cases i <;>
        simp [fixedPreparePrefix,fixedPrepareInstructions,execInstrBr,pc,MachineState.setPC]
    have pcNat : (fixedPreparePrefix s i).pc.toNat=4176+4*i := by
      rw [currentPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
    rw [fetch,pcNat,if_pos (by omega)]
    have idx : (4176+4*i-4096)/4=20+i := by omega
    rw [idx]
    interval_cases i <;> rfl
  · interval_cases i
    · simpa [fixedPreparePrefix,fixedPrepareInstructions,ordinaryStep,memoryArgumentsValid,
        memAccess,signExtend12] using indexValid
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases i <;> rfl

def fixedSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 24,.ADD .x20 .x20 .x19]
def fixedSaltPrefix (s : MachineState) (count : Nat) : MachineState :=
  (fixedSaltInstructions.take count).foldl execInstrBr s

theorem fixed_salt_same (s : MachineState) (counterZero : s.getReg .x28=0) : fixedSaltPrefix s 2=((openingSaltAdvancedState s).setReg .x28 0).setPC (s.pc+8) := by
  have expansion (s : MachineState) : openingSaltAdvancedState s=
      ([.ADDI .x25 .x25 24,.ADD .x20 .x20 .x19,.ADDI .x28 .x0 0,
        .SLLI .x28 .x28 11,.ADDI .x28 .x28 24,.BEQ .x28 .x0 64] : List Instr).foldl execInstrBr s := rfl
  rw [expansion]
  simp [fixedSaltPrefix,fixedSaltInstructions,execInstrBr,signExtend21,signExtend13,
    signExtend12,MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc] at counterZero ⊢
  funext reg
  cases reg <;> simp_all

theorem fixed_salt_advance (s : MachineState) (pc : s.pc=4224)
    (counterZero : s.getReg .x28=0) (fuel : Nat) (coins : Bool) :
    execute fixedImage (2+fuel) s coins=
      (do let result ← execute fixedImage fuel (((openingSaltAdvancedState s).setReg .x28 0).setPC (s.pc+8)) coins
          return result.charge 2 0) := by
  rw [←fixed_salt_same s counterZero]
  apply execute_unit_steps (states := fixedSaltPrefix s)
  intro i hi
  refine ⟨.base ((fixedSaltInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have currentPC : (fixedSaltPrefix s i).pc=BitVec.ofNat 64 (4224+4*i) := by
      interval_cases i <;>
        simp [fixedSaltPrefix,fixedSaltInstructions,execInstrBr,pc,MachineState.setPC]
    have pcNat : (fixedSaltPrefix s i).pc.toNat=4224+4*i := by
      rw [currentPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
    rw [fetch,pcNat,if_pos (by omega)]
    have idx : (4224+4*i-4096)/4=32+i := by omega
    rw [idx]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem fixed_nonce_fetched : OpeningNonceFetched fixedImage := by
  intro s i hi pc
  have pcNat : s.pc.toNat=4196+4*i := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,pcNat,if_pos (by omega)]
  have idx : (4196+4*i-4096)/4=25+i := by omega
  rw [idx]
  interval_cases i <;> rfl

theorem fixed_position_setup (s : MachineState) (pc : s.pc=4176)
    (counterZero : s.getReg .x28=0)
    (indexValid : accessValid (s.getReg .x24) 8=true)
    (sourceValid : ∀ word : Fin 4,accessValid
      (s.getReg .x18+nonceOffset (s.getMem (s.getReg .x24))+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (s.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fixedImage (14+fuel) s coins=
      (do let result ← execute fixedImage fuel (((openingPositionPathState s).setReg .x28 0).setPC 4232) coins
          return result.charge 14 0) := by
  let ready := openingPositionPreparedState s
  let copied := openingNonceCopyState ready
  have readyPC : ready.pc=4196 := by
    dsimp only [ready]
    rw [←fixed_prepare_same]
    simp [fixedPreparePrefix,fixedPrepareInstructions,execInstrBr,pc,MachineState.setPC]
  have copiedPC : copied.pc=4224 := by rw [opening_nonce_copy_pc,readyPC];rfl
  have reads : ∀ word : Fin 3,accessValid
      (ready.getReg .x23+BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro word
    rw [(opening_position_prepared s).2]
    exact sourceValid ⟨word.val,by omega⟩
  have writes : ∀ word : Fin 4,accessValid
      (ready.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro word
    rw [opening_position_prepare_register s .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  have copiedZero : copied.getReg .x28=0 := by
    rw [opening_nonce_copy_register ready .x28 (by decide),
      opening_position_prepare_register s .x28 (by decide) (by decide) (by decide),counterZero]
  rw [show 14+fuel=5+(7+(2+fuel)) by omega,fixed_prepare s pc indexValid,
    opening_nonce_execute fixedImage fixed_nonce_fetched ready readyPC reads writes,
    fixed_salt_advance copied copiedPC copiedZero]
  simp [openingPositionPathState,ready,copied,copiedPC,Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Compact
