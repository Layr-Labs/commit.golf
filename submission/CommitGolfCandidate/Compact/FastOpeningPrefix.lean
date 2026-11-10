import CommitGolfCandidate.Compact.FastOpeningImage
/-! The unchanged nonce-address calculation, seven nonce-copy instructions and
compact path-counter setup, fetched from the new opening image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def fastPrepareInstructions : List Instr :=
  [.LD .x20 .x24 0,.SLLI .x6 .x20 1,.ADD .x6 .x6 .x20,
   .SLLI .x6 .x6 3,.ADD .x23 .x18 .x6]
def fastPreparePrefix (s : MachineState) (count : Nat) : MachineState :=
  (fastPrepareInstructions.take count).foldl execInstrBr s

theorem fast_prepare_same (s : MachineState) :
    fastPreparePrefix s 5=openingPositionPreparedState s := rfl

theorem fast_prepare (s : MachineState) (pc : s.pc=4176)
    (indexValid : accessValid (s.getReg .x24) 8=true) (fuel : Nat) (coins : Bool) :
    execute fastImage (5+fuel) s coins=
      (do let result ← execute fastImage fuel (openingPositionPreparedState s) coins
          return result.charge 5 0) := by
  rw [←fast_prepare_same]
  apply execute_unit_steps (states := fastPreparePrefix s)
  intro i hi
  refine ⟨.base ((fastPrepareInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have currentPC : (fastPreparePrefix s i).pc=BitVec.ofNat 64 (4176+4*i) := by
      interval_cases i <;>
        simp [fastPreparePrefix,fastPrepareInstructions,execInstrBr,pc,MachineState.setPC]
    have pcNat : (fastPreparePrefix s i).pc.toNat=4176+4*i := by
      rw [currentPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
    rw [fetch,pcNat,if_pos (by omega)]
    have idx : (4176+4*i-4096)/4=20+i := by omega
    rw [idx]
    interval_cases i <;> rfl
  · interval_cases i
    · simpa [fastPreparePrefix,fastPrepareInstructions,ordinaryStep,memoryArgumentsValid,
        memAccess,signExtend12] using indexValid
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases i <;> rfl

def fastSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 24,.ADD .x20 .x20 .x19,.ADDI .x28 .x0 24,.JAL .x0 12]
def fastSaltPrefix (s : MachineState) (count : Nat) : MachineState :=
  (fastSaltInstructions.take count).foldl execInstrBr s

theorem fast_salt_same (s : MachineState) : fastSaltPrefix s 4=openingSaltAdvancedState s := by
  have expansion (s : MachineState) : openingSaltAdvancedState s=
      ([.ADDI .x25 .x25 24,.ADD .x20 .x20 .x19,.ADDI .x28 .x0 0,
        .SLLI .x28 .x28 11,.ADDI .x28 .x28 24,.BEQ .x28 .x0 64] : List Instr).foldl execInstrBr s := rfl
  rw [expansion]
  simp [fastSaltPrefix,fastSaltInstructions,execInstrBr,signExtend21,signExtend13,
    signExtend12,MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc]
  funext reg
  cases reg <;> rfl

theorem fast_salt_advance (s : MachineState) (pc : s.pc=4224)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (4+fuel) s coins=
      (do let result ← execute fastImage fuel (openingSaltAdvancedState s) coins
          return result.charge 4 0) := by
  rw [←fast_salt_same]
  apply execute_unit_steps (states := fastSaltPrefix s)
  intro i hi
  refine ⟨.base ((fastSaltInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have currentPC : (fastSaltPrefix s i).pc=BitVec.ofNat 64 (4224+4*i) := by
      interval_cases i <;>
        simp [fastSaltPrefix,fastSaltInstructions,execInstrBr,pc,MachineState.setPC]
    have pcNat : (fastSaltPrefix s i).pc.toNat=4224+4*i := by
      rw [currentPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
    rw [fetch,pcNat,if_pos (by omega)]
    have idx : (4224+4*i-4096)/4=32+i := by omega
    rw [idx]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem fast_nonce_fetched : OpeningNonceFetched fastImage := by
  intro s i hi pc
  have pcNat : s.pc.toNat=4196+4*i := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,pcNat,if_pos (by omega)]
  have idx : (4196+4*i-4096)/4=25+i := by omega
  rw [idx]
  interval_cases i <;> rfl

theorem fast_position_setup (s : MachineState) (pc : s.pc=4176)
    (indexValid : accessValid (s.getReg .x24) 8=true)
    (sourceValid : ∀ word : Fin 4,accessValid
      (s.getReg .x18+nonceOffset (s.getMem (s.getReg .x24))+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (s.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (16+fuel) s coins=
      (do let result ← execute fastImage fuel (openingPositionPathState s) coins
          return result.charge 16 0) := by
  let ready := openingPositionPreparedState s
  let copied := openingNonceCopyState ready
  have readyPC : ready.pc=4196 := by
    dsimp only [ready]
    rw [←fast_prepare_same]
    simp [fastPreparePrefix,fastPrepareInstructions,execInstrBr,pc,MachineState.setPC]
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
  rw [show 16+fuel=5+(7+(4+fuel)) by omega,fast_prepare s pc indexValid,
    opening_nonce_execute fastImage fast_nonce_fetched ready readyPC reads writes,
    fast_salt_advance copied copiedPC]
  simp [openingPositionPathState,ready,copied,Execution.charge,←Nat.add_assoc]

theorem fast_position_path_pc (s : MachineState) (pc : s.pc=4176) :
    (openingPositionPathState s).pc=4248 := by
  unfold openingPositionPathState
  rw [←fast_salt_same]
  have noncePC : (openingNonceCopyState (openingPositionPreparedState s)).pc=4224 := by
    rw [opening_nonce_copy_pc,←fast_prepare_same]
    simp [fastPreparePrefix,fastPrepareInstructions,execInstrBr,pc,MachineState.setPC]
  simp [fastSaltPrefix,fastSaltInstructions,execInstrBr,noncePC,signExtend21,MachineState.setPC]
end CommitGolfCandidate.Compact
