import CommitGolfCandidate.NonceExpandRegisters
import CommitGolfCandidate.NonceCheckOldTail
import CommitGolfCandidate.NonceCodecExpandIndex

/-! The old checker input is obtained by deterministic expansion of the
adversary's packed proof, preserving its commitment, positions and values. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

def nonceExpandedInput (input : CheckInput) : CheckInput :=
  { input with proof := NonceCodec.expand 0 input.positions.card input.proof }

theorem nonce_expanded_input_length (input : CheckInput)
    (enough : 536*input.positions.card ≤ input.proof.length) :
    (nonceExpandedInput input).proof.length=input.proof.length+8*input.positions.card :=
  NonceCodec.expand_length 0 _ _ enough

private theorem initial_register_other (program : Submission) (input : CheckInput) (proof : Proof)
    (reg : Reg) (outside : reg ≠ .x17) :
    (program.initialState .check {input with proof:=proof}).getReg reg=
      (program.initialState .check input).getReg reg := by
  unfold Submission.initialState
  rw [MachineState.getReg_setReg_ne _ .x17 reg _ (Ne.symm outside),
    MachineState.getReg_setReg_ne _ .x17 reg _ (Ne.symm outside)]
  simp only [inputCount]
  cases reg <;> simp only [MachineState.getReg,MachineState.setReg,BEq.beq,
    decide_false,decide_true,ite_true,ite_false]

private theorem saved_reset (program : Submission) (input : CheckInput) (reg : Reg)
    (reset : reg ∈ nonceExpandResetRegisters) :
    (execInstrBr (program.initialState .check input) (.ADDI .x26 .x11 0)).getReg reg=0 := by
  cases reg <;> simp only [nonceExpandResetRegisters,List.mem_cons,List.not_mem_nil,
    reduceCtorEq,false_or,or_false,true_or] at reset <;> first | contradiction | rfl

private theorem initial_length (program : Submission) (input : CheckInput) :
    (program.initialState .check input).getReg .x17=BitVec.ofNat 64 input.proof.length := rfl

private theorem saved_other (state : MachineState) (reg : Reg) (outside : reg ≠ .x26) :
    (execInstrBr state (.ADDI .x26 .x11 0)).getReg reg=state.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

private theorem saved_root (state : MachineState) :
    (execInstrBr state (.ADDI .x26 .x11 0)).getReg .x26=state.getReg .x11 := by
  simp [execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]

theorem nonce_expanded_input_register (input : CheckInput) (reg : Reg) (outside : reg ≠ .x17) :
    (capProgram.initialState .check (nonceExpandedInput input)).getReg reg=
      (capProgram.initialState .check input).getReg reg :=
  initial_register_other capProgram input _ reg outside

theorem nonce_expand_initial_registers (input : CheckInput) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length
      ((capProgram.initialState .check input).setPC 4896))
    (countEq : count=input.positions.card) (lengthEq : length=input.proof.length)
    (enough : 536*input.positions.card ≤ input.proof.length) (reg : Reg) :
    (nonceExpandCoreState ((capProgram.initialState .check input).setPC 4896) count length).getReg reg=
      (nonceOldCheckTailState (nonceExpandedInput input)).getReg reg := by
  by_cases reset : reg ∈ nonceExpandResetRegisters
  · rw [nonce_expand_core_reset _ count length reg reset]
    exact (saved_reset capProgram (nonceExpandedInput input) reg reset).symm
  · by_cases isLength : reg=.x17
    · subst reg
      rw [(nonce_expand_core_metadata _ base count length facts).1]
      rw [nonceOldCheckTailState,saved_other _ .x17 (by decide),initial_length]
      rw [nonce_expanded_input_length input enough,countEq,lengthEq]
    · by_cases isRoot : reg=.x26
      · subst reg
        rw [(nonce_expand_core_metadata _ base count length facts).2]
        rw [nonceOldCheckTailState,saved_root,nonce_expanded_input_register input .x11 (by decide)]
        rfl
      · rw [nonce_expand_core_register _ count length reg ⟨isLength,isRoot,reset⟩]
        rw [MachineState.getReg_setPC]
        change _=(execInstrBr (capProgram.initialState .check (nonceExpandedInput input)) (.ADDI .x26 .x11 0)).getReg reg
        rw [show (execInstrBr (capProgram.initialState .check (nonceExpandedInput input)) (.ADDI .x26 .x11 0)).getReg reg=
            (capProgram.initialState .check (nonceExpandedInput input)).getReg reg by
          simp only [execInstrBr,MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm isRoot)]]
        exact (nonce_expanded_input_register input reg isLength).symm
end CommitGolfCandidate
