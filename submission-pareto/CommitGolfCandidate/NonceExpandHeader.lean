import CommitGolfCandidate.NonceExpandFinish

/-! The first real expansion guard saves the ABI root/count and checks the
packed proof's byte alignment before any proof memory is read or written. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandHeaderInstructions : List Instr :=
  [.ADDI .x26 .x11 0,.ADDI .x24 .x16 0,.ANDI .x6 .x17 7,.BNE .x6 .x0 8092]

def nonceExpandHeaderPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceExpandHeaderInstructions.take count).foldl execInstrBr state

theorem nonce_expand_header_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 3) :
    (nonceExpandHeaderPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [nonceExpandHeaderPrefix,nonceExpandHeaderInstructions,
    execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem nonce_expand_header_execute (state : MachineState) (pc : state.pc=4896)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (4+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandHeaderPrefix state 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := nonceExpandHeaderPrefix state)
  intro count bounded
  refine ⟨.base ((nonceExpandHeaderInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
  · apply cap_image_fetch _ _ (200+count) _ (by omega)
    · rw [nonce_expand_header_prefix_pc state count (by omega),pc]
      interval_cases count <;> rfl
    · interval_cases count <;> rfl
  · interval_cases count <;> rfl
  · interval_cases count <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x6 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x6 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_expand_header_memory (state : MachineState) :
    (nonceExpandHeaderPrefix state 4).mem=state.mem := by
  change (execInstrBr (nonceExpandHeaderPrefix state 3) (.BNE .x6 .x0 8092)).mem=_
  rw [branch_memory]
  rfl

theorem nonce_expand_header_low (state : MachineState) :
    (nonceExpandHeaderPrefix state 3).getReg .x6=state.getReg .x17 &&& 7 := by
  simp [nonceExpandHeaderPrefix,nonceExpandHeaderInstructions,execInstrBr,signExtend12,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem nonce_expand_header_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x24 ∧ reg ≠ .x26) :
    (nonceExpandHeaderPrefix state 4).getReg reg=state.getReg reg := by
  change (execInstrBr (nonceExpandHeaderPrefix state 3) (.BNE .x6 .x0 8092)).getReg reg=_
  rw [branch_register]
  simp only [nonceExpandHeaderPrefix,nonceExpandHeaderInstructions,List.take,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem nonce_expand_header_saved (state : MachineState) :
    (nonceExpandHeaderPrefix state 4).getReg .x26=state.getReg .x11 ∧
    (nonceExpandHeaderPrefix state 4).getReg .x24=state.getReg .x16 := by
  constructor <;>
    change (execInstrBr (nonceExpandHeaderPrefix state 3) (.BNE .x6 .x0 8092)).getReg _=_
  all_goals rw [branch_register]
  all_goals simp [nonceExpandHeaderPrefix,nonceExpandHeaderInstructions,execInstrBr,signExtend12,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem nonce_expand_header_pc (state : MachineState) (pc : state.pc=4896)
    (length : Nat) (small : length<2^64) (reported : state.getReg .x17=BitVec.ofNat 64 length) :
    (nonceExpandHeaderPrefix state 4).pc=if length%8=0 then 4912 else 4808 := by
  have low : BitVec.ofNat 64 length &&& (7:Word)=BitVec.ofNat 64 (length%8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    change length &&& (2^3-1)=(length%8)%2^64
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by omega : length%8<2^64)]
  have zero : (BitVec.ofNat 64 (length%8) : Word)=0 ↔ length%8=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      change (length%8)%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt (by omega)] at numeric
      exact numeric
    · rintro equal
      rw [equal]
      rfl
  change (execInstrBr (nonceExpandHeaderPrefix state 3) (.BNE .x6 .x0 8092)).pc=_
  simp only [execInstrBr,nonce_expand_header_low,reported,low,
    show (nonceExpandHeaderPrefix state 3).getReg .x0=0 from rfl,bne_iff_ne,ne_eq,zero]
  by_cases aligned : length%8=0 <;>
    simp [aligned,MachineState.setPC,nonce_expand_header_prefix_pc state 3 (by decide),pc,signExtend13]

end CommitGolfCandidate
