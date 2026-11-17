import CommitGolfCandidate.NonceExpandCapacity

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandFooterInstructions : List Instr :=
  [.ADD .x23 .x15 .x17,.ADDI .x23 .x23 4088,.ADD .x25 .x15 .x18,.ADDI .x25 .x25 4088,
    .SUB .x28 .x17 .x6,.SRLI .x28 .x28 3,.BEQ .x28 .x0 8]

def nonceExpandFooterPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceExpandFooterInstructions.take count).foldl execInstrBr state

theorem nonce_expand_footer_prefix_next (state : MachineState) (count : Nat) (bounded : count<7) :
    nonceExpandFooterPrefix state (count+1)=execInstrBr (nonceExpandFooterPrefix state count)
      ((nonceExpandFooterInstructions[count]?).getD .EBREAK) := by
  have inside : count<nonceExpandFooterInstructions.length := by simpa [nonceExpandFooterInstructions] using bounded
  unfold nonceExpandFooterPrefix
  rw [List.take_succ_eq_append_getElem inside,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,getElem?_pos nonceExpandFooterInstructions count inside,Option.getD_some]

theorem nonce_expand_footer_last (state : MachineState) :
    nonceExpandFooterPrefix state 7=execInstrBr (nonceExpandFooterPrefix state 6) (.BEQ .x28 .x0 8) :=
  nonce_expand_footer_prefix_next state 6 (by decide)

attribute [local irreducible] nonceExpandFooterPrefix

theorem nonce_expand_footer_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 6) :
    (nonceExpandFooterPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [nonceExpandFooterPrefix,nonceExpandFooterInstructions,
    execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem nonce_expand_footer_execute (state : MachineState) (pc : state.pc=4980)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (7+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandFooterPrefix state 7) coins
          return result.charge 7 0) := by
  have zero : nonceExpandFooterPrefix state 0=state := by unfold nonceExpandFooterPrefix; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := nonceExpandFooterPrefix state)
  intro count bounded
  refine ⟨.base ((nonceExpandFooterInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
  · apply cap_image_fetch _ _ (221+count) _ (by omega)
    · rw [nonce_expand_footer_prefix_pc state count (by omega),pc]
      interval_cases count <;> rfl
    · interval_cases count <;> rfl
  · rw [nonce_expand_footer_prefix_next state count bounded]
    interval_cases count <;> rfl
  · interval_cases count <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_expand_footer_memory (state : MachineState) :
    (nonceExpandFooterPrefix state 7).mem=state.mem := by
  rw [nonce_expand_footer_last,branch_memory]
  unfold nonceExpandFooterPrefix
  rfl

theorem nonce_expand_footer_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceExpandFooterPrefix state 7).getReg reg=state.getReg reg := by
  rw [nonce_expand_footer_last,branch_register]
  simp only [nonceExpandFooterPrefix,nonceExpandFooterInstructions,List.take,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem nonce_expand_footer_raw (state : MachineState) :
    (nonceExpandFooterPrefix state 6).getReg .x23=(state.getReg .x15+state.getReg .x17)+signExtend12 (4088:BitVec 12) ∧
    (nonceExpandFooterPrefix state 6).getReg .x25=(state.getReg .x15+state.getReg .x18)+signExtend12 (4088:BitVec 12) ∧
    (nonceExpandFooterPrefix state 6).getReg .x28=(state.getReg .x17-state.getReg .x6) >>> 3 := by
  constructor
  · unfold nonceExpandFooterPrefix
    rfl
  · constructor <;> unfold nonceExpandFooterPrefix <;> rfl

theorem nonce_expand_footer_source (state : MachineState) (base length : Nat) (start : 8 ≤ base)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base) (reported : state.getReg .x17=BitVec.ofNat 64 length) :
    (nonceExpandFooterPrefix state 7).getReg .x23=BitVec.ofNat 64 (base+length-8) := by
  rw [nonce_expand_footer_last,branch_register,(nonce_expand_footer_raw state).1,proofBase,reported,
    ←BitVec.ofNat_add,NonceBackwardReady.decrement_eight _ (by omega)]

theorem nonce_expand_footer_target (state : MachineState) (base expanded : Nat) (start : 8 ≤ base)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base) (reported : state.getReg .x18=BitVec.ofNat 64 expanded) :
    (nonceExpandFooterPrefix state 7).getReg .x25=BitVec.ofNat 64 (base+expanded-8) := by
  rw [nonce_expand_footer_last,branch_register,(nonce_expand_footer_raw state).2.1,proofBase,reported,
    ←BitVec.ofNat_add,NonceBackwardReady.decrement_eight _ (by omega)]

theorem nonce_expand_footer_count (state : MachineState) (length minimum : Nat)
    (small : length<2^64) (enough : minimum ≤ length)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) (required : state.getReg .x6=BitVec.ofNat 64 minimum) :
    (nonceExpandFooterPrefix state 7).getReg .x28=BitVec.ofNat 64 ((length-minimum)/8) := by
  rw [nonce_expand_footer_last,branch_register,(nonce_expand_footer_raw state).2.2,reported,required,
    BitVec.ofNat_sub_ofNat_of_le length minimum (by omega) enough]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change (length-minimum)%2^64/8=((length-minimum)/8)%2^64
  rw [Nat.mod_eq_of_lt (by omega : length-minimum<2^64),
    Nat.mod_eq_of_lt (by omega : (length-minimum)/8<2^64)]

theorem nonce_expand_footer_pc (state : MachineState) (pc : state.pc=4980) (length minimum : Nat)
    (small : length<2^64) (enough : minimum ≤ length)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) (required : state.getReg .x6=BitVec.ofNat 64 minimum) :
    (nonceExpandFooterPrefix state 7).pc=if (length-minimum)/8=0 then 5012 else 5008 := by
  have counter:=nonce_expand_footer_count state length minimum small enough reported required
  rw [nonce_expand_footer_last,branch_register] at counter
  have zero : (BitVec.ofNat 64 ((length-minimum)/8) : Word)=0 ↔ (length-minimum)/8=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      change ((length-minimum)/8)%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt (by omega)] at numeric
      exact numeric
    · rintro equal
      rw [equal]
      rfl
  rw [nonce_expand_footer_last]
  simp only [execInstrBr,counter,show (nonceExpandFooterPrefix state 6).getReg .x0=0 from rfl,beq_iff_eq,zero]
  by_cases empty : (length-minimum)/8=0 <;>
    simp [empty,MachineState.setPC,nonce_expand_footer_prefix_pc state 6 (by decide),pc,signExtend13]

end CommitGolfCandidate
