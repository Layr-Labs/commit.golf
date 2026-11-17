import CommitGolfCandidate.NonceCompactCall
import CommitGolfCandidate.NonceCopyMemory

/-! One straight-line compacting record in the actual image: sixty-seven
load/store pairs with fixed offsets (three nonce words, the padding word skipped,
sixty-four sibling words), the two pointer advances and the counted back-edge.
Each pair costs two cycles; the whole record costs 138. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open NonceCopyMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Source word of the `index`-th output word: the padding word 3 is skipped. -/
def nonceRecordSourceWord (index : Nat) : Nat := if index<3 then index else index+1

def nonceRecordLoad (index : Nat) : Instr :=
  .LD .x6 .x23 (BitVec.ofNat 12 (8*nonceRecordSourceWord index))

def nonceRecordStore (index : Nat) : Instr :=
  .SD .x25 .x6 (BitVec.ofNat 12 (8*index))

def nonceRecordPair (state : MachineState) (index : Nat) : MachineState :=
  execInstrBr (execInstrBr state (nonceRecordLoad index)) (nonceRecordStore index)

/-- The first `count` load/store pairs of the block. -/
def nonceRecordPairs (state : MachineState) : Nat → MachineState
  | 0 => state
  | count+1 => nonceRecordPair (nonceRecordPairs state count) count

/-- The three pointer/counter advances of the block. -/
def nonceRecordTailAdds (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr state (.ADDI .x23 .x23 544)) (.ADDI .x25 .x25 536))
    (.ADDI .x24 .x24 4095)

def nonceRecordTailState (state : MachineState) : MachineState :=
  execInstrBr (nonceRecordTailAdds state) (.BNE .x24 .x0 7644)

def nonceCompactRecordState (state : MachineState) : MachineState :=
  nonceRecordTailState (nonceRecordPairs state 67)

theorem nonce_record_source_le (index : Nat) :
    index ≤ nonceRecordSourceWord index ∧ nonceRecordSourceWord index ≤ index+1 := by
  unfold nonceRecordSourceWord
  split <;> omega

theorem nonce_record_offset (value : Nat) (small : value<2048) :
    signExtend12 (BitVec.ofNat 12 value)=BitVec.ofNat 64 value := by
  have notNeg : (BitVec.ofNat 12 value).msb=false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega
  rw [signExtend12, BitVec.signExtend_eq_setWidth_of_msb_false notNeg]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem nonce_record_target_address (state : MachineState) (target index : Nat)
    (targetReg : state.getReg .x25=BitVec.ofNat 64 target) (inside : index<67) :
    state.getReg .x25+signExtend12 (BitVec.ofNat 12 (8*index))=address target index := by
  rw [targetReg, nonce_record_offset _ (by omega), ← BitVec.ofNat_add]
  rfl

theorem nonce_record_source_address (state : MachineState) (source index : Nat)
    (sourceReg : state.getReg .x23=BitVec.ofNat 64 source) (inside : index<67) :
    state.getReg .x23+signExtend12 (BitVec.ofNat 12 (8*nonceRecordSourceWord index))=
      address source (nonceRecordSourceWord index) := by
  have bound:=nonce_record_source_le index
  rw [sourceReg, nonce_record_offset _ (by omega), ← BitVec.ofNat_add]
  rfl

theorem nonce_record_pair_pc (state : MachineState) (index : Nat) :
    (nonceRecordPair state index).pc=state.pc+8 := by
  simp only [nonceRecordPair, nonceRecordLoad, nonceRecordStore, execInstrBr, MachineState.setPC,
    MachineState.setReg, MachineState.setMem, BitVec.add_assoc]
  rfl

theorem nonce_record_pair_register (state : MachineState) (index : Nat) (reg : Reg)
    (outside : reg ≠ .x6) :
    (nonceRecordPair state index).getReg reg=state.getReg reg := by
  have memory (current : MachineState) (location value : Word) :
      (current.setMem location value).getReg reg=current.getReg reg := by
    cases reg <;> rfl
  simp only [nonceRecordPair, nonceRecordLoad, nonceRecordStore, execInstrBr,
    MachineState.getReg_setPC, memory]
  exact MachineState.getReg_setReg_ne state .x6 reg _ (Ne.symm outside)

theorem nonce_record_pair_memory (state : MachineState) (index : Nat) :
    (nonceRecordPair state index).mem=
      (state.setMem (state.getReg .x25+signExtend12 (BitVec.ofNat 12 (8*index)))
        (state.getMem (state.getReg .x23+
          signExtend12 (BitVec.ofNat 12 (8*nonceRecordSourceWord index))))).mem := by
  rfl

theorem nonce_record_pairs_pc (state : MachineState) (count : Nat) :
    (nonceRecordPairs state count).pc=state.pc+BitVec.ofNat 64 (8*count) := by
  induction count with
  | zero => simp [nonceRecordPairs]
  | succ count ih =>
    rw [nonceRecordPairs, nonce_record_pair_pc, ih, BitVec.add_assoc]
    congr 1
    rw [show (8:Word)=BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
    congr 1

theorem nonce_record_pairs_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x6) :
    (nonceRecordPairs state count).getReg reg=state.getReg reg := by
  induction count with
  | zero => rfl
  | succ count ih => rw [nonceRecordPairs, nonce_record_pair_register _ _ _ outside, ih]

/-- Every load and store word of the block, read from the delivered image. -/
theorem nonce_record_load_word : ∀ index<67,
    (nonceCompactImage.code[116+2*index]?).bind decodeInstruction=
      some (.base (nonceRecordLoad index)) := by
  intro index inside
  interval_cases index <;> rfl

theorem nonce_record_store_word : ∀ index<67,
    (nonceCompactImage.code[117+2*index]?).bind decodeInstruction=
      some (.base (nonceRecordStore index)) := by
  intro index inside
  interval_cases index <;> rfl

theorem nonce_record_pair_execute (state : MachineState) (index : Nat) (inside : index<67)
    (pc : state.pc=BitVec.ofNat 64 (4560+8*index))
    (sourceValid : accessValid (state.getReg .x23+
      signExtend12 (BitVec.ofNat 12 (8*nonceRecordSourceWord index))) 8=true)
    (targetValid : accessValid (state.getReg .x25+signExtend12 (BitVec.ofNat 12 (8*index))) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (2+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceRecordPair state index) coins
          return result.charge 2 0) := by
  let loaded := execInstrBr state (nonceRecordLoad index)
  have first : fetch nonceCompactImage state=some (.base (nonceRecordLoad index)) := by
    apply cap_image_fetch _ state (116+2*index) _ (by omega)
    · rw [pc]
      congr 1
      omega
    · exact nonce_record_load_word index inside
  have second : fetch nonceCompactImage loaded=some (.base (nonceRecordStore index)) := by
    apply cap_image_fetch _ loaded (117+2*index) _ (by omega)
    · simp only [loaded, nonceRecordLoad, execInstrBr, MachineState.setPC, MachineState.setReg]
      rw [pc, show (4:Word)=BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      congr 1
      omega
    · exact nonce_record_store_word index inside
  have firstStep : ordinaryStep state (.base (nonceRecordLoad index))=some loaded := by
    simp only [ordinaryStep, nonceRecordLoad, memoryArgumentsValid, memAccess, sourceValid,
      if_true]
    rfl
  have kept : loaded.getReg .x25=state.getReg .x25 := by
    simp only [loaded, nonceRecordLoad, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne state .x6 .x25 _ (by decide)
  have secondStep : ordinaryStep loaded (.base (nonceRecordStore index))=
      some (nonceRecordPair state index) := by
    simp only [ordinaryStep, nonceRecordStore, memoryArgumentsValid, memAccess, kept, targetValid,
      if_true]
    rfl
  rw [show 2+fuel=(fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ _ (fuel+1) coins first firstStep,
    execute_ordinary_step _ _ _ _ fuel coins second secondStep]
  simp [instructionCycles, nonceRecordLoad, nonceRecordStore, Execution.charge, bind_assoc,
    ← Nat.add_assoc]

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

/-- Pointer and buffer premises for one record block. -/
structure NonceRecordWindow (source target : Nat) (state : MachineState) : Prop where
  ordered : target ≤ source
  source_window : source+544 ≤ MEMORY_BYTES
  source_aligned : source%8=0
  target_aligned : target%8=0
  source : state.getReg .x23=BitVec.ofNat 64 source
  target : state.getReg .x25=BitVec.ofNat 64 target

theorem nonce_record_address_valid (base index : Nat) (aligned : base%8=0)
    (window : base+8*index+8 ≤ MEMORY_BYTES) :
    accessValid (address base index) 8=true := by
  have small : base+8*index<2^64 := by
    norm_num [MEMORY_BYTES] at window
    omega
  simp only [address, accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨window, by omega⟩

theorem nonce_record_pairs_execute (source target : Nat) (state : MachineState)
    (pc : state.pc=4560) (window : NonceRecordWindow source target state)
    (count : Nat) (bounded : count ≤ 67) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (2*count+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceRecordPairs state count) coins
          return result.charge (2*count) 0) := by
  induction count generalizing fuel with
  | zero => simp [nonceRecordPairs, Execution.charge]
  | succ count ih =>
    let current := nonceRecordPairs state count
    have currentPc : current.pc=BitVec.ofNat 64 (4560+8*count) := by
      rw [nonce_record_pairs_pc, pc, show (4560:Word)=BitVec.ofNat 64 4560 from rfl,
        ← BitVec.ofNat_add]
    have sourceReg : current.getReg .x23=BitVec.ofNat 64 source :=
      (nonce_record_pairs_register state count .x23 (by decide)).trans window.source
    have targetReg : current.getReg .x25=BitVec.ofNat 64 target :=
      (nonce_record_pairs_register state count .x25 (by decide)).trans window.target
    have sourceWindow:=window.source_window
    have ordered:=window.ordered
    have sourceBound:=nonce_record_source_le count
    have sourceValid : accessValid (current.getReg .x23+
        signExtend12 (BitVec.ofNat 12 (8*nonceRecordSourceWord count))) 8=true := by
      rw [nonce_record_source_address current source count sourceReg (by omega)]
      exact nonce_record_address_valid source _ window.source_aligned (by omega)
    have targetValid : accessValid (current.getReg .x25+
        signExtend12 (BitVec.ofNat 12 (8*count))) 8=true := by
      rw [nonce_record_target_address current target count targetReg (by omega)]
      exact nonce_record_address_valid target _ window.target_aligned (by omega)
    rw [show 2*(count+1)+fuel=2*count+(2+fuel) by omega, ih (by omega) (2+fuel),
      nonce_record_pair_execute current count (by omega) currentPc sourceValid targetValid fuel coins]
    simp only [bind_assoc, pure_bind, charges]
    rfl

theorem nonce_record_tail_execute (state : MachineState) (pc : state.pc=5096)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (4+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceRecordTailState state) coins
          return result.charge 4 0) := by
  let first := execInstrBr state (.ADDI .x23 .x23 544)
  let second := execInstrBr first (.ADDI .x25 .x25 536)
  let third := execInstrBr second (.ADDI .x24 .x24 4095)
  have firstPc : first.pc=5100 := by
    simp only [first, execInstrBr, MachineState.setPC, pc]
    rfl
  have secondPc : second.pc=5104 := by
    simp only [second, execInstrBr, MachineState.setPC, firstPc]
    rfl
  have thirdPc : third.pc=5108 := by
    simp only [third, execInstrBr, MachineState.setPC, secondPc]
    rfl
  have fetch0 : fetch nonceCompactImage state=some (.base (.ADDI .x23 .x23 544)) := by
    apply cap_image_fetch _ state 250 _ (by decide) pc
    rfl
  have fetch1 : fetch nonceCompactImage first=some (.base (.ADDI .x25 .x25 536)) := by
    apply cap_image_fetch _ first 251 _ (by decide) firstPc
    rfl
  have fetch2 : fetch nonceCompactImage second=some (.base (.ADDI .x24 .x24 4095)) := by
    apply cap_image_fetch _ second 252 _ (by decide) secondPc
    rfl
  have fetch3 : fetch nonceCompactImage third=some (.base (.BNE .x24 .x0 7644)) := by
    apply cap_image_fetch _ third 253 _ (by decide) thirdPc
    rfl
  have step0 : ordinaryStep state (.base (.ADDI .x23 .x23 544))=some first := rfl
  have step1 : ordinaryStep first (.base (.ADDI .x25 .x25 536))=some second := rfl
  have step2 : ordinaryStep second (.base (.ADDI .x24 .x24 4095))=some third := rfl
  have step3 : ordinaryStep third (.base (.BNE .x24 .x0 7644))=some (nonceRecordTailState state) := rfl
  rw [show 4+fuel=(((fuel+1)+1)+1)+1 by omega,
    execute_ordinary_step _ _ _ _ (((fuel+1)+1)+1) coins fetch0 step0,
    execute_ordinary_step _ _ _ _ ((fuel+1)+1) coins fetch1 step1,
    execute_ordinary_step _ _ _ _ (fuel+1) coins fetch2 step2,
    execute_ordinary_step _ _ _ _ fuel coins fetch3 step3]
  simp [instructionCycles, Execution.charge, bind_assoc, ← Nat.add_assoc]

theorem nonce_compact_record_block_execute (source target : Nat) (state : MachineState)
    (pc : state.pc=4560) (window : NonceRecordWindow source target state)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (138+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactRecordState state) coins
          return result.charge 138 0) := by
  have pairsPc : (nonceRecordPairs state 67).pc=5096 := by
    rw [nonce_record_pairs_pc, pc]
    decide
  rw [show 138+fuel=2*67+(4+fuel) by omega,
    nonce_record_pairs_execute source target state pc window 67 (by decide) (4+fuel) coins,
    nonce_record_tail_execute _ pairsPc fuel coins]
  simp only [bind_assoc, pure_bind, charges]
  rfl

private theorem tail_branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x24 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem tail_branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x24 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_record_tail_adds (state : MachineState) :
    (nonceRecordTailAdds state).getReg .x23=state.getReg .x23+signExtend12 544 ∧
    (nonceRecordTailAdds state).getReg .x25=state.getReg .x25+signExtend12 536 ∧
    (nonceRecordTailAdds state).getReg .x24=state.getReg .x24+signExtend12 4095 ∧
    (nonceRecordTailAdds state).pc=state.pc+12 ∧
    (nonceRecordTailAdds state).mem=state.mem := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp [nonceRecordTailAdds, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, BitVec.add_assoc]

theorem nonce_record_tail_adds_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25) :
    (nonceRecordTailAdds state).getReg reg=state.getReg reg := by
  cases reg <;>
    simp_all [nonceRecordTailAdds, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]

theorem nonce_record_tail_state_register (state : MachineState) (reg : Reg) :
    (nonceRecordTailState state).getReg reg=(nonceRecordTailAdds state).getReg reg :=
  tail_branch_register _ _ reg

theorem nonce_record_tail_state_pc (state : MachineState) :
    (nonceRecordTailState state).pc=
      if (nonceRecordTailAdds state).getReg .x24=0 then (nonceRecordTailAdds state).pc+4
      else (nonceRecordTailAdds state).pc+signExtend13 7644 := by
  simp only [nonceRecordTailState, execInstrBr,
    show (nonceRecordTailAdds state).getReg .x0=0 from rfl, bne_iff_ne, ne_eq]
  by_cases zero : (nonceRecordTailAdds state).getReg .x24=0
  · rw [if_neg (not_not_intro zero), if_pos zero]
    rfl
  · rw [if_pos zero, if_neg zero]
    rfl

theorem nonce_record_tail_memory (state : MachineState) :
    (nonceRecordTailState state).mem=state.mem := by
  rw [nonceRecordTailState, tail_branch_memory]
  exact (nonce_record_tail_adds state).2.2.2.2

theorem nonce_compact_record_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceCompactRecordState state).getReg reg=state.getReg reg := by
  rw [nonceCompactRecordState, nonce_record_tail_state_register,
    nonce_record_tail_adds_register _ reg ⟨outside.2.2.1, outside.2.2.2.1, outside.2.2.2.2.1⟩,
    nonce_record_pairs_register _ _ reg outside.2.1]

end CommitGolfCandidate
