import CommitGolfCandidate.ChainedCheckerLower

/-! The cap wrapper derives its actual height by shifting the parent heap node. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setPC MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem zero_reg (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
private theorem mem_reg (s : MachineState) (reg : Reg) (value : Word) : (s.setReg reg value).mem=s.mem := by cases reg <;> rfl
private theorem mem_pc (s : MachineState) (pc : Word) : (s.setPC pc).mem=s.mem := rfl

def capDepth (height : Fin 8) : Nat := 7-height.val
def CapNodeRange (height : Fin 8) (node : Fin 256) : Prop :=
  2^(7-height.val)≤node.val ∧ node.val<2^(8-height.val)

theorem cap_shift_add (value : Word) (first second : Nat) :
    (value >>> first) >>> second=value >>> (first+second) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  simp only [BitVec.getLsbD_ushiftRight,Nat.add_assoc]

theorem cap_node_shift_zero (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (shift : Nat) (small : shift≤8) :
    BitVec.ofNat 64 node.val >>> shift=0 ↔ 8-height.val≤shift := by
  have value : (BitVec.ofNat 64 node.val >>> shift).toNat=node.val/2^shift := by
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node.val<2^64),Nat.shiftRight_eq_div_pow]
  have zero : BitVec.ofNat 64 node.val >>> shift=0 ↔ node.val/2^shift=0 := by
    constructor
    · intro same
      have numeric := congrArg BitVec.toNat same
      change (BitVec.ofNat 64 node.val >>> shift).toNat=0 at numeric
      rwa [value] at numeric
    · intro same
      apply BitVec.eq_of_toNat_eq
      rw [value,same]
      rfl
  rw [zero,Nat.div_eq_zero_iff_lt (by positivity)]
  unfold CapNodeRange at range
  constructor
  · intro less
    by_contra late
    have := height.isLt
    have bounded : shift≤7-height.val := by omega
    have power : 2^shift≤2^(7-height.val) := Nat.pow_le_pow_right (by decide) bounded
    exact (Nat.not_lt_of_ge (power.trans range.1)) less
  · intro late
    exact range.2.trans_le (Nat.pow_le_pow_right (by decide) late)

def capRoundOps : List Instr := [.SRLI .x30 .x30 1,.BEQ .x30 .x0 12,
  .ADDI .x17 .x17 4095,.JAL .x0 2097140]
@[irreducible] def capRoundPrefix (s : MachineState) (n : Nat) : MachineState :=
  (capRoundOps.take n).foldl execInstrBr s

theorem cap_round_zero (s : MachineState) : capRoundPrefix s 0=s := by rw [capRoundPrefix]; rfl
theorem cap_round_succ (s : MachineState) (n : Nat) (small : n<4) :
    capRoundPrefix s (n+1)=execInstrBr (capRoundPrefix s n) (capRoundOps.getD n .EBREAK) := by
  interval_cases n <;> rw [capRoundPrefix,capRoundPrefix] <;> rfl
theorem cap_round_at : OpsAt chainedCheckerImage (4096+4*2903) capRoundOps :=
  chained_checker_slice_at 2903 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem cap_round_one (s : MachineState) : capRoundPrefix s 1=execInstrBr s (.SRLI .x30 .x30 1) := by
  rw [capRoundPrefix] <;> rfl
theorem cap_round_second (s : MachineState) : capRoundPrefix s 2=execInstrBr (capRoundPrefix s 1) (.BEQ .x30 .x0 12) := by
  rw [capRoundPrefix,capRoundPrefix] <;> rfl
theorem cap_round_third (s : MachineState) : capRoundPrefix s 3=execInstrBr (capRoundPrefix s 2) (.ADDI .x17 .x17 4095) := by
  rw [capRoundPrefix,capRoundPrefix] <;> rfl
theorem cap_round_last (s : MachineState) : capRoundPrefix s 4=execInstrBr (capRoundPrefix s 3) (.JAL .x0 2097140) := by
  rw [capRoundPrefix,capRoundPrefix] <;> rfl

theorem cap_round_prefix_pc (s : MachineState) (pc : s.pc=4096+4*2903)
    (nonzero : s.getReg .x30 >>> 1≠0) (n : Nat) (small : n<4) :
    (capRoundPrefix s n).pc=4096+BitVec.ofNat 64 (4*(2903+n)) := by
  have nonzero' : s.getReg .x30 >>> 1≠0#64 := nonzero
  interval_cases n <;> simp [capRoundPrefix,capRoundOps,execInstrBr,pc,nonzero',signExtend12,signExtend13]

theorem cap_round_pc (s : MachineState) (pc : s.pc=4096+4*2903) (nonzero : s.getReg .x30 >>> 1≠0) :
    (capRoundPrefix s 4).pc=4096+4*2903 := by
  rw [cap_round_succ s 3 (by decide)]
  change (capRoundPrefix s 3).pc+signExtend21 2097140=_
  rw [cap_round_prefix_pc s pc nonzero 3 (by decide)]
  decide +kernel

private theorem beq_register (s : MachineState) (a b : Reg) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr s (.BEQ a b offset)).getReg reg=s.getReg reg := by
  change MachineState.getReg (if s.getReg a==s.getReg b then s.setPC (s.pc+signExtend13 offset) else s.setPC (s.pc+4)) reg=_
  split <;> rfl
private theorem jal_register (s : MachineState) (offset : BitVec 21) (reg : Reg) :
    (execInstrBr s (.JAL .x0 offset)).getReg reg=s.getReg reg := by cases reg <;> rfl
private theorem addi_register (s : MachineState) (rd rs : Reg) (offset : BitVec 12) (reg : Reg) (away : reg≠rd) :
    (execInstrBr s (.ADDI rd rs offset)).getReg reg=s.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm away)]
private theorem srli_register (s : MachineState) (rd rs : Reg) (offset : BitVec 6) (reg : Reg) (away : reg≠rd) :
    (execInstrBr s (.SRLI rd rs offset)).getReg reg=s.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm away)]

theorem cap_round_register (s : MachineState) (reg : Reg) (height : reg≠.x17) (counter : reg≠.x30) :
    (capRoundPrefix s 4).getReg reg=s.getReg reg := by
  rw [cap_round_last,jal_register,cap_round_third,addi_register _ .x17 .x17 4095 reg height,
    cap_round_second,beq_register,cap_round_one,srli_register _ .x30 .x30 1 reg counter]

theorem cap_round_height (s : MachineState) :
    (capRoundPrefix s 4).getReg .x17=s.getReg .x17+signExtend12 4095 := by
  rw [cap_round_last,jal_register,cap_round_third]
  change (capRoundPrefix s 2).getReg .x17+signExtend12 4095=_
  rw [cap_round_second,beq_register,cap_round_one,srli_register _ .x30 .x30 1 .x17 (by decide)]

theorem cap_round_counter (s : MachineState) :
    (capRoundPrefix s 4).getReg .x30=s.getReg .x30 >>> 1 := by
  rw [cap_round_last,jal_register,cap_round_third,addi_register _ .x17 .x17 4095 .x30 (by decide),
    cap_round_second,beq_register,cap_round_one]
  rfl

theorem cap_round_execution (s : MachineState) (pc : s.pc=4096+4*2903)
    (nonzero : s.getReg .x30 >>> 1≠0) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capRoundPrefix s 4) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←cap_round_zero s]
  apply execute_unit_steps (states := capRoundPrefix s)
  intro i inside
  refine ⟨.base (capRoundOps.getD i .EBREAK),?_,?_,?_⟩
  · apply cap_round_at i inside
    rw [cap_round_prefix_pc s pc nonzero i inside]
    simp only [show 4*(2903+i)=4*2903+4*i by omega,BitVec.ofNat_add,BitVec.add_assoc,
      show BitVec.ofNat 64 (4*2903)=(4 : Word)*2903 from by decide +kernel]
  · rw [cap_round_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def capRounds (s : MachineState) (n : Nat) : MachineState :=
  Nat.rec s (fun _ before => capRoundPrefix before 4) n
theorem cap_rounds_zero (s : MachineState) : capRounds s 0=s := by rw [capRounds]; rfl
theorem cap_rounds_succ (s : MachineState) (n : Nat) : capRounds s (n+1)=capRoundPrefix (capRounds s n) 4 := by
  rw [capRounds,capRounds]

theorem cap_rounds_ready (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2903) (initialHeight : s.getReg .x17=23)
    (initialCounter : s.getReg .x30=BitVec.ofNat 64 node.val) (n : Nat) (small : n≤capDepth height) :
    (capRounds s n).pc=4096+4*2903 ∧ (capRounds s n).getReg .x17=BitVec.ofNat 64 (23-n) ∧
      (capRounds s n).getReg .x30=BitVec.ofNat 64 node.val >>> n := by
  induction n with
  | zero => simp only [cap_rounds_zero,Nat.sub_zero,BitVec.ushiftRight_zero]; exact ⟨pc,initialHeight,initialCounter⟩
  | succ n ih =>
    have previous := ih (by omega)
    have depth : n<7-height.val := by unfold capDepth at small; omega
    have nonzero : (capRounds s n).getReg .x30 >>> 1≠0 := by
      rw [previous.2.2,cap_shift_add]
      intro zero
      have impossible := (cap_node_shift_zero height node range (n+1) (by omega)).mp zero
      omega
    rw [cap_rounds_succ]
    refine ⟨cap_round_pc _ previous.1 nonzero,?_,?_⟩
    · rw [cap_round_height,previous.2.1]
      have bound : n≤6 := by omega
      interval_cases n <;> decide +kernel
    · rw [cap_round_counter,previous.2.2,cap_shift_add]

theorem cap_rounds_register (s : MachineState) (n : Nat) (reg : Reg) (height : reg≠.x17) (counter : reg≠.x30) :
    (capRounds s n).getReg reg=s.getReg reg := by
  induction n with
  | zero => rw [cap_rounds_zero]
  | succ n ih => rw [cap_rounds_succ,cap_round_register _ reg height counter,ih]

theorem cap_rounds_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2903) (initialHeight : s.getReg .x17=23)
    (initialCounter : s.getReg .x30=BitVec.ofNat 64 node.val) (n : Nat) (small : n≤capDepth height)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4*n+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capRounds s n) coins
          return result.charge (4*n) 0) := by
  induction n generalizing fuel with
  | zero => simp [cap_rounds_zero,Execution.charge]
  | succ n ih =>
    have previous := cap_rounds_ready height node range s pc initialHeight initialCounter n (by omega)
    have depth : n<7-height.val := by unfold capDepth at small; omega
    have nonzero : (capRounds s n).getReg .x30 >>> 1≠0 := by
      rw [previous.2.2,cap_shift_add]
      intro zero
      have impossible := (cap_node_shift_zero height node range (n+1) (by omega)).mp zero
      omega
    rw [show 4*(n+1)+fuel=4*n+(4+fuel) by omega,ih (by omega),cap_round_execution _ previous.1 nonzero,cap_rounds_succ]
    simp [Execution.charge,Nat.mul_add,Nat.add_assoc]

def capInitOps : List Instr := [.ADDI .x17 .x0 23,.ADDI .x30 .x6 0]
@[irreducible] def capInitPrefix (s : MachineState) (n : Nat) : MachineState :=
  (capInitOps.take n).foldl execInstrBr s
theorem cap_init_at : OpsAt chainedCheckerImage (4096+4*2901) capInitOps :=
  chained_checker_slice_at 2901 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem cap_init_pc (s : MachineState) (pc : s.pc=4096+4*2901) (n : Nat) (small : n≤2) :
    (capInitPrefix s n).pc=4096+BitVec.ofNat 64 (4*(2901+n)) := by
  interval_cases n <;> simp [capInitPrefix,capInitOps,execInstrBr,pc,signExtend12]
theorem cap_init_height (s : MachineState) : (capInitPrefix s 2).getReg .x17=23 := by
  rw [capInitPrefix]; rfl
theorem cap_init_counter (s : MachineState) : (capInitPrefix s 2).getReg .x30=s.getReg .x6 := by
  simp [capInitPrefix,capInitOps,execInstrBr,signExtend12]
theorem cap_init_register (s : MachineState) (reg : Reg) (height : reg≠.x17) (counter : reg≠.x30) :
    (capInitPrefix s 2).getReg reg=s.getReg reg := by
  simp [capInitPrefix,capInitOps,execInstrBr,Ne.symm height,Ne.symm counter]

theorem cap_init_execution (s : MachineState) (pc : s.pc=4096+4*2901) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capInitPrefix s 2) coins
          return result.charge 2 0) := by
  rw [checking_manifest_image]
  have zero : capInitPrefix s 0=s := by rw [capInitPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := capInitPrefix s)
  intro i inside
  refine ⟨.base (capInitOps.getD i .EBREAK),?_,?_,?_⟩
  · apply cap_init_at i inside
    interval_cases i <;> simp [capInitPrefix,capInitOps,execInstrBr,pc,signExtend12]
  · interval_cases i <;> rw [capInitPrefix,capInitPrefix] <;> rfl
  · interval_cases i <;> rfl

def capFinalOps : List Instr := [.SRLI .x30 .x30 1,.BEQ .x30 .x0 12,
  .ADDI .x18 .x0 0,.ADDI .x16 .x0 4095,.SRLI .x16 .x16 18]
@[irreducible] def capFinalPrefix (s : MachineState) (n : Nat) : MachineState :=
  (capFinalOps.take n).foldl execInstrBr s
theorem cap_final_one (s : MachineState) : capFinalPrefix s 1=execInstrBr s (.SRLI .x30 .x30 1) := by
  rw [capFinalPrefix] <;> rfl
theorem cap_final_second (s : MachineState) : capFinalPrefix s 2=execInstrBr (capFinalPrefix s 1) (.BEQ .x30 .x0 12) := by
  rw [capFinalPrefix,capFinalPrefix] <;> rfl
theorem cap_final_third (s : MachineState) : capFinalPrefix s 3=execInstrBr (capFinalPrefix s 2) (.ADDI .x18 .x0 0) := by
  rw [capFinalPrefix,capFinalPrefix] <;> rfl
theorem cap_final_fourth (s : MachineState) : capFinalPrefix s 4=execInstrBr (capFinalPrefix s 3) (.ADDI .x16 .x0 4095) := by
  rw [capFinalPrefix,capFinalPrefix] <;> rfl
theorem cap_final_last (s : MachineState) : capFinalPrefix s 5=execInstrBr (capFinalPrefix s 4) (.SRLI .x16 .x16 18) := by
  rw [capFinalPrefix,capFinalPrefix] <;> rfl

def capFinalIndex (n : Fin 6) : Nat := ([2903,2904,2907,2908,2909,2910] : List Nat).getD n.val 0
theorem cap_final_pc (s : MachineState) (pc : s.pc=4096+4*2903) (zero : s.getReg .x30 >>> 1=0)
    (n : Fin 6) : (capFinalPrefix s n.val).pc=4096+BitVec.ofNat 64 (4*capFinalIndex n) := by
  have zero' : s.getReg .x30 >>> 1=0#64 := zero
  fin_cases n <;> simp [capFinalPrefix,capFinalOps,capFinalIndex,execInstrBr,pc,zero',signExtend12,signExtend13]

theorem cap_final_register (s : MachineState) (reg : Reg) (counter : reg≠.x30) (calls : reg≠.x18) (mask : reg≠.x16) :
    (capFinalPrefix s 5).getReg reg=s.getReg reg := by
  rw [cap_final_last,srli_register _ .x16 .x16 18 reg mask,cap_final_fourth,
    addi_register _ .x16 .x0 4095 reg mask,cap_final_third,addi_register _ .x18 .x0 0 reg calls,
    cap_final_second,beq_register,cap_final_one,srli_register _ .x30 .x30 1 reg counter]
theorem cap_final_calls (s : MachineState) : (capFinalPrefix s 5).getReg .x18=0 := by
  rw [cap_final_last,srli_register _ .x16 .x16 18 .x18 (by decide),cap_final_fourth,
    addi_register _ .x16 .x0 4095 .x18 (by decide),cap_final_third]
  rfl
private theorem mask_load (s : MachineState) :
    (execInstrBr s (.ADDI .x16 .x0 4095)).getReg .x16=signExtend12 4095 := by
  simp only [execInstrBr,MachineState.getReg_setPC,zero_reg,BitVec.zero_add]
  exact MachineState.getReg_setReg_eq (by decide)
private theorem mask_shift (s : MachineState) :
    (execInstrBr s (.SRLI .x16 .x16 18)).getReg .x16=s.getReg .x16 >>> 18 := rfl
theorem cap_final_mask (s : MachineState) : (capFinalPrefix s 5).getReg .x16=signExtend12 4095 >>> 18 := by
  rw [cap_final_last,mask_shift,cap_final_fourth,mask_load]

theorem cap_final_bounded (i : Fin 5) : capFinalIndex ⟨i.val,by omega⟩<3012 := by
  revert i
  decide +kernel
theorem cap_final_opcode (i : Fin 5) :
    chainedCheckerOps.getD (capFinalIndex ⟨i.val,by omega⟩) .EBREAK=capFinalOps.getD i.val .EBREAK := by
  revert i
  decide +kernel

theorem cap_final_execution (s : MachineState) (pc : s.pc=4096+4*2903) (zero : s.getReg .x30 >>> 1=0)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capFinalPrefix s 5) coins
          return result.charge 5 0) := by
  have zeroState : capFinalPrefix s 0=s := by rw [capFinalPrefix]; rfl
  conv_lhs => rw [←zeroState]
  apply execute_unit_steps (states := capFinalPrefix s)
  intro i inside
  refine ⟨.base (capFinalOps.getD i .EBREAK),?_,?_,?_⟩
  · apply RecordLeaf.trunc_fetch _ (capFinalIndex ⟨i,by omega⟩) _
    · exact cap_final_bounded ⟨i,inside⟩
    · rw [cap_final_pc s pc zero ⟨i,by omega⟩]
      rw [BitVec.ofNat_add]
      rfl
    · exact cap_final_opcode ⟨i,inside⟩
  · interval_cases i <;> rw [capFinalPrefix,capFinalPrefix] <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def capScheduled (height : Fin 8) (s : MachineState) : MachineState :=
  capFinalPrefix (capRounds (capInitPrefix s 2) (capDepth height)) 5

theorem cap_schedule_rounds_ready (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2901) (parent : s.getReg .x6=BitVec.ofNat 64 node.val) :
    (capRounds (capInitPrefix s 2) (capDepth height)).pc=4096+4*2903 ∧
      (capRounds (capInitPrefix s 2) (capDepth height)).getReg .x17=BitVec.ofNat 64 (16+height.val) ∧
      (capRounds (capInitPrefix s 2) (capDepth height)).getReg .x30 >>> 1=0 := by
  have ready := cap_rounds_ready height node range (capInitPrefix s 2) (cap_init_pc s pc 2 (by decide))
    (cap_init_height s) ((cap_init_counter s).trans parent) (capDepth height) (by rfl)
  refine ⟨ready.1,?_,?_⟩
  · rw [ready.2.1]
    congr 1
    unfold capDepth
    omega
  · rw [ready.2.2,cap_shift_add]
    exact (cap_node_shift_zero height node range (capDepth height+1) (by unfold capDepth; omega)).mpr (by unfold capDepth; omega)

theorem cap_scheduled_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2901) (parent : s.getReg .x6=BitVec.ofNat 64 node.val) :
    (capScheduled height s).pc=4096+4*2910 := by
  have ready := cap_schedule_rounds_ready height node range s pc parent
  rw [capScheduled]
  exact cap_final_pc _ ready.1 ready.2.2 ⟨5,by decide⟩
theorem cap_scheduled_height (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2901) (parent : s.getReg .x6=BitVec.ofNat 64 node.val) :
    (capScheduled height s).getReg .x17=BitVec.ofNat 64 (16+height.val) := by
  rw [capScheduled,cap_final_register _ .x17 (by decide) (by decide) (by decide)]
  exact (cap_schedule_rounds_ready height node range s pc parent).2.1
theorem cap_scheduled_calls (height : Fin 8) (s : MachineState) : (capScheduled height s).getReg .x18=0 := by
  rw [capScheduled,cap_final_calls]
theorem cap_scheduled_mask (height : Fin 8) (s : MachineState) : (capScheduled height s).getReg .x16=signExtend12 4095 >>> 18 := by
  rw [capScheduled,cap_final_mask]
theorem cap_scheduled_register (height : Fin 8) (s : MachineState) (reg : Reg)
    (h : reg≠.x17) (counter : reg≠.x30) (calls : reg≠.x18) (mask : reg≠.x16) :
    (capScheduled height s).getReg reg=s.getReg reg := by
  rw [capScheduled,cap_final_register _ reg counter calls mask,cap_rounds_register _ _ reg h counter,
    cap_init_register _ reg h counter]

theorem cap_schedule_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2901) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (7+4*capDepth height+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capScheduled height s) coins
          return result.charge (7+4*capDepth height) 0) := by
  have ready := cap_schedule_rounds_ready height node range s pc parent
  rw [show 7+4*capDepth height+fuel=2+(4*capDepth height+(5+fuel)) by omega,
    cap_init_execution s pc,cap_rounds_execution height node range (capInitPrefix s 2)
      (cap_init_pc s pc 2 (by decide)) (cap_init_height s) ((cap_init_counter s).trans parent)
      (capDepth height) (by rfl),cap_final_execution _ ready.1 ready.2.2,capScheduled]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [show 2+(5+4*capDepth height)=7+4*capDepth height by omega]

private theorem beq_memory (s : MachineState) (a b : Reg) (offset : BitVec 13) :
    (execInstrBr s (.BEQ a b offset)).mem=s.mem := by
  change (if s.getReg a==s.getReg b then s.setPC (s.pc+signExtend13 offset) else s.setPC (s.pc+4)).mem=_
  split <;> rfl
private theorem jal_memory (s : MachineState) (offset : BitVec 21) :
    (execInstrBr s (.JAL .x0 offset)).mem=s.mem := by
  simp only [execInstrBr,mem_reg,mem_pc]
private theorem addi_memory (s : MachineState) (rd rs : Reg) (offset : BitVec 12) :
    (execInstrBr s (.ADDI rd rs offset)).mem=s.mem := by
  simp only [execInstrBr,mem_reg,mem_pc]
private theorem srli_memory (s : MachineState) (rd rs : Reg) (offset : BitVec 6) :
    (execInstrBr s (.SRLI rd rs offset)).mem=s.mem := by
  simp only [execInstrBr,mem_reg,mem_pc]

theorem cap_round_memory (s : MachineState) : (capRoundPrefix s 4).mem=s.mem := by
  rw [cap_round_last,jal_memory,cap_round_third,addi_memory,cap_round_second,beq_memory,cap_round_one,srli_memory]
theorem cap_rounds_memory (s : MachineState) (n : Nat) : (capRounds s n).mem=s.mem := by
  induction n with
  | zero => rw [cap_rounds_zero]
  | succ n ih => rw [cap_rounds_succ,cap_round_memory,ih]
theorem cap_init_memory (s : MachineState) : (capInitPrefix s 2).mem=s.mem := by
  simp only [capInitPrefix,capInitOps,List.take,List.foldl,execInstrBr,mem_reg,mem_pc]
theorem cap_final_memory (s : MachineState) : (capFinalPrefix s 5).mem=s.mem := by
  rw [cap_final_last,srli_memory,cap_final_fourth,addi_memory,cap_final_third,addi_memory,
    cap_final_second,beq_memory,cap_final_one,srli_memory]
theorem cap_scheduled_memory (height : Fin 8) (s : MachineState) : (capScheduled height s).mem=s.mem := by
  rw [capScheduled,cap_final_memory,cap_rounds_memory,cap_init_memory]

def capHeight (height : Fin 8) : Height := ⟨16+height.val,by omega⟩
theorem cap_canonical_mask (height : Fin 8) : signExtend12 4095 >>> 18=finalMask (capHeight height) := by
  revert height
  decide +kernel

end CommitGolfCandidate.Chained.Native.CheckerCap
