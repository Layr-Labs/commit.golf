import CommitGolfCandidate.ChainedCheckerFooterSubtree
import CommitGolfCandidate.ChainedTailParseExecution

/-! Installed footer low-body endpoint setup and guarded parser initialization. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerFooterSetupOps : List Instr :=
  [.ADDI .x2 .x22 0,.SLLI .x20 .x22 5,.SLLI .x3 .x22 1,
   .SUB .x20 .x20 .x3,.SUB .x20 .x20 .x22,.ADD .x20 .x20 .x18,.ADD .x19 .x15 .x17]
def checkerFooterBufferOps : List Instr := [.ADDI .x21 .x8 0,.ADDI .x23 .x0 0,.ADDI .x25 .x0 0]

@[irreducible] def checkerFooterSetupPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i previous => execInstrBr previous (checkerFooterSetupOps.getD i .EBREAK)) n
@[irreducible] def checkerFooterBufferPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i previous => execInstrBr previous (checkerFooterBufferOps.getD i .EBREAK)) n
@[irreducible] def checkerFooterSetupGuard (s : MachineState) : MachineState := execInstrBr s (.BGEU .x19 .x20 8)
@[irreducible] def checkerFooterParseSetupState (s : MachineState) : MachineState :=
  checkerFooterBufferPrefix 3 (checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s))

theorem checker_footer_setup_zero (s : MachineState) : checkerFooterSetupPrefix 0 s=s := by
  unfold checkerFooterSetupPrefix
  rfl
theorem checker_footer_setup_succ (n : Nat) (s : MachineState) : checkerFooterSetupPrefix (n+1) s=
    execInstrBr (checkerFooterSetupPrefix n s) (checkerFooterSetupOps.getD n .EBREAK) := by
  unfold checkerFooterSetupPrefix
  rfl
theorem checker_footer_buffer_zero (s : MachineState) : checkerFooterBufferPrefix 0 s=s := by
  unfold checkerFooterBufferPrefix
  rfl
theorem checker_footer_buffer_succ (n : Nat) (s : MachineState) : checkerFooterBufferPrefix (n+1) s=
    execInstrBr (checkerFooterBufferPrefix n s) (checkerFooterBufferOps.getD n .EBREAK) := by
  unfold checkerFooterBufferPrefix
  rfl
theorem checker_footer_parse_setup_eq (s : MachineState) : checkerFooterParseSetupState s=
    checkerFooterBufferPrefix 3 (checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s)) := by
  rw [checkerFooterParseSetupState]

theorem checker_footer_setup_at : OpsAt chainedCheckerImage (4096+4*2190) checkerFooterSetupOps :=
  chained_checker_slice_at 2190 7 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_buffer_at : OpsAt chainedCheckerImage (4096+4*2199) checkerFooterBufferOps :=
  chained_checker_slice_at 2199 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

private theorem prefix_step_pc (s : MachineState) (i : Fin 7) :
    (execInstrBr s (checkerFooterSetupOps.getD i.val .EBREAK)).pc=s.pc+4 := by fin_cases i <;> rfl
private theorem buffer_step_pc (s : MachineState) (i : Fin 3) :
    (execInstrBr s (checkerFooterBufferOps.getD i.val .EBREAK)).pc=s.pc+4 := by fin_cases i <;> rfl

theorem checker_footer_setup_pc (s : MachineState) (n : Nat) (small : n≤7) :
    (checkerFooterSetupPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_footer_setup_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_footer_setup_succ,prefix_step_pc _ ⟨n,by omega⟩,ih (by omega)]
    change (s.pc+BitVec.ofNat 64 (4*n))+BitVec.ofNat 64 4=_
    rw [byte_offset_add]
    exact congrArg (fun offset => s.pc+BitVec.ofNat 64 offset) (by omega)
theorem checker_footer_buffer_pc (s : MachineState) (n : Nat) (small : n≤3) :
    (checkerFooterBufferPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_footer_buffer_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_footer_buffer_succ,buffer_step_pc _ ⟨n,by omega⟩,ih (by omega)]
    change (s.pc+BitVec.ofNat 64 (4*n))+BitVec.ofNat 64 4=_
    rw [byte_offset_add]
    exact congrArg (fun offset => s.pc+BitVec.ofNat 64 offset) (by omega)

theorem checker_footer_setup_memory (s : MachineState) (n : Nat) (small : n≤7) (query : Word) :
    (checkerFooterSetupPrefix n s).getMem query=s.getMem query := by
  have step (state : MachineState) (i : Fin 7) :
      (execInstrBr state (checkerFooterSetupOps.getD i.val .EBREAK)).getMem query=state.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_footer_setup_zero]
  | succ n ih => rw [checker_footer_setup_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_footer_buffer_memory (s : MachineState) (n : Nat) (small : n≤3) (query : Word) :
    (checkerFooterBufferPrefix n s).getMem query=s.getMem query := by
  have step (state : MachineState) (i : Fin 3) :
      (execInstrBr state (checkerFooterBufferOps.getD i.val .EBREAK)).getMem query=state.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_footer_buffer_zero]
  | succ n ih => rw [checker_footer_buffer_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_footer_setup_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3,.x19,.x20]) :
    (checkerFooterSetupPrefix 7 s).getReg reg=s.getReg reg := by
  simp only [checker_footer_setup_succ,checker_footer_setup_zero]
  cases reg <;> simp at kept
  all_goals rfl
theorem checker_footer_buffer_register (s : MachineState) (reg : Reg) (kept : reg∉[.x21,.x23,.x25]) :
    (checkerFooterBufferPrefix 3 s).getReg reg=s.getReg reg := by
  simp only [checker_footer_buffer_succ,checker_footer_buffer_zero]
  cases reg <;> simp at kept
  all_goals rfl

theorem checker_footer_setup_saved_count (s : MachineState) :
    (checkerFooterSetupPrefix 7 s).getReg .x2=s.getReg .x22 := by
  simp only [checker_footer_setup_succ,checker_footer_setup_zero]
  exact BitVec.add_zero _
theorem checker_footer_setup_end (s : MachineState) :
    (checkerFooterSetupPrefix 7 s).getReg .x19=s.getReg .x15+s.getReg .x17 := by
  simp only [checker_footer_setup_succ,checker_footer_setup_zero]
  rfl
theorem checker_footer_setup_source (s : MachineState) (source count : Nat) (bounded : count≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 count) :
    (checkerFooterSetupPrefix 7 s).getReg .x20=BitVec.ofNat 64 (source+29*count) := by
  simp only [checker_footer_setup_succ,checker_footer_setup_zero]
  change (((s.getReg .x22<<<5)-(s.getReg .x22<<<1))-s.getReg .x22)+s.getReg .x18=_
  rw [pointer,rows,BitVec.shiftLeft_eq_mul_twoPow,BitVec.shiftLeft_eq_mul_twoPow]
  change ((BitVec.ofNat 64 count*BitVec.ofNat 64 32-BitVec.ofNat 64 count*BitVec.ofNat 64 2)-BitVec.ofNat 64 count)+_=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_mul,
    BitVec.ofNat_sub_ofNat_of_le (count*32) (count*2) (by omega) (by omega),
    show count*32-count*2=30*count by omega,
    BitVec.ofNat_sub_ofNat_of_le (30*count) count (by omega) (by omega),
    show 30*count-count=29*count by omega,←BitVec.ofNat_add,Nat.add_comm]

theorem checker_footer_guard_register (s : MachineState) (reg : Reg) :
    (checkerFooterSetupGuard s).getReg reg=s.getReg reg := by
  by_cases enough : ¬BitVec.ult (s.getReg .x19) (s.getReg .x20)=true
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+8) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_left enough
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+4) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_right enough
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
theorem checker_footer_guard_memory (s : MachineState) (query : Word) :
    (checkerFooterSetupGuard s).getMem query=s.getMem query := by
  by_cases enough : ¬BitVec.ult (s.getReg .x19) (s.getReg .x20)=true
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+8) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_left enough
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+4) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_right enough
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
theorem checker_footer_guard_pc (s : MachineState) :
    (checkerFooterSetupGuard s).pc=if BitVec.ult (s.getReg .x19) (s.getReg .x20) then s.pc+4 else s.pc+8 := by
  by_cases enough : ¬BitVec.ult (s.getReg .x19) (s.getReg .x20)=true
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+8) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_left enough
    exact (congrArg MachineState.pc same).trans (by change s.pc+8=_; simp [enough])
  · have same : checkerFooterSetupGuard s=s.setPC (s.pc+4) := by
      rw [checkerFooterSetupGuard]; exact ite_eq_right enough
    exact (congrArg MachineState.pc same).trans (by change s.pc+4=_; simp at enough; simp [enough])

theorem checker_footer_setup_execution (s : MachineState) (pc : s.pc=4096+4*2190) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (7+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterSetupPrefix 7 s) coins
          return result.charge 7 0) := by
  conv_lhs => rw [←checker_footer_setup_zero s]
  apply execute_unit_steps (states := fun n => checkerFooterSetupPrefix n s)
  intro i inside
  refine ⟨.base (checkerFooterSetupOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_setup_at i inside
    rw [checker_footer_setup_pc s i (by omega),pc]
  · rw [checker_footer_setup_succ]; interval_cases i <;> rfl
  · interval_cases i <;> rfl
theorem checker_footer_buffer_execution (s : MachineState) (pc : s.pc=4096+4*2199) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (3+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterBufferPrefix 3 s) coins
          return result.charge 3 0) := by
  conv_lhs => rw [←checker_footer_buffer_zero s]
  apply execute_unit_steps (states := fun n => checkerFooterBufferPrefix n s)
  intro i inside
  refine ⟨.base (checkerFooterBufferOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_buffer_at i inside
    rw [checker_footer_buffer_pc s i (by omega),pc]
  · rw [checker_footer_buffer_succ]; interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_footer_guard_execution (s : MachineState) (pc : s.pc=4096+4*2197) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterSetupGuard s) coins
          return result.charge 1 0) := by
  have code : OpsAt chainedCheckerImage (4096+4*2197) [.BGEU .x19 .x20 8] :=
    chained_checker_slice_at 2197 1 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  have ordinary : ordinaryStep s (.base (.BGEU .x19 .x20 8))=some (checkerFooterSetupGuard s) := by
    rw [checkerFooterSetupGuard]; rfl
  have fetched : fetch chainedCheckerImage s=some (.base (.BGEU .x19 .x20 8)) := code 0 (by decide) s pc
  simpa only [Nat.add_comm,instructionCycles] using
    execute_ordinary_step chainedCheckerImage _ s _ fuel coins fetched ordinary

def CheckerFooterLowBodyFits (s : MachineState) : Prop :=
  BitVec.ult ((checkerFooterSetupPrefix 7 s).getReg .x19) ((checkerFooterSetupPrefix 7 s).getReg .x20)=false

theorem checker_footer_low_body_fits_iff (s : MachineState) (source count endpoint : Nat)
    (bounded : count≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 count) (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 endpoint)
    (sourceFit : source+29*count<2^64) (endFit : endpoint<2^64) :
    CheckerFooterLowBodyFits s ↔ source+29*count≤endpoint := by
  rw [CheckerFooterLowBodyFits,checker_footer_setup_end,checker_footer_setup_source s source count bounded pointer rows,
    endPointer,BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat,decide_eq_false_iff_not,Nat.not_lt]
  rw [Nat.mod_eq_of_lt sourceFit,Nat.mod_eq_of_lt endFit]

theorem checker_footer_parse_setup_memory (s : MachineState) (query : Word) :
    (checkerFooterParseSetupState s).getMem query=s.getMem query := by
  rw [checker_footer_parse_setup_eq,checker_footer_buffer_memory _ 3 (by decide),checker_footer_guard_memory,
    checker_footer_setup_memory _ 7 (by decide)]
theorem checker_footer_parse_setup_byte (s : MachineState) (query : Word) :
    (checkerFooterParseSetupState s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_parse_setup_memory]
theorem checker_footer_parse_setup_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x19,.x20,.x21,.x23,.x25]) :
    (checkerFooterParseSetupState s).getReg reg=s.getReg reg := by
  rw [checker_footer_parse_setup_eq]
  cases reg <;> simp at kept
  all_goals rw [checker_footer_buffer_register _ _ (by decide),checker_footer_guard_register,
    checker_footer_setup_register _ _ (by decide)]
theorem checker_footer_parse_setup_count (s : MachineState) :
    (checkerFooterParseSetupState s).getReg .x22=s.getReg .x22 :=
  checker_footer_parse_setup_register s .x22 (by decide)
theorem checker_footer_parse_setup_saved_count (s : MachineState) :
    (checkerFooterParseSetupState s).getReg .x2=s.getReg .x22 := by
  rw [checker_footer_parse_setup_eq,checker_footer_buffer_register _ .x2 (by decide),
    checker_footer_guard_register,checker_footer_setup_saved_count]
theorem checker_footer_parse_setup_source (s : MachineState) (source count : Nat) (bounded : count≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 count) :
    (checkerFooterParseSetupState s).getReg .x20=BitVec.ofNat 64 (source+29*count) := by
  rw [checker_footer_parse_setup_eq,checker_footer_buffer_register _ .x20 (by decide),
    checker_footer_guard_register,checker_footer_setup_source s source count bounded pointer rows]
theorem checker_footer_parse_setup_end (s : MachineState) :
    (checkerFooterParseSetupState s).getReg .x19=s.getReg .x15+s.getReg .x17 := by
  rw [checker_footer_parse_setup_eq,checker_footer_buffer_register _ .x19 (by decide),
    checker_footer_guard_register,checker_footer_setup_end]
theorem checker_footer_parse_setup_metadata (s : MachineState) :
    (checkerFooterParseSetupState s).getReg .x21=s.getReg .x8 := by
  rw [checker_footer_parse_setup_eq]
  simp only [checker_footer_buffer_succ,checker_footer_buffer_zero]
  change (checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s)).getReg .x8+0#64=_
  rw [BitVec.add_zero,checker_footer_guard_register,checker_footer_setup_register _ .x8 (by decide)]
theorem checker_footer_parse_setup_buffer (s : MachineState) : TailParseBuffer (checkerFooterParseSetupState s) [] := by
  rw [checker_footer_parse_setup_eq]
  constructor
  · simp only [checker_footer_buffer_succ,checker_footer_buffer_zero]; rfl
  · simp only [checker_footer_buffer_succ,checker_footer_buffer_zero]; rfl
  · decide
theorem checker_footer_parse_setup_widths (s : MachineState) (widths : List Nat)
    (table : ParseWidthsAt s (s.getReg .x8) widths) :
    ParseWidthsAt (checkerFooterParseSetupState s) ((checkerFooterParseSetupState s).getReg .x21) widths := by
  intro index inside
  rw [checker_footer_parse_setup_metadata,checker_footer_parse_setup_byte]
  exact table index inside

theorem checker_footer_setup_guard_pc (s : MachineState) (pc : s.pc=4096+4*2190)
    (enough : CheckerFooterLowBodyFits s) :
    (checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s)).pc=4096+4*2199 := by
  rw [checker_footer_guard_pc,enough,ite_eq_right (by decide),checker_footer_setup_pc _ 7 (by decide),pc]
  rfl
theorem checker_footer_parse_setup_pc (s : MachineState) (pc : s.pc=4096+4*2190)
    (enough : CheckerFooterLowBodyFits s) : (checkerFooterParseSetupState s).pc=4096+4*2202 := by
  rw [checker_footer_parse_setup_eq,checker_footer_buffer_pc _ 3 (by decide),checker_footer_setup_guard_pc s pc enough]
  rfl
theorem checker_footer_parse_setup_execution (s : MachineState) (pc : s.pc=4096+4*2190)
    (enough : CheckerFooterLowBodyFits s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (11+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterParseSetupState s) coins
          return result.charge 11 0) := by
  have prefixPC : (checkerFooterSetupPrefix 7 s).pc=4096+4*2197 := by
    rw [checker_footer_setup_pc s 7 (by decide),pc]; rfl
  rw [checking_manifest_image,checker_footer_parse_setup_eq,show 11+fuel=7+(1+(3+fuel)) by omega,
    checker_footer_setup_execution s pc,checker_footer_guard_execution _ prefixPC,
    checker_footer_buffer_execution _ (checker_footer_setup_guard_pc s pc enough)]
  simp [Execution.charge,←Nat.add_assoc]

theorem checker_footer_short_setup_pc (s : MachineState) (pc : s.pc=4096+4*2190)
    (short : ¬CheckerFooterLowBodyFits s) :
    (checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s)).pc=4096+4*2198 := by
  have less : BitVec.ult ((checkerFooterSetupPrefix 7 s).getReg .x19) ((checkerFooterSetupPrefix 7 s).getReg .x20)=true := by
    unfold CheckerFooterLowBodyFits at short
    cases result : BitVec.ult ((checkerFooterSetupPrefix 7 s).getReg .x19) ((checkerFooterSetupPrefix 7 s).getReg .x20) <;> simp_all
  rw [checker_footer_guard_pc,less,ite_eq_left rfl,checker_footer_setup_pc _ 7 (by decide),pc]
  rfl

end CommitGolfCandidate.Chained.Native
