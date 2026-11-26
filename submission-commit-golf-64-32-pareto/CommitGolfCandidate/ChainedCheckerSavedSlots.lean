import CommitGolfCandidate.ChainedCheckerFooterComplete
import CommitGolfCandidate.ChainedInverseMemoryFrame

section

/-! Footer reconstruction writes only the raw output and parser descriptor ranges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem inverse_footer_field_byte_frame (s : MachineState) (query : Word)
    (away : ∀ index, index<30 → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (inverseFooterFieldState s).getByte query=s.getByte query := by
  rw [inverse_footer_field_byte,inverseFieldState,inverse_field_tail_byte,low_copy_destination,
    ite_eq_right (away 29 (by decide))]
  exact inverse_low_copy_byte_frame 29 s query (fun index inside => away index (by omega))

theorem inverse_footer_rows_byte_frame (count : Nat) (s : MachineState) (query : Word)
    (skip : s.getReg .x9=1#64)
    (away : ∀ index, index<30*count → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (inverseFooterRowsState count s).getByte query=s.getByte query := by
  induction count generalizing s with
  | zero => rw [inverse_footer_rows_zero]
  | succ count ih =>
    have nextSkip : (inverseFooterFieldState s).getReg .x9=1#64 := by
      rw [inverse_footer_field_register _ .x9 (by decide),inverse_field_frame _ _ .x9
        (by decide) (by decide) (by decide) (by decide),skip]
    have nextOutput : (inverseFooterFieldState s).getReg .x6=s.getReg .x6+30#64 := by
      rw [inverse_footer_field_register _ .x6 (by decide),inverse_field_destination,skip,BitVec.add_assoc]
      rfl
    rw [inverse_footer_rows_succ,ih _ nextSkip]
    · exact inverse_footer_field_byte_frame s query (fun index inside => away index (by omega))
    · intro index inside
      rw [nextOutput,byte_offset_add]
      exact away (30+index) (by omega)

theorem inverse_footer_rows_register (count : Nat) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x7,.x11,.x22]) :
    (inverseFooterRowsState count s).getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero => rw [inverse_footer_rows_zero]
  | succ count ih =>
    rw [inverse_footer_rows_succ,ih]
    cases reg <;> simp at kept
    all_goals rw [inverse_footer_field_register _ _ (by decide),inverse_field_frame _ _ _
      (by decide) (by decide) (by decide) (by decide)]

theorem checker_footer_reconstructed_register (count : Nat) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x5,.x6,.x7,.x9,.x11,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerFooterReconstructedState count s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_footer_reconstructed_eq,inverse_footer_rows_register _ _ _ (by decide),
    inverse_footer_entry_register,checker_footer_reconstruction_entry_eq,
    checker_footer_inverse_setup_register _ _ (by decide),MachineState.getReg_setPC,
    checker_footer_parsed_register _ _ _ (by decide)]

theorem checker_footer_reconstructed_byte_frame (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (query : Word)
    (outputAway : ∀ index, index<30*widths.length → query≠s.getReg .x6+BitVec.ofNat 64 index)
    (metadataAway : ∀ index, index<widths.length → query≠s.getReg .x8+BitVec.ofNat 64 (2*index)) :
    (checkerFooterReconstructedState widths.length s).getByte query=s.getByte query := by
  rw [checker_footer_reconstructed_eq,inverse_footer_rows_byte_frame]
  · rw [inverse_footer_entry_byte,checker_footer_reconstruction_byte]
    exact checker_footer_parsed_byte_frame s source widths bounded pointer rows metadata sourceEnd small table query metadataAway
  · rw [inverse_footer_entry_register,checker_footer_reconstruction_skip]
  · intro index inside
    rw [inverse_footer_entry_register,checker_footer_reconstruction_output]
    exact outputAway index inside

end CommitGolfCandidate.Chained.Native

end

section

/-! Delivered rejection halt and both footer rejection edges, independently of input contents. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerFailureState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 1)
theorem checker_failure_state_eq (s : MachineState) : checkerFailureState s=
    execInstrBr (execInstrBr s (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 1) := by rw [checkerFailureState]

theorem checker_failure_execution (s : MachineState) (pc : s.pc=4096+4*2364) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (3+fuel) s coins=pure ⟨.failure,checkerFailureState s,3,0⟩ := by
  have fetched0 : fetch chainedCheckerImage s=some (.base (.ADDI .x5 .x0 1)) :=
    chained_checker_ops_at 2364 (by rw [chained_checker_ops_length]; decide) s pc
  have pc1 : (execInstrBr s (.ADDI .x5 .x0 1)).pc=4096+4*2365 := by
    change s.pc+4=_
    rw [pc]; rfl
  have fetched1 : fetch chainedCheckerImage (execInstrBr s (.ADDI .x5 .x0 1))=some (.base (.ADDI .x10 .x0 1)) :=
    chained_checker_ops_at 2365 (by rw [chained_checker_ops_length]; decide) _ pc1
  have pc2 : (checkerFailureState s).pc=4096+4*2366 := by
    rw [checker_failure_state_eq]
    change (s.pc+4)+4=_
    rw [pc]; rfl
  have fetched2 : fetch chainedCheckerImage (checkerFailureState s)=some (.base .ECALL) :=
    chained_checker_ops_at 2366 (by rw [chained_checker_ops_length]; decide) _ pc2
  have halt : (checkerFailureState s).getReg .x5=1#64 := by rw [checker_failure_state_eq]; rfl
  have failed : (checkerFailureState s).getReg .x10=1#64 := by rw [checker_failure_state_eq]; rfl
  have block : execute chainedCheckerImage (2+(fuel+1)) s coins=
      (do let result ← execute chainedCheckerImage (fuel+1) (checkerFailureState s) coins
          return result.charge 2 0) := by
    rw [show 2+(fuel+1)=(1+(fuel+1))+1 by omega,
      execute_ordinary_step _ _ _ _ _ coins fetched0 (by rfl),
      show 1+(fuel+1)=(fuel+1)+1 by omega,
      execute_ordinary_step _ _ _ _ _ coins fetched1 (by rfl),←checker_failure_state_eq]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]
  rw [show 3+fuel=2+(fuel+1) by omega,block]
  unfold execute
  rw [fetched2]
  simp only [halt,failed]
  rfl

private theorem merged_ChainedCheckerFailure_reject_jump_execution (s : MachineState) (offset : BitVec 21)
    (fetched : fetch chainedCheckerImage s=some (.base (.JAL .x0 offset)))
    (target : s.pc+signExtend21 offset=4096+4*2364) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) s coins=
      pure ⟨.failure,checkerFailureState (s.setPC (4096+4*2364)),4,0⟩ := by
  have step : ordinaryStep s (.base (.JAL .x0 offset))=some (s.setPC (4096+4*2364)) := by
    change some (s.setPC (s.pc+signExtend21 offset))=_
    rw [target]
  rw [show 4+fuel=(3+fuel)+1 by omega,execute_ordinary_step _ _ _ _ _ coins fetched step,
    checker_failure_execution _ (by rfl)]
  rfl

theorem checker_footer_short_rejects (s : MachineState) (pc : s.pc=4096+4*2190)
    (short : ¬CheckerFooterLowBodyFits s) :
    ∃ after, ∀ fuel coins, execute (Artifact.submission.image .check) (12+fuel) s coins=pure ⟨.failure,after,12,0⟩ := by
  let guarded := checkerFooterSetupGuard (checkerFooterSetupPrefix 7 s)
  have prefixPC : (checkerFooterSetupPrefix 7 s).pc=4096+4*2197 := by
    rw [checker_footer_setup_pc _ 7 (by decide),pc]; rfl
  have guardPC : guarded.pc=4096+4*2198 := checker_footer_short_setup_pc s pc short
  have fetched : fetch chainedCheckerImage guarded=some (.base (.JAL .x0 664)) :=
    chained_checker_ops_at 2198 (by rw [chained_checker_ops_length]; decide) _ guardPC
  have target : guarded.pc+signExtend21 664=4096+4*2364 := by rw [guardPC]; rfl
  refine ⟨checkerFailureState (guarded.setPC (4096+4*2364)),?_⟩
  intro fuel coins
  rw [checking_manifest_image,show 12+fuel=7+(1+(4+fuel)) by omega,
    checker_footer_setup_execution s pc,checker_footer_guard_execution _ prefixPC,
    merged_ChainedCheckerFailure_reject_jump_execution guarded 664 fetched target]
  rfl

theorem checker_footer_invalid_rejects (count : Nat) (s : MachineState)
    (pc : (checkerFooterParsedState count s).pc=4096+4*2223)
    (invalid : (checkerFooterParsedState count s).getReg .x24=0#64) :
    ∃ after, ∀ fuel coins, execute (Artifact.submission.image .check) (5+fuel)
      (checkerFooterParsedState count s) coins=pure ⟨.failure,after,5,0⟩ := by
  let before := checkerFooterParsedState count s
  let next := before.setPC (before.pc+4)
  have fetched : fetch chainedCheckerImage before=some (.base (.BNE .x24 .x0 8)) :=
    chained_checker_ops_at 2223 (by rw [chained_checker_ops_length]; decide) _ pc
  have step : ordinaryStep before (.base (.BNE .x24 .x0 8))=some next := by
    change some (if before.getReg .x24 != before.getReg .x0 then _ else _)=_
    rw [invalid]; rfl
  have nextPC : next.pc=4096+4*2224 := by change before.pc+4=_; rw [pc]; rfl
  have jump : fetch chainedCheckerImage next=some (.base (.JAL .x0 560)) :=
    chained_checker_ops_at 2224 (by rw [chained_checker_ops_length]; decide) _ nextPC
  have target : next.pc+signExtend21 560=4096+4*2364 := by rw [nextPC]; rfl
  refine ⟨checkerFailureState (next.setPC (4096+4*2364)),?_⟩
  intro fuel coins
  rw [checking_manifest_image,show 5+fuel=(4+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ coins fetched step,merged_ChainedCheckerFailure_reject_jump_execution next 560 jump target]
  rfl

theorem checker_footer_flag_cases (count : Nat) (s : MachineState) :
    (checkerFooterParsedState count s).getReg .x24=0#64 ∨ (checkerFooterParsedState count s).getReg .x24=1#64 := by
  rw [checker_footer_parsed_eq,tail_validate_flag]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem checker_footer_noncanonical_flag (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+proof.length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+proof.length))
    (enough : CheckerFooterLowBodyFits s) (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (invalid : SplitCodec.unpack (InteriorCodec.footerSpec nodes) proof=none) :
    (checkerFooterParsedState nodes.length s).getReg .x24=0#64 := by
  rcases checker_footer_flag_cases nodes.length s with zero | one
  · exact zero
  · have accepted := (checker_footer_parsed_accepts s source nodes proof bounded pointer rows metadata table proofFit endPointer enough memory one).1
    rw [invalid] at accepted
    cases accepted

theorem checker_footer_invalid_complete (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s)
    (invalid : (checkerFooterParsedState widths.length s).getReg .x24=0#64) :
    ∃ after, ∀ fuel coins, execute (Artifact.submission.image .check)
      (11+checkerFooterParserCycles widths.length s+5+fuel) s coins=
      pure ⟨.failure,after,11+checkerFooterParserCycles widths.length s+5,0⟩ := by
  have parsedPC := checker_footer_parsed_pc s source widths bounded pointer rows metadata sourceEnd small table pc enough
  obtain ⟨after,rejects⟩ := checker_footer_invalid_rejects widths.length s parsedPC invalid
  refine ⟨after,?_⟩
  intro fuel coins
  rw [show 11+checkerFooterParserCycles widths.length s+5+fuel=
    (11+checkerFooterParserCycles widths.length s)+(5+fuel) by omega,
    checker_footer_setup_parser_execution s source widths bounded pointer rows metadata sourceEnd small table pc enough,rejects fuel coins]
  simp [Execution.charge,Nat.add_comm]

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual decoder ABI restoration and nonempty dispatch to the cryptographic checker. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerRestoreOps : List Instr :=
  [.LD .x11 .x8 1024,.LD .x13 .x8 1032,.LD .x14 .x8 1040,.LD .x16 .x8 1048,
   .SUB .x17 .x6 .x12,.ADDI .x15 .x12 0]
@[irreducible] def checkerRestorePrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerRestoreOps.getD index .EBREAK)) n
theorem checker_restore_zero (s : MachineState) : checkerRestorePrefix 0 s=s := by rw [checkerRestorePrefix]; rfl
theorem checker_restore_succ (n : Nat) (s : MachineState) : checkerRestorePrefix (n+1) s=
    execInstrBr (checkerRestorePrefix n s) (checkerRestoreOps.getD n .EBREAK) := by unfold checkerRestorePrefix; rfl
theorem checker_restore_at : OpsAt chainedCheckerImage (4096+4*2352) checkerRestoreOps :=
  chained_checker_slice_at 2352 6 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_restore_metadata (n : Nat) (s : MachineState) (small : n≤6) :
    (checkerRestorePrefix n s).getReg .x8=s.getReg .x8 := by
  have step (t : MachineState) (i : Fin 6) : (execInstrBr t (checkerRestoreOps.getD i.val .EBREAK)).getReg .x8=t.getReg .x8 := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_restore_zero]
  | succ n ih => rw [checker_restore_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_restore_memory (n : Nat) (s : MachineState) (small : n≤6) (query : Word) :
    (checkerRestorePrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 6) : (execInstrBr t (checkerRestoreOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_restore_zero]
  | succ n ih => rw [checker_restore_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_restore_pc (n : Nat) (s : MachineState) (small : n≤6) :
    (checkerRestorePrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 6) : (execInstrBr t (checkerRestoreOps.getD i.val .EBREAK)).pc=t.pc+4 := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_restore_zero]; simp
  | succ n ih =>
    rw [checker_restore_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1

private theorem merged_ChainedCheckerRestore_restore_ordinary (s : MachineState) (i : Fin 6)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) :
    ordinaryStep s (.base (checkerRestoreOps.getD i.val .EBREAK))=some (execInstrBr s (checkerRestoreOps.getD i.val .EBREAK)) := by
  fin_cases i
  all_goals first
    | rfl
    | change (if accessValid (s.getReg .x8+_) 8 then _ else _)=_
      rw [metadata]
      exact ite_eq_left (by decide +kernel)

theorem checker_restore_loads_execution (s : MachineState) (pc : s.pc=4096+4*2352)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (6+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRestorePrefix 6 s) coins
          return result.charge 6 0) := by
  suffices entry : execute chainedCheckerImage (6+fuel) (checkerRestorePrefix 0 s) coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRestorePrefix 6 s) coins
          return result.charge 6 0) by simpa only [checker_restore_zero] using entry
  apply execute_unit_steps (states := fun n => checkerRestorePrefix n s)
  intro i inside
  refine ⟨.base (checkerRestoreOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_restore_at i (by exact inside)
    rw [checker_restore_pc i s (by omega),pc]
  · rw [checker_restore_succ]
    exact merged_ChainedCheckerRestore_restore_ordinary _ ⟨i,inside⟩ ((checker_restore_metadata i s (by omega)).trans metadata)
  · interval_cases i <;> rfl

@[irreducible] def checkerRestoreControls (s : MachineState) : Nat → MachineState
  | 0 => s
  | 1 => s.setPC (4096+4*2361)
  | 2 => s.setPC (4096+4*2362)
  | _ => s.setPC (4096+4*2367)
private theorem merged_ChainedCheckerRestore_controls_zero (s : MachineState) : checkerRestoreControls s 0=s := by simp [checkerRestoreControls]
private theorem merged_ChainedCheckerRestore_controls_one (s : MachineState) : checkerRestoreControls s 1=s.setPC (4096+4*2361) := by simp [checkerRestoreControls]
private theorem merged_ChainedCheckerRestore_controls_two (s : MachineState) : checkerRestoreControls s 2=s.setPC (4096+4*2362) := by simp [checkerRestoreControls]
private theorem merged_ChainedCheckerRestore_controls_three (s : MachineState) : checkerRestoreControls s 3=s.setPC (4096+4*2367) := by simp [checkerRestoreControls]

private theorem merged_ChainedCheckerRestore_restore_controls_execution (s : MachineState) (pc : s.pc=4096+4*2358)
    (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (3+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (s.setPC (4096+4*2367)) coins
          return result.charge 3 0) := by
  have block : execute chainedCheckerImage (3+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRestoreControls s 3) coins
          return result.charge 3 0) := by
    suffices entry : execute chainedCheckerImage (3+fuel) (checkerRestoreControls s 0) coins=
        (do let result ← execute chainedCheckerImage fuel (checkerRestoreControls s 3) coins
            return result.charge 3 0) by simpa only [merged_ChainedCheckerRestore_controls_zero] using entry
    apply execute_unit_steps (states := checkerRestoreControls s)
    intro i inside
    interval_cases i
    · refine ⟨.base (.JAL .x0 12),?_,?_,by rfl⟩
      · rw [merged_ChainedCheckerRestore_controls_zero]
        exact chained_checker_ops_at 2358 (by rw [chained_checker_ops_length]; decide) _ pc
      · rw [merged_ChainedCheckerRestore_controls_zero,merged_ChainedCheckerRestore_controls_one]
        change some (s.setPC (s.pc+signExtend21 12))=_
        rw [pc]; rfl
    · refine ⟨.base (.BEQ .x16 .x0 2592),?_,?_,by rfl⟩
      · rw [merged_ChainedCheckerRestore_controls_one]
        exact chained_checker_ops_at 2361 (by rw [chained_checker_ops_length]; decide) _ (by rfl)
      · rw [merged_ChainedCheckerRestore_controls_one,merged_ChainedCheckerRestore_controls_two]
        change some (if s.getReg .x16==0#64 then _ else _)=_
        rw [if_neg (by simpa only [beq_iff_eq] using nonempty)]
        rfl
    · refine ⟨.base (.JAL .x0 20),?_,?_,by rfl⟩
      · rw [merged_ChainedCheckerRestore_controls_two]
        exact chained_checker_ops_at 2362 (by rw [chained_checker_ops_length]; decide) _ (by rfl)
      · rw [merged_ChainedCheckerRestore_controls_two,merged_ChainedCheckerRestore_controls_three]; rfl
  simpa only [merged_ChainedCheckerRestore_controls_three] using block

@[irreducible] def checkerDecoderRestoredState (s : MachineState) : MachineState :=
  (checkerRestorePrefix 6 s).setPC (4096+4*2367)
theorem checker_decoder_restored_eq (s : MachineState) : checkerDecoderRestoredState s=
    (checkerRestorePrefix 6 s).setPC (4096+4*2367) := by rw [checkerDecoderRestoredState]

theorem checker_decoder_restored_view (s : MachineState) :
    (checkerDecoderRestoredState s).pc=4096+4*2367 ∧
    (checkerDecoderRestoredState s).getReg .x11=s.getMem (s.getReg .x8+1024) ∧
    (checkerDecoderRestoredState s).getReg .x13=s.getMem (s.getReg .x8+1032) ∧
    (checkerDecoderRestoredState s).getReg .x14=s.getMem (s.getReg .x8+1040) ∧
    (checkerDecoderRestoredState s).getReg .x16=s.getMem (s.getReg .x8+1048) ∧
    (checkerDecoderRestoredState s).getReg .x15=s.getReg .x12 ∧
    (checkerDecoderRestoredState s).getReg .x17=s.getReg .x6-s.getReg .x12 := by
  rw [checker_decoder_restored_eq]
  simp only [MachineState.getReg_setPC,checker_restore_succ,checker_restore_zero]
  exact ⟨rfl,rfl,rfl,rfl,rfl,BitVec.add_zero _,rfl⟩

theorem checker_decoder_restored_memory (s : MachineState) (query : Word) :
    (checkerDecoderRestoredState s).getMem query=s.getMem query := by
  rw [checker_decoder_restored_eq]
  exact checker_restore_memory 6 s (by decide) query

theorem checker_decoder_restore_execution (s : MachineState) (pc : s.pc=4096+4*2352)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (nonempty : s.getMem (s.getReg .x8+1048)≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerDecoderRestoredState s) coins
          return result.charge 9 0) := by
  have restoredPC : (checkerRestorePrefix 6 s).pc=4096+4*2358 := by
    rw [checker_restore_pc 6 s (by decide),pc]; rfl
  have restoredCount : (checkerRestorePrefix 6 s).getReg .x16≠0#64 := by
    have same := (checker_decoder_restored_view s).2.2.2.2.1
    rw [checker_decoder_restored_eq,MachineState.getReg_setPC] at same
    exact fun zero => nonempty (same.symm.trans zero)
  rw [checking_manifest_image,checker_decoder_restored_eq,show 9+fuel=6+(3+fuel) by omega,
    checker_restore_loads_execution s pc metadata,merged_ChainedCheckerRestore_restore_controls_execution _ restoredPC restoredCount]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native

end

section

/-! Original ABI words survive the record/footer decoders and feed actual restoration. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

def checkerSavedReg (slot : Fin 4) : Reg := [.x11,.x13,.x14,.x16].getD slot.val .x0
def checkerSavedAddress (slot : Fin 4) : Nat := checkingMetadataBase+1024+8*slot.val
def CheckerSavedABI (original current : MachineState) : Prop :=
  ∀ slot : Fin 4, current.getMem (BitVec.ofNat 64 (checkerSavedAddress slot))=original.getReg (checkerSavedReg slot)

theorem checker_saved_address_aligned (slot : Fin 4) : checkerSavedAddress slot%8=0 := by
  fin_cases slot <;> decide +kernel
theorem checker_saved_byte_range (slot : Fin 4) (index : Nat) (inside : index<8) :
    checkingMetadataBase+1024≤checkerSavedAddress slot+index ∧
    checkerSavedAddress slot+index<checkingMetadataBase+1056 ∧ checkerSavedAddress slot+index<2^64 := by
  have room := checking_metadata_room
  have bound := slot.isLt
  unfold checkerSavedAddress
  omega

theorem checker_saved_abi_frame (original before after : MachineState)
    (saved : CheckerSavedABI original before)
    (memory : ∀ slot : Fin 4, after.getMem (BitVec.ofNat 64 (checkerSavedAddress slot))=
      before.getMem (BitVec.ofNat 64 (checkerSavedAddress slot))) : CheckerSavedABI original after :=
  fun slot => (memory slot).trans (saved slot)

theorem checker_saved_abi_byte_frame (original before after : MachineState)
    (saved : CheckerSavedABI original before)
    (memory : ∀ slot : Fin 4, ∀ index, index<8 →
      after.getByte (BitVec.ofNat 64 (checkerSavedAddress slot+index))=
      before.getByte (BitVec.ofNat 64 (checkerSavedAddress slot+index))) : CheckerSavedABI original after :=
  checker_saved_abi_frame original before after saved (fun slot =>
    aligned_word_of_byte_frame before after (checkerSavedAddress slot) (checker_saved_address_aligned slot) (memory slot))

theorem checker_record_loop_saved_abi (original s : MachineState) (records : List InteriorCodec.Record) (footer : Proof)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase)
    (saved : CheckerSavedABI original s) : CheckerSavedABI original (checkerRecordLoopState records s) := by
  apply checker_saved_abi_byte_frame original s _ saved
  intro slot index inside
  have range := checker_saved_byte_range slot index inside
  have outputEnd := ready.outputRoom
  have outputStart := ready.outputStart
  rw [checker_record_loop_byte_frame records footer s source outputBase _ ready]
  · intro written before
    rw [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ range.2.2 (by omega) (by omega)
  · intro written before
    rw [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ range.2.2 (by omega) (by omega)

theorem checker_footer_widths_saved_abi (original origin s : MachineState) (groups widths : List Nat) (node : Nat)
    (ready : CheckerFooterWidthsReady groups widths origin s node)
    (saved : CheckerSavedABI original origin) : CheckerSavedABI original s := by
  apply checker_saved_abi_byte_frame original origin s saved
  intro slot index inside
  have range := checker_saved_byte_range slot index inside
  exact ready.outside _ (Or.inr (by omega)) range.2.2

theorem checker_footer_init_saved_abi (original s : MachineState) (saved : CheckerSavedABI original s) :
    CheckerSavedABI original (checkerFooterInitPrefix s 4) :=
  checker_saved_abi_frame original s _ saved (fun _ => checker_footer_init_memory s _)

theorem checker_footer_reconstructed_saved_abi (original s : MachineState) (source output : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (destination : s.getReg .x6=BitVec.ofNat 64 output)
    (outputEnd : output+30*widths.length≤checkingMetadataBase)
    (saved : CheckerSavedABI original s) : CheckerSavedABI original (checkerFooterReconstructedState widths.length s) := by
  apply checker_saved_abi_byte_frame original s _ saved
  intro slot index inside
  have range := checker_saved_byte_range slot index inside
  rw [checker_footer_reconstructed_byte_frame s source widths bounded pointer rows metadata sourceEnd small table]
  · intro written before
    rw [destination,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ range.2.2 (by omega) (by omega)
  · intro written before
    rw [metadata,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ range.2.2 (by omega) (by omega)

theorem checker_restore_original_abi (original current : MachineState)
    (metadata : current.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (saved : CheckerSavedABI original current) :
    ∀ slot : Fin 4, (checkerDecoderRestoredState current).getReg (checkerSavedReg slot)=original.getReg (checkerSavedReg slot) := by
  have view := checker_decoder_restored_view current
  intro slot
  fin_cases slot
  · exact view.2.1.trans (by rw [metadata]; exact saved ⟨0,by decide⟩)
  · exact view.2.2.1.trans (by rw [metadata]; exact saved ⟨1,by decide⟩)
  · exact view.2.2.2.1.trans (by rw [metadata]; exact saved ⟨2,by decide⟩)
  · exact view.2.2.2.2.1.trans (by rw [metadata]; exact saved ⟨3,by decide⟩)

theorem checker_restore_original_nonempty (original current : MachineState)
    (metadata : current.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (saved : CheckerSavedABI original current) (nonempty : original.getReg .x16≠0#64) :
    current.getMem (current.getReg .x8+1048)≠0#64 := by
  rw [metadata]
  have count := saved ⟨3,by decide⟩
  change current.getMem (BitVec.ofNat 64 (checkingMetadataBase+1048))=original.getReg .x16 at count
  rw [show BitVec.ofNat 64 checkingMetadataBase+1048=BitVec.ofNat 64 (checkingMetadataBase+1048) from (BitVec.ofNat_add _ _).symm,count]
  exact nonempty

theorem checker_footer_restore_original (original s : MachineState) (source output : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (destination : s.getReg .x6=BitVec.ofNat 64 output)
    (outputEnd : output+30*widths.length≤checkingMetadataBase)
    (saved : CheckerSavedABI original s) (nonempty : original.getReg .x16≠0#64)
    (pc : (checkerFooterReconstructedState widths.length s).pc=4096+4*2352) :
    (∀ slot : Fin 4, (checkerDecoderRestoredState (checkerFooterReconstructedState widths.length s)).getReg (checkerSavedReg slot)=
      original.getReg (checkerSavedReg slot)) ∧
    (∀ fuel coins, execute (Artifact.submission.image .check) (9+fuel) (checkerFooterReconstructedState widths.length s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel
            (checkerDecoderRestoredState (checkerFooterReconstructedState widths.length s)) coins
          return result.charge 9 0)) := by
  have finalSaved := checker_footer_reconstructed_saved_abi original s source output widths bounded pointer rows metadata sourceEnd
    small table destination outputEnd saved
  have finalMeta : (checkerFooterReconstructedState widths.length s).getReg .x8=BitVec.ofNat 64 checkingMetadataBase :=
    (checker_footer_reconstructed_register widths.length s .x8 (by decide)).trans metadata
  refine ⟨checker_restore_original_abi original _ finalMeta finalSaved,?_⟩
  intro fuel coins
  exact checker_decoder_restore_execution _ pc finalMeta
    (checker_restore_original_nonempty original _ finalMeta finalSaved nonempty) fuel coins

end CommitGolfCandidate.Chained.Native

end
