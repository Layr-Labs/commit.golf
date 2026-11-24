import CommitGolfCandidate.ChainedCheckerRecordUntrusted
import CommitGolfCandidate.ChainedFooterAdvance

section

/-! Installed footer initialization and composition with the complete record decoder. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerFooterInitOps : List Instr :=
  [.ADDI .x7 .x8 0,.ADDI .x22 .x0 0,.ADDI .x29 .x0 256,.ADDI .x30 .x0 1]
@[irreducible] def checkerFooterInitPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFooterInitOps.take n).foldl execInstrBr s

theorem checker_footer_init_at : OpsAt chainedCheckerImage (4096+4*2164) checkerFooterInitOps :=
  chained_checker_slice_at 2164 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_footer_init_zero (s : MachineState) : checkerFooterInitPrefix s 0=s := by
  rw [checkerFooterInitPrefix]
  rfl
theorem checker_footer_init_succ (s : MachineState) (n : Nat) (small : n<4) :
    checkerFooterInitPrefix s (n+1)=execInstrBr (checkerFooterInitPrefix s n) (checkerFooterInitOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerFooterInitPrefix <;> rfl
theorem checker_footer_init_pc (s : MachineState) (n : Nat) (small : n≤4) :
    (checkerFooterInitPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_footer_init_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_footer_init_succ s n (by omega)]
    have step : (execInstrBr (checkerFooterInitPrefix s n) (checkerFooterInitOps.getD n .EBREAK)).pc=
        (checkerFooterInitPrefix s n).pc+4 := by
      have bound : n<4 := by omega
      interval_cases n <;> rfl
    rw [step,ih (by omega)]
    change (s.pc+BitVec.ofNat 64 (4*n))+BitVec.ofNat 64 4=_
    rw [byte_offset_add]
    congr 2
theorem checker_footer_init_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x7,.x22,.x29,.x30]) : (checkerFooterInitPrefix s 4).getReg reg=s.getReg reg := by
  unfold checkerFooterInitPrefix
  cases reg <;> simp at kept <;> rfl
theorem checker_footer_init_byte (s : MachineState) (query : Word) :
    (checkerFooterInitPrefix s 4).getByte query=s.getByte query := by rw [checkerFooterInitPrefix]; rfl
theorem checker_footer_init_memory (s : MachineState) (query : Word) :
    (checkerFooterInitPrefix s 4).getMem query=s.getMem query := by rw [checkerFooterInitPrefix]; rfl
theorem checker_footer_init_metadata (s : MachineState) : (checkerFooterInitPrefix s 4).getReg .x7=s.getReg .x8 := by
  rw [checkerFooterInitPrefix]
  exact BitVec.add_zero _
theorem checker_footer_init_count (s : MachineState) : (checkerFooterInitPrefix s 4).getReg .x22=0 := by
  rw [checkerFooterInitPrefix]; rfl
theorem checker_footer_init_limit (s : MachineState) : (checkerFooterInitPrefix s 4).getReg .x29=256 := by
  rw [checkerFooterInitPrefix]; rfl
theorem checker_footer_init_node (s : MachineState) : (checkerFooterInitPrefix s 4).getReg .x30=1 := by
  rw [checkerFooterInitPrefix]; rfl

theorem checker_footer_init_execution (s : MachineState) (pc : s.pc=4096+4*2164) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterInitPrefix s 4) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_footer_init_zero s]
  apply execute_unit_steps (states := checkerFooterInitPrefix s)
  intro i inside
  refine ⟨.base (checkerFooterInitOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_init_at i inside
    rw [checker_footer_init_pc s i (by omega),pc]
  · rw [checker_footer_init_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_record_footer_initialization (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerRecordLoopCycles records s+4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel
            (checkerFooterInitPrefix (checkerRecordLoopState records s) 4) coins
          return result.charge (checkerRecordLoopCycles records s+4) 0) := by
  have endReady := checker_record_loop_ready records footer s source outputBase ready
  rw [Nat.add_assoc,checker_record_loop_execution records footer s source outputBase ready,
    checker_footer_init_execution _ (by simpa using endReady.pc)]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_record_footer_entry (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase) :
    let after := checkerFooterInitPrefix (checkerRecordLoopState records s) 4
    after.pc=4096+4*2168 ∧ after.getReg .x7=BitVec.ofNat 64 checkingMetadataBase ∧
    after.getReg .x22=0 ∧ after.getReg .x29=256 ∧ after.getReg .x30=1 ∧
    after.getReg .x18=BitVec.ofNat 64 (source+482*records.length) ∧
    after.getReg .x6=BitVec.ofNat 64 (outputBase+498*records.length) ∧
    BytesAt after (BitVec.ofNat 64 outputBase) (rawRecordStream records) ∧
    BytesAt after (BitVec.ofNat 64 (source+482*records.length)) footer := by
  have endReady := checker_record_loop_ready records footer s source outputBase ready
  dsimp only
  refine ⟨?_,?_,checker_footer_init_count _,checker_footer_init_limit _,checker_footer_init_node _,?_,?_,?_,?_⟩
  · rw [checker_footer_init_pc _ 4 (by decide),show (checkerRecordLoopState records s).pc=4096+4*2164 by simpa using endReady.pc]
    rfl
  · rw [checker_footer_init_metadata]
    exact endReady.metadata
  · rw [checker_footer_init_register _ .x18 (by decide)]
    exact endReady.sourcePointer
  · rw [checker_footer_init_register _ .x6 (by decide)]
    exact endReady.outputPointer
  · intro index inside
    rw [checker_footer_init_byte]
    exact checker_record_loop_memory records footer s source outputBase ready index inside
  · intro index inside
    rw [checker_footer_init_byte]
    simpa only [encodedRecords,List.flatMap_nil,List.nil_append] using endReady.input index inside

end CommitGolfCandidate.Chained.Native

end

section

/-! Installed footer width emission, including its row-count increment. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerFooterWidthState (s : MachineState) : MachineState :=
  execInstrBr (footerWidthsState s) (.ADDI .x22 .x22 1)
def checkerFooterWidthCycles (s : MachineState) : Nat := footerHeaderCycles s+3
theorem checker_footer_width_eq (s : MachineState) : checkerFooterWidthState s=
    execInstrBr (footerWidthsState s) (.ADDI .x22 .x22 1) := by rw [checkerFooterWidthState]

private theorem merged_ChainedCheckerFooterWidth_row_pc (s : MachineState) : (execInstrBr s (.ADDI .x22 .x22 1)).pc=s.pc+4 := rfl
private theorem merged_ChainedCheckerFooterWidth_row_byte (s : MachineState) (query : Word) :
    (execInstrBr s (.ADDI .x22 .x22 1)).getByte query=s.getByte query := rfl
private theorem merged_ChainedCheckerFooterWidth_row_register (s : MachineState) (reg : Reg) (different : reg≠.x22) :
    (execInstrBr s (.ADDI .x22 .x22 1)).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
private theorem merged_ChainedCheckerFooterWidth_row_count (s : MachineState) :
    (execInstrBr s (.ADDI .x22 .x22 1)).getReg .x22=s.getReg .x22+1 := rfl

theorem checker_footer_width_pc (s : MachineState) (pc : s.pc=4096+4*2175) :
    (checkerFooterWidthState s).pc=4096+4*2182 := by
  rw [checker_footer_width_eq,merged_ChainedCheckerFooterWidth_row_pc,footerWidthsState,width_store_pc,footer_header_pc,pc]
  rfl
theorem checker_footer_width_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x7,.x9,.x10,.x22]) : (checkerFooterWidthState s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_footer_width_eq,merged_ChainedCheckerFooterWidth_row_register _ _ (by decide),
    footer_widths_register _ _ (by decide) (by decide) (by decide)]
theorem checker_footer_width_pointer (s : MachineState) :
    (checkerFooterWidthState s).getReg .x7=s.getReg .x7+2 := by
  rw [checker_footer_width_eq,merged_ChainedCheckerFooterWidth_row_register _ .x7 (by decide),footer_widths_pointer]
theorem checker_footer_width_count (s : MachineState) :
    (checkerFooterWidthState s).getReg .x22=s.getReg .x22+1 := by
  rw [checker_footer_width_eq,merged_ChainedCheckerFooterWidth_row_count,footer_widths_register _ .x22 (by decide) (by decide) (by decide)]
theorem checker_footer_width_byte (s : MachineState) (node : Nat) (fit : node<2^64)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) (query : Word) :
    (checkerFooterWidthState s).getByte query=
      if query=s.getReg .x7+1 then BitVec.ofNat 8 (InteriorCodec.footerWidth node-232) else s.getByte query := by
  rw [checker_footer_width_eq,merged_ChainedCheckerFooterWidth_row_byte,footer_widths_byte s node fit cursor limit]

theorem checker_footer_width_execution (s : MachineState) (pc : s.pc=4096+4*2175)
    (access : accessValid (s.getReg .x7+1) 1=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFooterWidthCycles s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterWidthState s) coins
          return result.charge (checkerFooterWidthCycles s) 0) := by
  rw [checking_manifest_image]
  have nextPC : (footerWidthsState s).pc=4096+4*2181 := by
    rw [footerWidthsState,width_store_pc,footer_header_pc,pc]
    rfl
  have code : OpsAt chainedCheckerImage (4096+4*2181) [.ADDI .x22 .x22 1] :=
    chained_checker_slice_at 2181 1 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  have fetched : fetch chainedCheckerImage (footerWidthsState s)=some (.base (.ADDI .x22 .x22 1)) :=
    code 0 (by decide) _ nextPC
  have ordinary : ordinaryStep (footerWidthsState s) (.base (.ADDI .x22 .x22 1))=
      some (checkerFooterWidthState s) := by rw [checker_footer_width_eq]; rfl
  rw [checkerFooterWidthCycles,show footerHeaderCycles s+3+fuel=footerHeaderCycles s+2+(fuel+1) by omega,
    footer_widths_execution chainedCheckerImage _ chained_checker_footer_width_at s pc access,
    execute_ordinary_step chainedCheckerImage _ _ _ fuel coins fetched ordinary]
  have arithmetic (cycles : Nat) : 2+(1+cycles)=3+cycles := by omega
  simp [Execution.charge,instructionCycles,Nat.add_assoc,arithmetic]

theorem checker_footer_width_cycles (s : MachineState) (node : Nat) (bounded : node<512)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    checkerFooterWidthCycles s=if node<256 then 7 else 6 := by
  rw [checkerFooterWidthCycles,footerHeaderCycles,footerWide,cursor,limit,BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node<2^64)]
  by_cases internal : node<256 <;> simp [internal]

end CommitGolfCandidate.Chained.Native

end

section

/-! The installed footer reads marks through x4 and dispatches to width emission or descent. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerFooterLookupOps : List Instr :=
  [.SLLI .x31 .x30 3,.ADD .x31 .x31 .x4,.LD .x31 .x31 0,.BEQ .x31 .x0 16]
def checkerFooterMarkAddress (s : MachineState) : Word := (s.getReg .x30<<<3)+s.getReg .x4
@[irreducible] def checkerFooterLookupPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFooterLookupOps.take n).foldl execInstrBr s
def checkerFooterEmpty (s : MachineState) : Bool := s.getReg .x31 == 0
def checkerFooterLookupGuard (s : MachineState) : MachineState := execInstrBr s (.BEQ .x31 .x0 16)
@[irreducible] def checkerFooterLookupState (s : MachineState) : MachineState :=
  checkerFooterLookupGuard (checkerFooterLookupPrefix s 3)
theorem checker_footer_lookup_eq (s : MachineState) :
    checkerFooterLookupState s=checkerFooterLookupGuard (checkerFooterLookupPrefix s 3) := by
  rw [checkerFooterLookupState]
theorem checker_footer_lookup_at : OpsAt chainedCheckerImage (4096+4*2168) checkerFooterLookupOps :=
  chained_checker_slice_at 2168 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_lookup_zero (s : MachineState) : checkerFooterLookupPrefix s 0=s := by
  rw [checkerFooterLookupPrefix]; rfl
theorem checker_footer_lookup_succ (s : MachineState) (n : Nat) (small : n<3) :
    checkerFooterLookupPrefix s (n+1)=execInstrBr (checkerFooterLookupPrefix s n) (checkerFooterLookupOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerFooterLookupPrefix <;> rfl
theorem checker_footer_lookup_prefix_pc (s : MachineState) (n : Nat) (small : n≤3) :
    (checkerFooterLookupPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_footer_lookup_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_footer_lookup_succ s n (by omega)]
    have step : (execInstrBr (checkerFooterLookupPrefix s n) (checkerFooterLookupOps.getD n .EBREAK)).pc=
        (checkerFooterLookupPrefix s n).pc+4 := by
      have bound : n<3 := by omega
      interval_cases n <;> rfl
    rw [step,ih (by omega)]
    change (s.pc+BitVec.ofNat 64 (4*n))+BitVec.ofNat 64 4=_
    rw [byte_offset_add]
    congr 2

private theorem merged_ChainedCheckerFooterLookup_lookup_guard_register (s : MachineState) (reg : Reg) :
    (checkerFooterLookupGuard s).getReg reg=s.getReg reg := by
  by_cases empty : checkerFooterEmpty s
  · have same : checkerFooterLookupGuard s=s.setPC (s.pc+16) := ite_eq_left empty
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : checkerFooterLookupGuard s=s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
private theorem merged_ChainedCheckerFooterLookup_lookup_guard_memory (s : MachineState) (query : Word) :
    (checkerFooterLookupGuard s).getMem query=s.getMem query := by
  by_cases empty : checkerFooterEmpty s
  · have same : checkerFooterLookupGuard s=s.setPC (s.pc+16) := ite_eq_left empty
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : checkerFooterLookupGuard s=s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
private theorem merged_ChainedCheckerFooterLookup_lookup_guard_pc (s : MachineState) : (checkerFooterLookupGuard s).pc=
    if checkerFooterEmpty s then s.pc+16 else s.pc+4 := by
  change (if checkerFooterEmpty s then s.setPC (s.pc+16) else s.setPC (s.pc+4)).pc=_
  split <;> rfl

theorem checker_footer_lookup_register (s : MachineState) (reg : Reg) (kept : reg≠.x31) :
    (checkerFooterLookupState s).getReg reg=s.getReg reg := by
  rw [checker_footer_lookup_eq,merged_ChainedCheckerFooterLookup_lookup_guard_register,checkerFooterLookupPrefix]
  cases reg <;> first | contradiction | rfl
theorem checker_footer_lookup_memory (s : MachineState) (query : Word) :
    (checkerFooterLookupState s).getMem query=s.getMem query := by
  rw [checker_footer_lookup_eq,merged_ChainedCheckerFooterLookup_lookup_guard_memory,checkerFooterLookupPrefix]
  rfl
theorem checker_footer_lookup_byte (s : MachineState) (query : Word) :
    (checkerFooterLookupState s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_lookup_memory]
theorem checker_footer_lookup_load (s : MachineState) :
    (checkerFooterLookupPrefix s 3).getReg .x31=s.getMem (checkerFooterMarkAddress s) := by
  rw [checkerFooterLookupPrefix]
  change s.getMem (((s.getReg .x30<<<3)+s.getReg .x4)+0#64)=_
  rw [BitVec.add_zero]
  rfl
theorem checker_footer_lookup_pc (s : MachineState) (pc : s.pc=4096+4*2168) :
    (checkerFooterLookupState s).pc=
      if s.getMem (checkerFooterMarkAddress s)=0 then 4096+4*2175 else 4096+4*2172 := by
  rw [checker_footer_lookup_eq,merged_ChainedCheckerFooterLookup_lookup_guard_pc,checkerFooterEmpty,checker_footer_lookup_load,
    checker_footer_lookup_prefix_pc _ 3 (by decide),pc]
  by_cases empty : s.getMem (checkerFooterMarkAddress s)=0 <;> simp [empty]

theorem checker_footer_lookup_prefix_execution (s : MachineState) (pc : s.pc=4096+4*2168)
    (valid : accessValid (checkerFooterMarkAddress s) 8=true) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (3+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterLookupPrefix s 3) coins
          return result.charge 3 0) := by
  conv_lhs => rw [←checker_footer_lookup_zero s]
  apply execute_unit_steps (states := checkerFooterLookupPrefix s)
  intro i inside
  refine ⟨.base (checkerFooterLookupOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_lookup_at i (by change i<4; omega)
    rw [checker_footer_lookup_prefix_pc s i (by omega),pc]
  · rw [checker_footer_lookup_succ s i inside]
    interval_cases i
    · rw [checkerFooterLookupPrefix]; rfl
    · rw [checkerFooterLookupPrefix]; rfl
    · have access : memoryArgumentsValid (checkerFooterLookupPrefix s 2) (.LD .x31 .x31 0)=true := by
        rw [checkerFooterLookupPrefix]
        change accessValid (((s.getReg .x30<<<3)+s.getReg .x4)+0#64) 8=true
        simpa only [checkerFooterMarkAddress,BitVec.add_zero] using valid
      change ordinaryStep (checkerFooterLookupPrefix s 2) (.base (.LD .x31 .x31 0))=_
      simp only [ordinaryStep,access,↓reduceIte]
      rfl
  · interval_cases i <;> rfl

theorem checker_footer_lookup_execution (s : MachineState) (pc : s.pc=4096+4*2168)
    (valid : accessValid (checkerFooterMarkAddress s) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterLookupState s) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  have fetched : fetch chainedCheckerImage (checkerFooterLookupPrefix s 3)=some (.base (.BEQ .x31 .x0 16)) := by
    apply checker_footer_lookup_at 3 (by decide)
    rw [checker_footer_lookup_prefix_pc _ 3 (by decide),pc]
  have ordinary : ordinaryStep (checkerFooterLookupPrefix s 3) (.base (.BEQ .x31 .x0 16))=
      some (checkerFooterLookupState s) := by rw [checker_footer_lookup_eq]; rfl
  rw [show 4+fuel=3+(fuel+1) by omega,checker_footer_lookup_prefix_execution s pc valid,
    execute_ordinary_step chainedCheckerImage _ _ _ fuel coins fetched ordinary]
  have arithmetic (cycles : Nat) : 3+(1+cycles)=4+cycles := by omega
  simp [Execution.charge,instructionCycles,arithmetic]

theorem checker_footer_mark_address (s : MachineState) (node : Nat)
    (base : s.getReg .x4=4096) (cursor : s.getReg .x30=BitVec.ofNat 64 node) :
    checkerFooterMarkAddress s=BitVec.ofNat 64 (4096+8*node) := by
  rw [checkerFooterMarkAddress,cursor,base,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 node*BitVec.ofNat 64 8+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega

theorem checker_footer_lookup_dispatch (groups : List Nat) (s : MachineState) (node height : Nat)
    (pc : s.pc=4096+4*2168) (base : s.getReg .x4=4096)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (span : CapSpan node height)
    (marks : ∀ index, index<512 → s.getMem (BitVec.ofNat 64 (4096+8*index))=markWord groups index) :
    (checkerFooterLookupState s).pc=if capIsMarked groups node height then 4096+4*2172 else 4096+4*2175 := by
  rw [checker_footer_lookup_pc s pc,checker_footer_mark_address s node base cursor,
    marks node (cap_span_node node height span).2,markWord,cap_span_height node height span]
  cases capIsMarked groups node height <;> decide

end CommitGolfCandidate.Chained.Native

end

section

/-! Installed stackless footer descent and root/parent/sibling control edges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem merged_ChainedCheckerFooterControl_control_pc_set (s : MachineState) (target : Word) : (s.setPC target).pc=target := rfl
@[local simp] private theorem merged_ChainedCheckerFooterControl_control_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem merged_ChainedCheckerFooterControl_control_set_zero (s : MachineState) (value : Word) : s.setReg .x0 value=s := rfl
@[local simp] private theorem merged_ChainedCheckerFooterControl_control_sign_one : signExtend12 1#12=1#64 := rfl

def checkerFooterKnownOps : List Instr := [.BGEU .x30 .x29 40,.SLLI .x30 .x30 1,.JAL .x0 2097128]
@[irreducible] def checkerFooterKnownPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFooterKnownOps.take n).foldl execInstrBr s
@[irreducible] def checkerFooterDecisionPrefix (s : MachineState) (n : Nat) : MachineState := footerDecisionPrefix s n
@[irreducible] def checkerFooterParentPrefix (s : MachineState) (n : Nat) : MachineState := footerParentPrefix s n
def checkerFooterSiblingOps : List Instr := [.ADDI .x30 .x30 1,.JAL .x0 2097068]
@[irreducible] def checkerFooterSiblingPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFooterSiblingOps.take n).foldl execInstrBr s

theorem checker_footer_known_at : OpsAt chainedCheckerImage (4096+4*2172) checkerFooterKnownOps :=
  chained_checker_slice_at 2172 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_decision_at : OpsAt chainedCheckerImage (4096+4*2182) footerDecisionOps :=
  chained_checker_slice_at 2182 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_parent_at : OpsAt chainedCheckerImage (4096+4*2186) footerParentOps :=
  chained_checker_slice_at 2186 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_sibling_at : OpsAt chainedCheckerImage (4096+4*2188) checkerFooterSiblingOps :=
  chained_checker_slice_at 2188 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_footer_known_zero (s : MachineState) : checkerFooterKnownPrefix s 0=s := by
  rw [checkerFooterKnownPrefix]; rfl
theorem checker_footer_known_succ (s : MachineState) (n : Nat) (small : n<3) :
    checkerFooterKnownPrefix s (n+1)=execInstrBr (checkerFooterKnownPrefix s n) (checkerFooterKnownOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerFooterKnownPrefix <;> rfl
theorem checker_footer_prune_pc (s : MachineState) (pc : s.pc=4096+4*2172) (leaf : ¬footerWide s) :
    (checkerFooterKnownPrefix s 1).pc=4096+4*2182 := by
  change ¬BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at leaf
  simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,pc,leaf,signExtend13]
theorem checker_footer_prune_register (s : MachineState) (reg : Reg) :
    (checkerFooterKnownPrefix s 1).getReg reg=s.getReg reg := by
  by_cases internal : footerWide s
  · have same : checkerFooterKnownPrefix s 1=s.setPC (s.pc+4) := by
      rw [checkerFooterKnownPrefix]
      exact ite_eq_right (by simpa [footerWide] using internal)
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : checkerFooterKnownPrefix s 1=s.setPC (s.pc+40) := by
      rw [checkerFooterKnownPrefix]
      exact ite_eq_left internal
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
theorem checker_footer_prune_memory (s : MachineState) (query : Word) :
    (checkerFooterKnownPrefix s 1).getMem query=s.getMem query := by
  by_cases internal : footerWide s
  · have same : checkerFooterKnownPrefix s 1=s.setPC (s.pc+4) := by
      rw [checkerFooterKnownPrefix]
      exact ite_eq_right (by simpa [footerWide] using internal)
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : checkerFooterKnownPrefix s 1=s.setPC (s.pc+40) := by
      rw [checkerFooterKnownPrefix]
      exact ite_eq_left internal
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
theorem checker_footer_prune_byte (s : MachineState) (query : Word) :
    (checkerFooterKnownPrefix s 1).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_prune_memory]
theorem checker_footer_prune_execution (s : MachineState) (pc : s.pc=4096+4*2172) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (1+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterKnownPrefix s 1) coins
          return result.charge 1 0) := by
  rw [checking_manifest_image]
  have fetched : fetch chainedCheckerImage s=some (.base (.BGEU .x30 .x29 40)) :=
    checker_footer_known_at 0 (by decide) _ (by simpa using pc)
  have ordinary : ordinaryStep s (.base (.BGEU .x30 .x29 40))=some (checkerFooterKnownPrefix s 1) := by
    rw [checkerFooterKnownPrefix]; rfl
  simpa only [Nat.add_comm,instructionCycles] using
    execute_ordinary_step chainedCheckerImage _ s _ fuel coins fetched ordinary

theorem checker_footer_descend_pc (s : MachineState) (pc : s.pc=4096+4*2172) (internal : footerWide s) :
    (checkerFooterKnownPrefix s 3).pc=4096+4*2168 := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,pc,internal,signExtend21]
theorem checker_footer_descend_node (s : MachineState) (internal : footerWide s) :
    (checkerFooterKnownPrefix s 3).getReg .x30=s.getReg .x30<<<1 := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,internal]
theorem checker_footer_descend_register (s : MachineState) (internal : footerWide s) (reg : Reg) (kept : reg≠.x30) :
    (checkerFooterKnownPrefix s 3).getReg reg=s.getReg reg := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,internal,Ne.symm kept]
theorem checker_footer_descend_memory (s : MachineState) (internal : footerWide s) (query : Word) :
    (checkerFooterKnownPrefix s 3).getMem query=s.getMem query := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,internal]
theorem checker_footer_descend_byte (s : MachineState) (internal : footerWide s) (query : Word) :
    (checkerFooterKnownPrefix s 3).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_descend_memory s internal]
theorem checker_footer_descend_execution (s : MachineState) (pc : s.pc=4096+4*2172) (internal : footerWide s)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (3+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterKnownPrefix s 3) coins
          return result.charge 3 0) := by
  rw [checking_manifest_image]
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  conv_lhs => rw [←checker_footer_known_zero s]
  apply execute_unit_steps (states := checkerFooterKnownPrefix s)
  intro i inside
  refine ⟨.base (checkerFooterKnownOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_known_at i inside
    interval_cases i <;> simp [checkerFooterKnownPrefix,checkerFooterKnownOps,execInstrBr,pc,internal]
  · rw [checker_footer_known_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_footer_decision_pc (s : MachineState) (pc : s.pc=4096+4*2182) (notRoot : s.getReg .x30≠1#64) :
    (checkerFooterDecisionPrefix s 4).pc=if s.getReg .x30&&&1#64=0#64 then 4096+4*2188 else 4096+4*2186 := by
  by_cases even : s.getReg .x30&&&1#64=0#64 <;>
    simp [checkerFooterDecisionPrefix,footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,notRoot,even,signExtend12,signExtend13]
theorem checker_footer_decision_register (s : MachineState) (reg : Reg) (kept : reg≠.x31) :
    (checkerFooterDecisionPrefix s 4).getReg reg=s.getReg reg := by
  rw [checkerFooterDecisionPrefix,footer_decision_register s reg kept]
theorem checker_footer_decision_memory (s : MachineState) (query : Word) :
    (checkerFooterDecisionPrefix s 4).getMem query=s.getMem query := by
  rw [checkerFooterDecisionPrefix,footer_decision_memory]
theorem checker_footer_decision_byte (s : MachineState) (query : Word) :
    (checkerFooterDecisionPrefix s 4).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_decision_memory]
theorem checker_footer_decision_execution (s : MachineState) (pc : s.pc=4096+4*2182) (notRoot : s.getReg .x30≠1#64)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterDecisionPrefix s 4) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image,checkerFooterDecisionPrefix]
  apply execute_unit_steps (states := footerDecisionPrefix s)
  intro i inside
  refine ⟨.base (footerDecisionOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_decision_at i inside
    interval_cases i <;> simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,notRoot]
  · have step : footerDecisionPrefix s (i+1)=execInstrBr (footerDecisionPrefix s i) (footerDecisionOps.getD i .EBREAK) := by
      interval_cases i <;> rfl
    rw [step]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_footer_parent_pc (s : MachineState) (pc : s.pc=4096+4*2186) :
    (checkerFooterParentPrefix s 2).pc=4096+4*2182 := by
  simp [checkerFooterParentPrefix,footerParentPrefix,footerParentOps,execInstrBr,pc,signExtend21]
theorem checker_footer_parent_node (s : MachineState) :
    (checkerFooterParentPrefix s 2).getReg .x30=s.getReg .x30>>>1 := by
  rw [checkerFooterParentPrefix,footer_parent_node]
theorem checker_footer_parent_register (s : MachineState) (reg : Reg) (kept : reg≠.x30) :
    (checkerFooterParentPrefix s 2).getReg reg=s.getReg reg := by
  rw [checkerFooterParentPrefix,footer_parent_register s reg kept]
theorem checker_footer_parent_memory (s : MachineState) (query : Word) :
    (checkerFooterParentPrefix s 2).getMem query=s.getMem query := by
  rw [checkerFooterParentPrefix,footer_parent_memory]
theorem checker_footer_parent_byte (s : MachineState) (query : Word) :
    (checkerFooterParentPrefix s 2).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_parent_memory]
theorem checker_footer_parent_execution (s : MachineState) (pc : s.pc=4096+4*2186) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterParentPrefix s 2) coins
          return result.charge 2 0) := by
  rw [checking_manifest_image,checkerFooterParentPrefix]
  apply execute_unit_steps (states := footerParentPrefix s)
  intro i inside
  refine ⟨.base (footerParentOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_parent_at i inside
    interval_cases i <;> simp [footerParentPrefix,footerParentOps,execInstrBr,pc]
  · have step : footerParentPrefix s (i+1)=execInstrBr (footerParentPrefix s i) (footerParentOps.getD i .EBREAK) := by
      interval_cases i <;> rfl
    rw [step]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_footer_sibling_pc (s : MachineState) (pc : s.pc=4096+4*2188) :
    (checkerFooterSiblingPrefix s 2).pc=4096+4*2168 := by
  simp [checkerFooterSiblingPrefix,checkerFooterSiblingOps,execInstrBr,pc,signExtend21]
theorem checker_footer_sibling_node (s : MachineState) :
    (checkerFooterSiblingPrefix s 2).getReg .x30=s.getReg .x30+1 := by
  simp [checkerFooterSiblingPrefix,checkerFooterSiblingOps,execInstrBr]
theorem checker_footer_sibling_register (s : MachineState) (reg : Reg) (kept : reg≠.x30) :
    (checkerFooterSiblingPrefix s 2).getReg reg=s.getReg reg := by
  simp [checkerFooterSiblingPrefix,checkerFooterSiblingOps,execInstrBr,Ne.symm kept]
theorem checker_footer_sibling_memory (s : MachineState) (query : Word) :
    (checkerFooterSiblingPrefix s 2).getMem query=s.getMem query := by
  simp [checkerFooterSiblingPrefix,checkerFooterSiblingOps,execInstrBr]
theorem checker_footer_sibling_byte (s : MachineState) (query : Word) :
    (checkerFooterSiblingPrefix s 2).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_sibling_memory]
theorem checker_footer_sibling_execution (s : MachineState) (pc : s.pc=4096+4*2188) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterSiblingPrefix s 2) coins
          return result.charge 2 0) := by
  rw [checking_manifest_image]
  have zero : checkerFooterSiblingPrefix s 0=s := by rw [checkerFooterSiblingPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerFooterSiblingPrefix s)
  intro i inside
  refine ⟨.base (checkerFooterSiblingOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_sibling_at i inside
    interval_cases i <;> simp [checkerFooterSiblingPrefix,checkerFooterSiblingOps,execInstrBr,pc]
  · have step : checkerFooterSiblingPrefix s (i+1)=execInstrBr (checkerFooterSiblingPrefix s i) (checkerFooterSiblingOps.getD i .EBREAK) := by
      interval_cases i <;> unfold checkerFooterSiblingPrefix <;> rfl
    rw [step]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_footer_root_pc (s : MachineState) (pc : s.pc=4096+4*2182) (root : s.getReg .x30=1#64) :
    (checkerFooterDecisionPrefix s 2).pc=4096+4*2190 := by
  simp [checkerFooterDecisionPrefix,footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,root,signExtend12,signExtend13]
theorem checker_footer_root_register (s : MachineState) (root : s.getReg .x30=1#64) (reg : Reg) (kept : reg≠.x31) :
    (checkerFooterDecisionPrefix s 2).getReg reg=s.getReg reg := by
  rw [checkerFooterDecisionPrefix,footer_root_register s root reg kept]
theorem checker_footer_root_memory (s : MachineState) (root : s.getReg .x30=1#64) (query : Word) :
    (checkerFooterDecisionPrefix s 2).getMem query=s.getMem query := by
  rw [checkerFooterDecisionPrefix,footer_root_memory s root query]
theorem checker_footer_root_byte (s : MachineState) (root : s.getReg .x30=1#64) (query : Word) :
    (checkerFooterDecisionPrefix s 2).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_root_memory s root]
theorem checker_footer_root_execution (s : MachineState) (pc : s.pc=4096+4*2182) (_root : s.getReg .x30=1#64)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterDecisionPrefix s 2) coins
          return result.charge 2 0) := by
  rw [checking_manifest_image,checkerFooterDecisionPrefix]
  apply execute_unit_steps (states := footerDecisionPrefix s)
  intro i inside
  refine ⟨.base (footerDecisionOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_decision_at i (by change i<4; omega)
    interval_cases i <;> simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc]
  · have step : footerDecisionPrefix s (i+1)=execInstrBr (footerDecisionPrefix s i) (footerDecisionOps.getD i .EBREAK) := by
      interval_cases i <;> rfl
    rw [step]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native

end
