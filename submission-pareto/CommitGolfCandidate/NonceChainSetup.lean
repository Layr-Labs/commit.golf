import CommitGolfCandidate.NonceChainExec

/-! The seed draw, jumps, and preserved ABI registers of the expansion prelude. -/
namespace TwoPermutationPrototype.RV64.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 60000
set_option maxHeartbeats 620000
attribute [local irreducible] execute packedWideCommitImage chainRun

def seedOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 4056,.LUI .x19 131072,
   .ADD .x20 .x9 .x19,.ADD .x21 .x20 .x19,.LUI .x22 327680,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 (-176),.ADDI .x11 .x0 24]
def startOps : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.JAL .x0 932572,
    .ADDI .x12 .x22 0,.LUI .x7 65538,.ADDI .x7 .x7 0,.ADD .x7 .x7 .x22]
def finishOps : List Instr :=
  [.ADDI .x10 .x18 0,.JAL .x0 1163792,.SLLI .x7 .x13 11,.ADD .x22 .x22 .x7,
    .SLLI .x7 .x7 1,.ADDI .x0 .x0 0,.ADDI .x0 .x0 0,.ADDI .x10 .x10 40]

def seedSetup (s : MachineState) := seedOps.foldl execInstrBr s
def seedWritten (s : MachineState) (k : BitVec 192) :=
  writeBits (seedSetup s) (BitVec.ofNat 64 (nonceChainSource 0)) k
def chainInitial (s : MachineState) (k : BitVec 192) := startOps.foldl execInstrBr (seedWritten s k)
def chainFinish (s : MachineState) := finishOps.foldl execInstrBr s

structure Saved (s : MachineState) : Prop where
  root : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  source : s.getReg .x18=wordAddress (leafStart 0)
  stride : s.getReg .x19=536870912
  slots : s.getReg .x20=wordAddress (leafDest 0)
  stop : s.getReg .x21=wordAddress (leafDest (2^24))
  salts : s.getReg .x22=wordAddress (leafSalt 0)

structure BodyRegs (s : MachineState) : Prop where
  root : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  source : s.getReg .x18=wordAddress (leafStart 0)
  stride : s.getReg .x19=536870912
  slots : s.getReg .x20=wordAddress (leafDest 0)
  stop : s.getReg .x21=wordAddress (leafDest (2^24))
  salts : s.getReg .x22=wordAddress (leafSalt 0)+2048
  pc : s.pc=4184
  ready : ChainPermReady s
  cursor : s.getReg .x10=wordAddress (leafStart 0+5)
  step : s.getReg .x7=4096

private theorem seed_last_two (s : MachineState) : seedSetup s =
    execInstrBr (execInstrBr (initialPrefix s 9) (.ADDI .x10 .x22 (-176))) (.ADDI .x11 .x0 24) := by
  simp only [seedSetup,seedOps,initialPrefix,initialInstructions,List.take,List.foldl]

private theorem prior_last_two (s : MachineState) : initialPrefix s 11 =
    execInstrBr (execInstrBr (initialPrefix s 9) (.ADDI .x10 .x22 0)) (.LUI .x11 65536) := by
  simp only [initialPrefix,initialInstructions,List.take,List.foldl]

attribute [local irreducible] initialPrefix seedSetup

private theorem common_setup_reg (s : MachineState) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x11) :
    (seedSetup s).getReg r = (initialPrefix s 11).getReg r := by
  rw [seed_last_two,prior_last_two]
  simp only [execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ a.symm,MachineState.getReg_setReg_ne _ _ _ _ b.symm]

private theorem two_word_source (u : MachineState) :
    (execInstrBr (execInstrBr u (.ADDI .x10 .x22 (-176))) (.ADDI .x11 .x0 24)).getReg .x10 =
      (execInstrBr (execInstrBr u (.ADDI .x10 .x22 0)) (.LUI .x11 65536)).getReg .x22 +
        signExtend12 3920 := by
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ .x11 .x10 _ (by decide),
    MachineState.getReg_setReg_ne _ .x11 .x22 _ (by decide),
    MachineState.getReg_setReg_ne _ .x10 .x22 _ (by decide),
    MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
  rfl

private theorem saved_source (s : MachineState) :
    (seedSetup s).getReg .x10 = (initialPrefix s 11).getReg .x22 + signExtend12 3920 :=
  (congrArg (fun u : MachineState => u.getReg .x10) (seed_last_two s)).trans
    ((two_word_source (initialPrefix s 9)).trans
      (congrArg (fun u : MachineState => u.getReg .x22 + signExtend12 3920) (prior_last_two s).symm))

private theorem saved_pc (s : MachineState) (atEntry : s.pc=4096) : (seedSetup s).pc=4140 := by
  simp only [seedSetup,seedOps,List.foldl,execInstrBr,MachineState.setPC,atEntry]
  rfl

private theorem saved_width (s : MachineState) : (seedSetup s).getReg .x11 = 24 := by
  rw [seed_last_two]
  rfl

private theorem seed_delta : wordAddress (leafSalt 0) + signExtend12 3920 =
    BitVec.ofNat 64 (nonceChainSource 0) := by decide

private theorem setup_regs (s : MachineState) (e : CommitEntry s) :
    (seedSetup s).pc=4140 ∧ (seedSetup s).getReg .x5=2 ∧
    (seedSetup s).getReg .x10=BitVec.ofNat 64 (nonceChainSource 0) ∧
    (seedSetup s).getReg .x11=24 ∧ Saved (seedSetup s) := by
  have r := setup_registers s e
  have keep (reg : Reg) (ha : reg ≠ .x10 := by decide) (hb : reg ≠ .x11 := by decide) :=
    common_setup_reg s reg ha hb
  have offset := congrArg (fun x : Word => x + signExtend12 3920) r.salts
  exact ⟨saved_pc s e.pc,(keep .x5).trans r.selector,
    (saved_source s).trans (offset.trans seed_delta),saved_width s,
    ⟨(keep .x8).trans r.out,(keep .x9).trans r.heap,(keep .x18).trans r.source,
      (keep .x19).trans r.stride,(keep .x20).trans r.leaves,(keep .x21).trans r.stop,(keep .x22).trans r.salts⟩⟩

private theorem after_seed (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    (seedWritten s k).pc=4144 := by
  rw [seedWritten,written_pc,(setup_regs s e).1]
  rfl

private theorem start_regs (s : MachineState) (pc : s.pc=4144) :
    (startOps.foldl execInstrBr s).pc=936744 ∧ ChainPermReady (startOps.foldl execInstrBr s) ∧
    (startOps.foldl execInstrBr s).getReg .x10=s.getReg .x10 ∧
    (startOps.foldl execInstrBr s).getReg .x12=s.getReg .x22 ∧
    (startOps.foldl execInstrBr s).getReg .x7=268443648+s.getReg .x22 := by
  refine ⟨?_,⟨rfl,rfl,rfl⟩,rfl,?_,rfl⟩
  · change s.pc+4+4+4+signExtend21 932572+4+4+4+4=_
    rw [pc]
    rfl
  · exact BitVec.add_zero _

private theorem start_saved (s : MachineState) (h : Saved s) : Saved (startOps.foldl execInstrBr s) :=
  ⟨h.root,h.heap,h.source,h.stride,h.slots,h.stop,h.salts⟩

theorem initial_frame (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    NonceChainFrame (chainInitial s k) 0 ∧ Saved (chainInitial s k) := by
  obtain ⟨_,_,src,_,saved⟩ := setup_regs s e
  have keep (r : Reg) : (seedWritten s k).getReg r = (seedSetup s).getReg r := writeBits_register ..
  obtain ⟨pc,ready,input,output,limit⟩ := start_regs _ (after_seed s e k)
  rw [keep,src] at input
  rw [keep,saved.salts] at output limit
  refine ⟨⟨pc,ready,input,output,limit⟩,?_⟩
  have saved' : Saved (seedWritten s k) := by
    exact ⟨(keep _).trans saved.root,(keep _).trans saved.heap,(keep _).trans saved.source,
      (keep _).trans saved.stride,(keep _).trans saved.slots,(keep _).trans saved.stop,(keep _).trans saved.salts⟩
  exact start_saved _ saved'

theorem advance_saved (s : MachineState) (j : Nat) (y : BitVec 1600) (h : Saved s) : Saved (chainAdvance s j y) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  exact ⟨(keep .x8).trans h.root,(keep .x9).trans h.heap,(keep .x18).trans h.source,
    (keep .x19).trans h.stride,(keep .x20).trans h.slots,(keep .x21).trans h.stop,(keep .x22).trans h.salts⟩

theorem run_frame (j n : Nat) (s : MachineState) (frame : NonceChainFrame s j) (base : Saved s)
    (last : MachineState) (hit : last ∈ support (chainRun j s n)) :
    NonceChainFrame last (j+n) ∧ Saved last := by
  induction n generalizing j s with
  | zero =>
    simp only [chainRun,support_pure,Set.mem_singleton_iff] at hit
    simpa [hit] using And.intro frame base
  | succ n ih =>
    simp only [chainRun,mem_support_bind_iff] at hit
    obtain ⟨y,_,tail⟩ := hit
    simpa only [show j+(n+1)=(j+1)+n by omega] using
      ih (j+1) _ (chain_advance_frame s j y frame) (advance_saved s j y base) tail

private theorem final_stride (s : MachineState) (sel : s.getReg .x13=1) : (chainFinish s).getReg .x7 = 4096 := by
  change ((s.getReg .x13 <<< (11 : Nat)) <<< (1 : Nat)) = _
  rw [sel]
  rfl

private theorem final_salts (s : MachineState) (base : s.getReg .x22=wordAddress (leafSalt 0))
    (sel : s.getReg .x13=1) : (chainFinish s).getReg .x22=wordAddress (leafSalt 0)+2048 := by
  change s.getReg .x22+(s.getReg .x13 <<< (11 : Nat))=_
  rw [base,sel]
  rfl

theorem finish_regs (s : MachineState) (frame : NonceChainFrame s nonceChainCount) (h : Saved s) :
    BodyRegs (chainFinish s) := by
  have pc : s.pc=937516 := frame.pc
  refine ⟨h.root,h.heap,h.source,h.stride,h.slots,h.stop,final_salts s h.salts frame.ready.2.2,?_,frame.ready,?_,
    final_stride s frame.ready.2.2⟩
  · change s.pc+4+signExtend21 1163792+4+4+4+4+4+4=_
    rw [pc]
    rfl
  · change (s.getReg .x18+0)+40=_
    rw [h.source]
    rfl


theorem seed_run (s : MachineState) (pc : s.pc=4096) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) s true =
      (do let result ← execute packedWideCommitImage fuel (seedSetup s) true
          return result.charge 11 0) := by
  unfold seedSetup
  apply execute_unit_steps (states := fun i => (seedOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((seedOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply packed_wide_fetch_decoded _ (i) (by omega)
    · interval_cases i <;>
        simp only [seedOps,initialInstructions,List.take,List.append,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem start_run (s : MachineState) (pc : s.pc=4144) (fuel : Nat) :
    execute packedWideCommitImage (8+fuel) s true =
      (do let result ← execute packedWideCommitImage fuel (startOps.foldl execInstrBr s) true
          return result.charge 8 0) := by
  apply execute_unit_steps (states := fun i => (startOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((startOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply packed_wide_fetch_decoded _ (if i<4 then 12+i else 233158+(i-4)) (by split <;> omega)
    · interval_cases i <;>
        simp only [startOps,initialInstructions,List.take,List.append,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem finish_run (s : MachineState) (pc : s.pc=937516) (fuel : Nat) :
    execute packedWideCommitImage (8+fuel) s true =
      (do let result ← execute packedWideCommitImage fuel (finishOps.foldl execInstrBr s) true
          return result.charge 8 0) := by
  apply execute_unit_steps (states := fun i => (finishOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((finishOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply packed_wide_fetch_decoded _ (if i<2 then 233355+i else 16+(i-2)) (by split <;> omega)
    · interval_cases i <;>
        simp only [finishOps,initialInstructions,List.take,List.append,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
theorem seed_draw (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) (seedSetup s) true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute packedWideCommitImage fuel (seedWritten s k) true
          return result.charge 4 0) := by
  obtain ⟨pc,selector,src,width,_⟩ := setup_regs s e
  have fetched := packed_wide_fetch_decoded (seedSetup s) 11 (by decide) pc .ECALL (by decide +kernel)
  have valid : randomArgumentsValid (seedSetup s) = true := by rw [randomArgumentsValid,src,width];decide
  have raw :
      execute packedWideCommitImage (1+fuel) (seedSetup s) true =
        (do let k ← liftM ($ᵗ BitVec (8*((seedSetup s).getReg .x11).toNat) :
              ProbComp (BitVec (8*((seedSetup s).getReg .x11).toNat)))
            let result ← execute packedWideCommitImage fuel
              (writeBits (seedSetup s) ((seedSetup s).getReg .x10) k) true
            return result.charge (1+(((seedSetup s).getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 fuel,execute,fetched]
    simp only [selector,valid]
    rfl
  rw [width,src] at raw
  exact raw

def expansion (s : MachineState) (k : BitVec 192) : OracleComp World MachineState :=
  chainRun 0 (chainInitial s k) nonceChainCount

theorem expansion_post (s : MachineState) (e : CommitEntry s) (k : BitVec 192)
    (last : MachineState) (hit : last ∈ support (expansion s k)) :
    last.pc=937516 ∧ BodyRegs (chainFinish last) := by
  obtain ⟨frame,saved⟩ := initial_frame s e k
  obtain ⟨tail,kept⟩ := run_frame 0 nonceChainCount _ frame saved last hit
  exact ⟨tail.pc,finish_regs last tail kept⟩

theorem after_draw (s : MachineState) (e : CommitEntry s) (k : BitVec 192) (fuel : Nat) :
    execute packedWideCommitImage (4599592+fuel) (seedWritten s k) true =
      (do let last ← expansion s k
          let result ← execute packedWideCommitImage fuel (chainFinish last) true
          return result.charge 15276328 nonceChainCount) := by
  have start := start_run _ (after_seed s e k) ((nonceChainSteps nonceChainCount)+(8+fuel))
  have loop := nonce_chain_run (chainInitial s k) 0 nonceChainCount (by decide) (initial_frame s e k).1 (8+fuel)
  rw [show 4599592+fuel = 8+(nonceChainSteps nonceChainCount+(8+fuel)) by unfold nonceChainSteps nonceChainCount;omega,start]
  change (execute packedWideCommitImage (nonceChainSteps nonceChainCount+(8+fuel)) (chainInitial s k) true >>= _) = _
  rw [show nonceChainSteps nonceChainCount+(8+fuel) =
    nonceChainSteps (0+nonceChainCount)-nonceChainSteps 0+(8+fuel) by simp only [Nat.zero_add,nonceChainSteps,Nat.mul_zero,Nat.zero_div,Nat.add_zero,Nat.sub_zero],loop]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro last hit
  rw [finish_run _ (expansion_post s e k _ hit).1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro result
  simp only [Execution.charge]
  have rate : nonceChainCycles (0+nonceChainCount)-nonceChainCycles 0 = 15276312 := by decide
  rw [rate]
  congr 2 <;> omega

end TwoPermutationPrototype.RV64.Chain
