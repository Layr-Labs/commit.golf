import CommitGolfCandidate.QuartetChainExec
import CommitGolfCandidate.QuartetCommitSetup

/-! Adapted from submission c28dd9ca (dadon), `NonceChainSetup`, for the Quartet commitment:
the 24-byte seed draw at word 15 (written at `T`), words 16-21 ending in the jump to the
generator, its four-instruction head, and the return to the leaf loop at word 22. -/
namespace TwoPermutationPrototype.QuartetChain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 (wordAddress Manifest.decodeBase CommitEntry written_pc)
open TwoPermutationPrototype.RV64.Chain (chainPermInput chainPermReply ChainPermReady)
open TwoPermutationPrototype.QuartetCommit (image codeWord fetch_decoded wordPC prePrefix pre_run postPrefix
  post_run SeedRegs seed_registers StartLeafRegs fetch_setup setupOps qSalt qSource)
set_option maxRecDepth 60000
set_option maxHeartbeats 620000
attribute [local irreducible] execute image chainRun

def headOps : List Instr := [.ADDI .x12 .x24 0, .LUI .x7 65536, .ADD .x7 .x7 .x24, .JAL .x0 107984]
def finishOps : List Instr := [.ADDI .x10 .x18 0, .JAL .x0 1063772]

def seedWritten (s : MachineState) (k : BitVec 192) :=
  writeBits (prePrefix s 15) (BitVec.ofNat 64 (nonceChainSource 0)) k
def chainInitial (s : MachineState) (k : BitVec 192) :=
  headOps.foldl execInstrBr (postPrefix (seedWritten s k) 6)
def chainFinish (s : MachineState) := finishOps.foldl execInstrBr s

/-- Registers the generator never writes, with the values the leaf loop expects. -/
structure Saved (s : MachineState) : Prop where
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  salt : s.getReg .x22=wordAddress (qSalt 0)+2048
  bigStride : s.getReg .x23=4096
  sentinel : s.getReg .x25=wordAddress (qSource 4194304)+2048
  quartet : s.getReg .x21=wordAddress (qSource 0)
  stop : s.getReg .x24=wordAddress (qSource 4194304)
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  stride : s.getReg .x19=536870912
  message : s.getReg .x18=4096

private theorem seed_target : (BitVec.ofNat 64 (8*qSalt 0) : Word) = BitVec.ofNat 64 (nonceChainSource 0) := by
  decide

theorem seed_draw (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (1+fuel) (prePrefix s 15) true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (seedWritten s k) true
          return result.charge 4 0) := by
  have r := seed_registers s e
  have fetched : fetch image (prePrefix s 15) = some (.base .ECALL) := fetch_setup _ ⟨15, by decide⟩ r.pc
  have src : (prePrefix s 15).getReg .x10 = BitVec.ofNat 64 (nonceChainSource 0) := r.target.trans seed_target
  have valid : randomArgumentsValid (prePrefix s 15) = true := by rw [randomArgumentsValid,src,r.size]; decide
  have raw :
      execute image (1+fuel) (prePrefix s 15) true =
        (do let k ← liftM ($ᵗ BitVec (8*((prePrefix s 15).getReg .x11).toNat) :
              ProbComp (BitVec (8*((prePrefix s 15).getReg .x11).toNat)))
            let result ← execute image fuel
              (writeBits (prePrefix s 15) ((prePrefix s 15).getReg .x10) k) true
            return result.charge (1+(((prePrefix s 15).getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 fuel,execute,fetched]
    simp only [r.selector,valid]
    rfl
  rw [r.size,src] at raw
  exact raw

private theorem seed_written_pc (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    (seedWritten s k).pc = wordPC 16 := by
  rw [seedWritten,written_pc,(seed_registers s e).pc]
  rfl

theorem head_run (s : MachineState) (pc : s.pc=wordPC 178360) (fuel : Nat) :
    execute image (4+fuel) s true =
      (do let result ← execute image fuel (headOps.foldl execInstrBr s) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (headOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((headOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetch_decoded _ (178360+i) (by omega)
    · interval_cases i <;>
        simp only [headOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc,wordPC] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem start_run (s : MachineState) (e : CommitEntry s) (k : BitVec 192) (fuel : Nat) :
    execute image (10+fuel) (seedWritten s k) true =
      (do let result ← execute image fuel (chainInitial s k) true
          return result.charge 10 0) := by
  rw [show 10+fuel = 6+(4+fuel) by omega, post_run _ (seed_written_pc s e k)]
  have jumped : (postPrefix (seedWritten s k) 6).pc = wordPC 178360 := by
    change (seedWritten s k).pc+4+4+4+4+4+signExtend21 713356=_
    rw [seed_written_pc s e k]
    rfl
  rw [head_run _ jumped]
  simp only [bind_assoc,pure_bind,chainInitial]
  apply bind_congr
  intro r
  simp only [Execution.charge]
  congr 2 <;> omega

theorem finish_run (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*258366)) (fuel : Nat) :
    execute image (2+fuel) s true =
      (do let result ← execute image fuel (chainFinish s) true
          return result.charge 2 0) := by
  apply execute_unit_steps (states := fun i => (finishOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((finishOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetch_decoded _ (258366+i) (by omega)
    · interval_cases i <;>
        simp only [finishOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### Registers -/

attribute [local irreducible] seedWritten writeBits

private theorem write_reg (s : MachineState) (k : BitVec 192) (r : Reg) :
    (seedWritten s k).getReg r = (prePrefix s 15).getReg r := by
  rw [seedWritten]
  exact writeBits_register ..

private theorem through (s : MachineState) (k : BitVec 192) (r : Reg)
    (h : (chainInitial s k).getReg r = (seedWritten s k).getReg r) :
    (chainInitial s k).getReg r = (prePrefix s 15).getReg r := h.trans (write_reg s k r)

private theorem post_x20 (u : MachineState) : (postPrefix u 6).getReg .x20 = u.getReg .x20 := rfl
private theorem head_x20 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x20 = v.getReg .x20 := rfl
private theorem init_x20 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x20 = (seedWritten s k).getReg .x20 :=
  (head_x20 _).trans (post_x20 _)
private theorem post_x23 (u : MachineState) : (postPrefix u 6).getReg .x23 = u.getReg .x23 := rfl
private theorem head_x23 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x23 = v.getReg .x23 := rfl
private theorem init_x23 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x23 = (seedWritten s k).getReg .x23 :=
  (head_x23 _).trans (post_x23 _)
private theorem post_x21 (u : MachineState) : (postPrefix u 6).getReg .x21 = u.getReg .x21 := rfl
private theorem head_x21 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x21 = v.getReg .x21 := rfl
private theorem init_x21 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x21 = (seedWritten s k).getReg .x21 :=
  (head_x21 _).trans (post_x21 _)
private theorem post_x24 (u : MachineState) : (postPrefix u 6).getReg .x24 = u.getReg .x24 := rfl
private theorem head_x24 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x24 = v.getReg .x24 := rfl
private theorem init_x24 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x24 = (seedWritten s k).getReg .x24 :=
  (head_x24 _).trans (post_x24 _)
private theorem post_x8 (u : MachineState) : (postPrefix u 6).getReg .x8 = u.getReg .x8 := rfl
private theorem head_x8 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x8 = v.getReg .x8 := rfl
private theorem init_x8 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x8 = (seedWritten s k).getReg .x8 :=
  (head_x8 _).trans (post_x8 _)
private theorem post_x9 (u : MachineState) : (postPrefix u 6).getReg .x9 = u.getReg .x9 := rfl
private theorem head_x9 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x9 = v.getReg .x9 := rfl
private theorem init_x9 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x9 = (seedWritten s k).getReg .x9 :=
  (head_x9 _).trans (post_x9 _)
private theorem post_x19 (u : MachineState) : (postPrefix u 6).getReg .x19 = u.getReg .x19 := rfl
private theorem head_x19 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x19 = v.getReg .x19 := rfl
private theorem init_x19 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x19 = (seedWritten s k).getReg .x19 :=
  (head_x19 _).trans (post_x19 _)
private theorem post_x18 (u : MachineState) : (postPrefix u 6).getReg .x18 = u.getReg .x18 := rfl
private theorem head_x18 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x18 = v.getReg .x18 := rfl
private theorem init_x18 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x18 = (seedWritten s k).getReg .x18 :=
  (head_x18 _).trans (post_x18 _)
private theorem post_x10 (u : MachineState) : (postPrefix u 6).getReg .x10 = u.getReg .x10 := rfl
private theorem head_x10 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x10 = v.getReg .x10 := rfl
private theorem init_x10 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x10 = (seedWritten s k).getReg .x10 :=
  (head_x10 _).trans (post_x10 _)
private theorem post_x22 (u : MachineState) : (postPrefix u 6).getReg .x22 = u.getReg .x22 + u.getReg .x7 := rfl
private theorem head_x22 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x22 = v.getReg .x22 := rfl
private theorem post_x7 (u : MachineState) : (postPrefix u 6).getReg .x7 = u.getReg .x7 := rfl
private theorem init_x22 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x22 = (seedWritten s k).getReg .x22 + (seedWritten s k).getReg .x7 :=
  (head_x22 _).trans (post_x22 _)
private theorem post_x25 (u : MachineState) : (postPrefix u 6).getReg .x25 = u.getReg .x24 + u.getReg .x7 := rfl
private theorem head_x25 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x25 = v.getReg .x25 := rfl
private theorem init_x25 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x25 = (seedWritten s k).getReg .x24 + (seedWritten s k).getReg .x7 :=
  (head_x25 _).trans (post_x25 _)
private theorem head_x12 (v : MachineState) : (headOps.foldl execInstrBr v).getReg .x12 = v.getReg .x24 + signExtend12 0 := rfl
private theorem init_x12 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x12 = (seedWritten s k).getReg .x24 + signExtend12 0 :=
  (head_x12 _).trans (congrArg (· + signExtend12 0) (post_x24 _))
private theorem head_x7 (v : MachineState) :
    (headOps.foldl execInstrBr v).getReg .x7 = BitVec.signExtend 64 ((65536#20).zeroExtend 32 <<< 12) + v.getReg .x24 := rfl
private theorem init_x7 (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).getReg .x7 = BitVec.signExtend 64 ((65536#20).zeroExtend 32 <<< 12) + (seedWritten s k).getReg .x24 :=
  (head_x7 _).trans (congrArg (BitVec.signExtend 64 ((65536#20).zeroExtend 32 <<< 12) + ·) (post_x24 _))
private theorem post_ready (u : MachineState) : ChainPermReady (postPrefix u 6) := ⟨rfl,rfl,rfl⟩
private theorem head_ready (v : MachineState) (h : ChainPermReady v) : ChainPermReady (headOps.foldl execInstrBr v) := h
private theorem post_pc (u : MachineState) : (postPrefix u 6).pc = u.pc+4+4+4+4+4+signExtend21 713356 := rfl
private theorem head_pc (v : MachineState) : (headOps.foldl execInstrBr v).pc = v.pc+4+4+4+signExtend21 107984 := rfl
private theorem init_ready (s : MachineState) (k : BitVec 192) : ChainPermReady (chainInitial s k) :=
  head_ready _ (post_ready _)
private theorem init_pc (s : MachineState) (k : BitVec 192) :
    (chainInitial s k).pc = (seedWritten s k).pc+4+4+4+4+4+signExtend21 713356+4+4+4+signExtend21 107984 := by
  rw [show chainInitial s k = headOps.foldl execInstrBr (postPrefix (seedWritten s k) 6) from rfl,head_pc,post_pc]
private theorem dest_zero (x : Word) (h : x = wordAddress (qSource 4194304)) :
    x + signExtend12 0 = BitVec.ofNat 64 (nonceChainDest 0) := by rw [h]; decide
private theorem dest_count (x : Word) (h : x = wordAddress (qSource 4194304)) :
    BitVec.signExtend 64 ((65536#20).zeroExtend 32 <<< 12) + x = BitVec.ofNat 64 chainLimit := by
  rw [h]; decide
private theorem start_pc (x : Word) (h : x = wordPC 16) :
    x+4+4+4+4+4+signExtend21 713356+4+4+4+signExtend21 107984 = BitVec.ofNat 64 (nonceChainPC 0) := by rw [h]; decide

theorem initial_frame (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    NonceChainFrame (chainInitial s k) 0 ∧ Saved (chainInitial s k) := by
  have r := seed_registers s e
  have w := write_reg s k
  refine ⟨⟨(init_pc s k).trans (start_pc _ (seed_written_pc s e k)),init_ready s k,
      (init_x10 s k).trans ((w .x10).trans (r.target.trans seed_target)),
      (init_x12 s k).trans (dest_zero _ ((w .x24).trans r.sentinel)),
      (init_x7 s k).trans (dest_count _ ((w .x24).trans r.sentinel))⟩,
    ⟨(init_x20 s k).trans ((w .x20).trans r.cursor),?_,(init_x23 s k).trans ((w .x23).trans r.bigStride),?_,
      (init_x21 s k).trans ((w .x21).trans r.quartet),(init_x24 s k).trans ((w .x24).trans r.sentinel),
      (init_x8 s k).trans ((w .x8).trans r.output),(init_x9 s k).trans ((w .x9).trans r.heap),
      (init_x19 s k).trans ((w .x19).trans r.stride),(init_x18 s k).trans ((w .x18).trans r.message)⟩⟩
  · rw [init_x22,w,w,r.salt,r.bias]
  · rw [init_x25,w,w,r.sentinel,r.bias]

theorem advance_saved (s : MachineState) (j : Nat) (y : BitVec 1600) (h : Saved s) : Saved (chainAdvance s j y) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  exact ⟨(keep .x20).trans h.cursor,(keep .x22).trans h.salt,(keep .x23).trans h.bigStride,
    (keep .x25).trans h.sentinel,(keep .x21).trans h.quartet,(keep .x24).trans h.stop,(keep .x8).trans h.output,
    (keep .x9).trans h.heap,(keep .x19).trans h.stride,(keep .x18).trans h.message⟩

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

theorem finish_regs (s : MachineState) (frame : NonceChainFrame s nonceChainCount) (h : Saved s) :
    StartLeafRegs (chainFinish s) := by
  have pc : s.pc=BitVec.ofNat 64 (4096+4*258366) := frame.pc
  have keep (r : Reg) (h : (chainFinish s).getReg r = s.getReg r := by rfl) : (chainFinish s).getReg r = s.getReg r := h
  refine ⟨?_,?_,(keep .x20).trans h.cursor,(keep .x22).trans h.salt,(keep .x23).trans h.bigStride,
    (keep .x5).trans frame.ready.1,(keep .x11).trans frame.ready.2.1,(keep .x13).trans frame.ready.2.2,
    (keep .x25).trans h.sentinel,(keep .x21).trans h.quartet,(keep .x24).trans h.stop,(keep .x8).trans h.output,
    (keep .x9).trans h.heap,(keep .x19).trans h.stride⟩
  · change s.pc+4+signExtend21 1063772=_
    rw [pc]
    rfl
  · change s.getReg .x18+signExtend12 0=_
    rw [h.message]
    rfl

def expansion (s : MachineState) (k : BitVec 192) : OracleComp World MachineState :=
  chainRun 0 (chainInitial s k) nonceChainCount

theorem expansion_post (s : MachineState) (e : CommitEntry s) (k : BitVec 192)
    (last : MachineState) (hit : last ∈ support (expansion s k)) :
    last.pc=BitVec.ofNat 64 (4096+4*258366) ∧ StartLeafRegs (chainFinish last) := by
  obtain ⟨frame,saved⟩ := initial_frame s e k
  obtain ⟨tail,kept⟩ := run_frame 0 nonceChainCount _ frame saved last hit
  exact ⟨tail.pc,finish_regs last tail kept⟩

theorem steps_total : nonceChainSteps nonceChainCount = 3813100 := by decide
theorem steps_zero : nonceChainSteps 0 = 0 := by decide

theorem after_draw (s : MachineState) (e : CommitEntry s) (k : BitVec 192) (fuel : Nat) :
    execute image (3813112+fuel) (seedWritten s k) true =
      (do let last ← expansion s k
          let result ← execute image fuel (chainFinish last) true
          return result.charge 14489526 nonceChainCount) := by
  have loop := nonce_chain_run (chainInitial s k) 0 nonceChainCount (by decide) (initial_frame s e k).1 (2+fuel)
  rw [show 3813112+fuel = 10+(nonceChainSteps nonceChainCount+(2+fuel)) by rw [steps_total]; omega,
    start_run s e k]
  rw [show nonceChainSteps nonceChainCount+(2+fuel) =
    nonceChainSteps (0+nonceChainCount)-nonceChainSteps 0+(2+fuel) by
      rw [Nat.zero_add,steps_zero,Nat.sub_zero],loop]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro last hit
  rw [finish_run _ (expansion_post s e k _ hit).1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro result
  simp only [Execution.charge]
  have rate : nonceChainCycles (0+nonceChainCount)-nonceChainCycles 0 = 14489514 := by decide
  rw [rate]
  congr 2 <;> omega

end TwoPermutationPrototype.QuartetChain
