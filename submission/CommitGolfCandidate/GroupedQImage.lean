import CommitGolfCandidate.GroupedUpperImage
import CommitGolfCandidate.GroupedQPost

/-!
# The setups, loops and root parent of the commit tail, on the delivered image

* level-21 setup (`x11 := 64; x13 := 0; x10 := s_{2^21-1}; x7 := s_{-1}; x12 := heap node 2^22-1`) → `L21Regs _ 2^21`;
* level-21 loop → `L21Regs _ 0`;
* heap setup and band glue (`sub x10,x12,x9; add x10,x10,x12`; `x7 := node 2^17-1`; `x6 := 0x3fff`)
  → `BandRegs _ (2^21-1) (2^17-1)`;
* band A (record parents) down to node `2^17`; `addi x7,x9,32` (`x7 := node 1`);
* band B (238-bit parents) down to node 2; the root parent (node 1, 238 bits), then the root copy.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedUpper (packedWideCommitImage l21StartPrefix heapStartPrefix)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
attribute [local irreducible] execute

/-- The machine state at the first tail word, as the body leaves it. -/
structure TailEntry (s : MachineState) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*GroupedUpper.tailStart)
  selector : s.getReg .x5=0
  out : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  cells : s.getReg .x21=wordAddress cellFirst
  key : s.getReg .x24=9126809632

theorem l21_start_regs (s : MachineState) (e : TailEntry s) :
    L21Regs (l21StartPrefix s GroupedUpper.l21SetupLen) 2097152 := by
  constructor <;> dsimp [l21StartPrefix,GroupedUpper.l21SetupLen,GroupedUpper.l21SetupOps,List.take,List.foldl,
    execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x5=0 from e.selector,show s.regs .x9=4294971424 from e.heap,
    show s.regs .x21=wordAddress cellFirst from e.cells,show s.regs .x24=9126809632 from e.key]
  all_goals first | rfl | decide

theorem l21_start_x8 (s : MachineState) :
    (l21StartPrefix s GroupedUpper.l21SetupLen).getReg .x8=s.getReg .x8 := by
  unfold l21StartPrefix GroupedUpper.l21SetupLen; rfl

theorem l21_start_mem (s : MachineState) : (l21StartPrefix s GroupedUpper.l21SetupLen).mem=s.mem := by
  unfold l21StartPrefix GroupedUpper.l21SetupLen; rfl

theorem l21_start_pc (s : MachineState) (e : TailEntry s) :
    (l21StartPrefix s GroupedUpper.l21SetupLen).pc=GroupedUpper.l21Base := by
  have pc := e.pc
  unfold l21StartPrefix GroupedUpper.l21SetupLen
  simp only [GroupedUpper.l21SetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc]
  rfl

theorem heap_start_regs (s : MachineState) (r : L21Regs s 0) :
    BandRegs (heapStartPrefix s 7) 2097151 131071 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩ <;> dsimp [heapStartPrefix,GroupedUpper.heapSetupOps,List.take,List.foldl,
    execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x12=wordAddress (treeWord (l21Node 0)) from r.target,
    show s.regs .x9=wordAddress (treeWord 0) from r.heap,show s.regs .x5=0 from r.selector,
    show s.regs .x11=64 from r.size,show s.regs .x13=0 from r.primitive]
  all_goals first | rfl | decide

theorem heap_start_x8 (s : MachineState) : (heapStartPrefix s 7).getReg .x8=s.getReg .x8 := by
  unfold heapStartPrefix; rfl

theorem heap_start_mem (s : MachineState) : (heapStartPrefix s 7).mem=s.mem := by
  unfold heapStartPrefix; rfl

theorem heap_start_pc (s : MachineState) (pc : s.pc=GroupedUpper.heapSetupPC) :
    (heapStartPrefix s 7).pc=GroupedUpper.bandABase := by
  unfold heapStartPrefix
  simp only [GroupedUpper.heapSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc]
  rfl

theorem l21_loop_run (s : MachineState) (fuel : Nat) (r : L21Regs s 2097152) (pc : s.pc=GroupedUpper.l21Base) :
    execute packedWideCommitImage (6291711+fuel) s true = (do
      let mid ← l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes s
      let e ← execute packedWideCommitImage fuel mid true
      return e.charge 20971775 2097152) :=
  l21_group_execution packedWideCommitImage GroupedUpper.l21Base GroupedUpper.l21Span
    (fun i hi => GroupedUpper.l21_words i hi) GroupedUpper.l21Control (by decide) GroupedUpper.l21Passes fuel s
    (by decide) r (fun _ => pc)

theorem l21_loop_post (s : MachineState) (r : L21Regs s 2097152) (pc : s.pc=GroupedUpper.l21Base)
    {out : MachineState} (reached : out ∈ support (l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes s)) :
    L21Regs out 0 ∧ out.pc=GroupedUpper.heapSetupPC := by
  have post := l21_groups_post GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes s (by decide)
    (fun _ => pc) r reached
  exact ⟨post.1,(post.2 (by decide)).trans (by decide)⟩

theorem bandA_run (s : MachineState) (fuel : Nat) (r : BandRegs s 2097151 131071) (pc : s.pc=GroupedUpper.bandABase) :
    execute packedWideCommitImage (7864559+fuel) s true = (do
      let mid ← bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071 GroupedUpper.bandAPasses s
      let e ← execute packedWideCommitImage fuel mid true
      return e.charge 21627119 1966080) :=
  band_execution recordKind packedWideCommitImage GroupedUpper.bandABase GroupedUpper.bandASpan
    (fun i hi => GroupedUpper.bandA_words i hi) GroupedUpper.bandAControl (by decide) 131071 GroupedUpper.bandAPasses
    fuel s (by decide) r (fun _ => pc)

theorem bandA_post (s : MachineState) (r : BandRegs s 2097151 131071) (pc : s.pc=GroupedUpper.bandABase)
    {out : MachineState} (reached : out ∈ support (bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan
      131071 GroupedUpper.bandAPasses s)) :
    BandRegs out 131071 131071 ∧ out.pc=GroupedUpper.midPC := by
  have post := band_post recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071 GroupedUpper.bandAPasses s
    (by decide) (fun _ => pc) r reached
  exact ⟨post.1,(post.2 (by decide)).trans (by decide)⟩

/-- `addi x7,x9,32`: band B stops at node 1. -/
def midState (s : MachineState) := execInstrBr s (.ADDI .x7 .x9 32)

theorem mid_run (s : MachineState) (pc : s.pc=GroupedUpper.midPC) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) s true = (do
      let e ← execute packedWideCommitImage fuel (midState s) true; return e.charge 1 0) := by
  rw [Nat.add_comm,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (GroupedUpper.fetch_mid s pc)
    (show ordinaryStep s _=some (midState s) from rfl)]
  rfl

theorem mid_regs (s : MachineState) (r : BandRegs s 131071 131071) : BandRegs (midState s) 131071 1 := by
  have keep (reg : Reg) (h : reg≠.x7) : (midState s).getReg reg=s.getReg reg := by
    simp only [midState,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  refine ⟨⟨(keep .x10 (by decide)).trans r.source,(keep .x12 (by decide)).trans r.target,
    (keep .x5 (by decide)).trans r.selector,(keep .x11 (by decide)).trans r.size,
    (keep .x13 (by decide)).trans r.primitive,(keep .x9 (by decide)).trans r.heap⟩,?_,
    (keep .x6 (by decide)).trans r.maskReg⟩
  simp only [midState,execInstrBr,MachineState.getReg_setPC]
  rw [MachineState.getReg_setReg_eq (by decide),r.heap]
  decide

theorem mid_x8 (s : MachineState) : (midState s).getReg .x8=s.getReg .x8 := by
  simp only [midState,execInstrBr,MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne _ _ _ _ (by decide)

theorem mid_mem (s : MachineState) : (midState s).mem=s.mem := rfl

theorem mid_pc (s : MachineState) (pc : s.pc=GroupedUpper.midPC) : (midState s).pc=GroupedUpper.bandBBase := by
  change s.pc+4=_; rw [pc]; rfl

theorem bandB_run (s : MachineState) (fuel : Nat) (r : BandRegs s 131071 1) (pc : s.pc=GroupedUpper.bandBBase) :
    execute packedWideCommitImage (786449+fuel) s true = (do
      let mid ← bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1 GroupedUpper.bandBPasses s
      let e ← execute packedWideCommitImage fuel mid true
      return e.charge 1703939 131070) :=
  band_execution t238Kind packedWideCommitImage GroupedUpper.bandBBase GroupedUpper.bandBSpan
    (fun i hi => GroupedUpper.bandB_words i hi) GroupedUpper.bandBControl (by decide) 1 GroupedUpper.bandBPasses
    fuel s (by decide) r (fun _ => pc)

theorem bandB_post (s : MachineState) (r : BandRegs s 131071 1) (pc : s.pc=GroupedUpper.bandBBase)
    {out : MachineState} (reached : out ∈ support (bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan
      1 GroupedUpper.bandBPasses s)) :
    BandRegs out 1 1 ∧ out.pc=GroupedUpper.rootParentPC := by
  have post := band_post t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1 GroupedUpper.bandBPasses s
    (by decide) (fun _ => pc) r reached
  exact ⟨post.1,(post.2 (by decide)).trans (by decide)⟩

/-- The root parent: compression of nodes 3 and 2 into node 1, cut to 238 bits (no cursor moves). -/
theorem root_parent_run (s : MachineState) (fuel : Nat) (r : BandRegs s 1 1) (pc : s.pc=GroupedUpper.rootParentPC) :
    execute packedWideCommitImage (4+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s 1)))) : OracleComp World (BitVec 256))
          let result ← execute packedWideCommitImage fuel (t238Mask s 1 answer) true
          return result.charge 11 1) := by
  have words := GroupedUpper.root_parent_words
  rw [show 4+fuel=(fuel+3)+1 by omega,band_call_at _ s 1 _ (by decide) r.toParentRegs ((words s).1 pc)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let t := parentWritten s 1 answer
  let u := execInstrBr t (.LHU .x31 .x12 28)
  let v := execInstrBr u (.AND .x31 .x31 .x6)
  have tpc : t.pc=GroupedUpper.rootParentPC+4 := by simp only [t,parentWritten,written_pc,pc]
  have upc : u.pc=GroupedUpper.rootParentPC+8 := by change t.pc+4=_; rw [tpc,BitVec.add_assoc]; rfl
  have vpc : v.pc=GroupedUpper.rootParentPC+12 := by change u.pc+4=_; rw [upc,BitVec.add_assoc]; rfl
  have tx12 := t238_x12 s 1 answer r.toParentRegs
  have vx12 : v.getReg .x12=wordAddress (treeWord 1) := by
    rw [and_reg _ _ (by decide),lhu_reg _ _ (by decide)]; exact tx12
  have loadAddr := node_address t 1 28 28 rfl tx12
  have storeAddr := node_address v 1 28 28 rfl vx12
  have loadValid := node_valid 1 28 2 (by decide) (by decide) (by decide) (by decide)
  have storeValid := node_valid 1 28 4 (by decide) (by decide) (by decide) (by decide)
  have load : ordinaryStep t (.base (.LHU .x31 .x12 28))=some u := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,loadAddr,loadValid,↓reduceIte]
    rfl
  have store : ordinaryStep v (.base (.SW .x12 .x31 28))=some (t238Mask s 1 answer) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,storeAddr,storeValid,↓reduceIte]
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((words t).2.1 tpc) load,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((words u).2.2.1 upc) (show ordinaryStep u _=some v from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((words v).2.2.2 vpc) store]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem root_parent_pc (s : MachineState) (answer : BitVec 256) (pc : s.pc=GroupedUpper.rootParentPC) :
    (t238Mask s 1 answer).pc=GroupedUpper.rootPC := by
  unfold t238Mask
  rw [step_pc _ _ (by simp),step_pc _ _ (by simp),step_pc _ _ (by simp),parentWritten,written_pc,pc]
  rfl

end TwoPermutationPrototype.Grouped
