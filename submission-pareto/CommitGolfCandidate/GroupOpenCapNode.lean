import CommitGolfCandidate.K3OpenCapStep
import CommitGolfCandidate.GroupOpenCapCost
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

/-! Chunked T238 cap walk, single nodes: the cursor state `CapRun`, the cursor moves keeping `x30` and memory, one
emit block (`emit_node`, entered at 668 and leaving at 701), and a DFS emit: lookup, the stub `jal x18,<668>` at
702, the emit block and the return `jalr x0,x18,0` at 701 into the advance block at 703. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64
open Opening (CapSpan proofBase cap_span_node cap_span_children cap_frontier_nodes_small capDigestAddress)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

private theorem beq_reg (u : MachineState) (a b r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BEQ a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

private theorem bgeu_reg (u : MachineState) (a b r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BGEU a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

private theorem bne_reg2 (u : MachineState) (a b r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BNE a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

private theorem jal_reg (u : MachineState) (r : Reg) (imm : BitVec 21) :
    (execInstrBr u (.JAL .x0 imm)).getReg r=u.getReg r := MachineState.getReg_setPC ..

private theorem instrs_preserve (code : List Instr) (s : MachineState) (r : Reg)
    (each : ∀ op ∈ code, ∀ st : MachineState, (execInstrBr st op).getReg r=st.getReg r) :
    (code.foldl execInstrBr s).getReg r=s.getReg r := by
  induction code generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun o h => each o (List.mem_cons_of_mem _ h)), each op (by simp)]

theorem visit_x30 (state : MachineState) : (cursorVisitPrefix state 4).getReg .x30=state.getReg .x30 :=
  visit_register state .x30 (by decide) (by decide) (by decide)

theorem known_x30 (state : MachineState) (n : Nat) (small : n ≤ 3) :
    (cursorKnownPrefix state n).getReg .x30=state.getReg .x30 := by
  unfold cursorKnownPrefix
  apply instrs_preserve; intro op hop st
  have code : (capWalkInstructions.drop 5).take 3=[.BGEU .x16 .x27 172, .SLLI .x6 .x6 1, .JAL .x0 2097128] := rfl
  have sub : op ∈ (capWalkInstructions.drop 5).take 3 := by
    rw [List.mem_iff_getElem] at hop ⊢
    obtain ⟨i,hi,e⟩ := hop
    refine ⟨i,by simp at hi ⊢; omega,?_⟩
    rw [← e]; simp [List.getElem_take]
  rw [code] at sub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sub
  rcases sub with rfl|rfl|rfl <;> first | exact bgeu_reg .. | exact jal_reg .. | simp [execInstrBr]

private theorem checks_x30 (state : MachineState) : (afterAdvanceChecks state).getReg .x30=state.getReg .x30 := by
  have c : (capWalkInstructions.drop 43).take 2=[.ANDI .x7 .x6 1, .BEQ .x7 .x0 8016] := rfl
  unfold afterAdvanceChecks advancePrefix; rw [c]
  apply instrs_preserve; intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl|rfl <;> first | exact beq_reg .. | simp [execInstrBr]

theorem right_x30 (state : MachineState) : (advanceRight state).getReg .x30=state.getReg .x30 := by
  have step : (advanceRight state).getReg .x30=(afterAdvanceChecks state).getReg .x30 := by
    simp [advanceRight, advanceRightStep, execInstrBr]
  exact step.trans (checks_x30 state)

theorem up_x30 (state : MachineState) : (advanceUp state).getReg .x30=state.getReg .x30 := by
  have c : (capWalkInstructions.drop 45).take 2=[.SRLI .x6 .x6 1, .BNE .x6 .x23 8180] := rfl
  unfold advanceUp advancePrefix; rw [c, instrs_preserve _ _ _ (by
    intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl|rfl <;> first | exact bne_reg2 .. | simp [execInstrBr])]
  exact checks_x30 state

theorem root_x30 (state : MachineState) : (advanceRootExit state).getReg .x30=state.getReg .x30 := by
  unfold advanceRootExit; rw [MachineState.getReg_setPC]; exact up_x30 state

theorem lookup_block (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x1a54) :
    let after := cursorVisitPrefix state 4
    RunsOpeningBlock state after 4 ∧
    after.pc = (if capIsMarked groups node height then 0x1a64 else 0x1af8) ∧
    CapPosition groups after node dest ∧ after.mem = state.mem ∧
    after.getReg .x16 = BitVec.ofNat 64 (8 * node) := by
  obtain ⟨_, target, nextNode, nextDest, memory, context, level⟩ :=
    cap_lookup state groups node height 0 false span position.context pc position.nodeWord
  exact ⟨fun fuel coins => (cap_lookup state groups node height fuel coins span position.context pc
    position.nodeWord).1, target, ⟨context, nextNode.trans position.nodeWord, nextDest.trans position.destWord⟩,
    memory, level⟩

theorem byte_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Word) : a.getByte w=b.getByte w := by
  unfold MachineState.getByte MachineState.getMem; rw [h]

theorem read_congr (s t : MachineState) (address count : Nat)
    (same : ∀ j<count, t.getByte (BitVec.ofNat 64 (address+j))=s.getByte (BitVec.ofNat 64 (address+j))) :
    readBuffer t address count=readBuffer s address count := by
  unfold readBuffer; congr 1
  apply Finset.sum_congr rfl; intro j hj; rw [same j (Finset.mem_range.1 hj)]

theorem bytes_mem {a b : MachineState} (h : a.mem=b.mem) (address count : Nat) :
    bytesAt a address count=bytesAt b address count :=
  bytes_at_congr _ _ _ _ (fun j _ => byte_of_mem h _)

theorem read_mem {a b : MachineState} (h : a.mem=b.mem) (address count : Nat) :
    readBuffer a address count=readBuffer b address count :=
  read_congr _ _ _ _ (fun j _ => byte_of_mem h _)

private theorem heap_room (n : Nat) (hn : n<512) (j : Nat) (hj : j<32) : capDigestAddress n+j<proofBase := by
  unfold capDigestAddress Opening.trapdoorBase Opening.proofBase Opening.indicesBase Opening.trapdoorBytes
    LENGTH LOG_LENGTH
  omega

/-- What a cursor state carries: the cap position of `node`, the countdown, the cap bytes so far and the heap. -/
structure CapRun (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat) (vs : List (BitVec 256))
    (state : MachineState) (node : Nat) : Prop where
  position : CapPosition groups state node (capStart+capOffset vs.length)
  counter : state.getReg .x30=BitVec.ofNat 64 (7-vs.length%8)
  bytes : bytesAt state capStart (capOffset vs.length)=foldNodes vs
  heapRead : ∀ n<512, readBuffer state (capDigestAddress n) 32=heap n

theorem cap_offset_even (n : Nat) : capOffset n%2=0 := by unfold capOffset; omega

theorem cap_offset_mono (n m : Nat) (h : n ≤ m) : capOffset n ≤ capOffset m := by
  unfold capOffset; omega

/-- A run survives a step that keeps the fixed registers, `x6`, `x21`, `x30` and memory. -/
theorem CapRun.of_kept {groups : List Nat} {heap : Nat → BitVec 256} {capStart : Nat} {vs : List (BitVec 256)}
    {before after : MachineState} {node : Nat} (run : CapRun groups heap capStart vs before node)
    (regs : ∀ r, r ∈ ([.x25,.x26,.x27,.x20,.x23,.x6,.x21,.x30] : List Reg) → after.getReg r=before.getReg r)
    (memory : after.mem=before.mem) : CapRun groups heap capStart vs after node := by
  refine ⟨⟨?_, (regs .x6 (by decide)).trans run.position.nodeWord, (regs .x21 (by decide)).trans run.position.destWord⟩,
    (regs .x30 (by decide)).trans run.counter, (bytes_mem memory _ _).trans run.bytes,
    fun n hn => (read_mem memory _ _).trans (run.heapRead n hn)⟩
  apply run.position.context.of_preserved
  · intro r member
    exact regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  · intro n _ _
    exact congrFun memory (BitVec.ofNat 64 (Opening.markBase+8*n))

/-- A run moved to another node: the fixed registers, `x21`, `x30` and memory kept, `x6` the new node. -/
theorem CapRun.of_moved {groups : List Nat} {heap : Nat → BitVec 256} {capStart : Nat} {vs : List (BitVec 256)}
    {before after : MachineState} {node node' : Nat} (run : CapRun groups heap capStart vs before node)
    (regs : ∀ r, r ∈ ([.x25,.x26,.x27,.x20,.x23,.x21,.x30] : List Reg) → after.getReg r=before.getReg r)
    (memory : after.mem=before.mem) (nodeWord : after.getReg .x6=BitVec.ofNat 64 node') :
    CapRun groups heap capStart vs after node' := by
  refine ⟨⟨?_, nodeWord, (regs .x21 (by decide)).trans run.position.destWord⟩,
    (regs .x30 (by decide)).trans run.counter, (bytes_mem memory _ _).trans run.bytes,
    fun n hn => (read_mem memory _ _).trans (run.heapRead n hn)⟩
  apply run.position.context.of_preserved
  · intro r member
    exact regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  · intro n _ _
    exact congrFun memory (BitVec.ofNat 64 (Opening.markBase+8*n))

/-- One emit block for the node in `x6`: entered at 668, it leaves at 701 with the node's 28 or 30 bytes added. -/
theorem emit_node (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (vs : List (BitVec 256)) (state : MachineState) (node : Nat) (bounded : node<512)
    (run : CapRun groups heap capStart vs state node) (pc : state.pc=0x1a70)
    (separate : proofBase ≤ capStart) (aligned : capStart%2=0)
    (fits : capStart+capOffset (vs.length+1)+2 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (CapCopy.cycles (capStart+capOffset vs.length)+7+
        34*((vs.length+1)/8-vs.length/8)) ∧ after.pc=0x1af4 ∧
      CapRun groups heap capStart (vs++[heap node]) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+1) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) ∧
      (∀ r, r ≠ .x7 → r ≠ .x21 → r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → after.getReg r=state.getReg r) := by
  have succ := cap_offset_succ vs.length
  have big : vs.length%8=7 → 210 ≤ capOffset vs.length := by intro h; unfold capOffset; omega
  obtain ⟨after,erun,epc,epos,ecount,copied,folded,frame,keep⟩ :=
    emit groups state node (capStart+capOffset vs.length) (7-vs.length%8) bounded run.position run.counter
      (by omega) pc
      (by split <;> (rename_i h; first | (have := big (by omega); omega) | omega))
      (by have := cap_offset_even vs.length; omega)
      (by split at succ <;> omega)
  have zero : (7-vs.length%8=0) ↔ vs.length%8=7 := by omega
  have width : capStart+capOffset vs.length+(if 7-vs.length%8=0 then 28 else 30)=capStart+capOffset (vs.length+1) := by
    rw [succ]; by_cases h : vs.length%8=7 <;> simp [h, zero] <;> omega
  have cost : (if 7-vs.length%8=0 then CapCopy.cycles (capStart+capOffset vs.length)+41
      else CapCopy.cycles (capStart+capOffset vs.length)+7)=
        CapCopy.cycles (capStart+capOffset vs.length)+7+34*((vs.length+1)/8-vs.length/8) := by
    by_cases h : vs.length%8=7
    · rw [if_pos (by omega)]; omega
    · rw [if_neg (by omega)]; omega
  have touched (a : Nat) (h : EmitTouched (capStart+capOffset vs.length) (7-vs.length%8) a) :
      capStart ≤ a ∧ a<capStart+capOffset (vs.length+1) := by
    rcases h with ⟨lo,hi⟩|⟨c0,k,hk,e|e⟩
    · rw [← width]; omega
    · have := big (by omega); rw [succ, if_pos (by omega)]; omega
    · have := big (by omega); rw [succ, if_pos (by omega)]; omega
  have outside (a : Nat) (fit : a<2^64) (far : a<capStart ∨ capStart+capOffset (vs.length+1) ≤ a) :
      after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a) :=
    frame a fit (fun t => by have := touched a t; omega)
  have bytes := cap_bytes_step state after capStart node (7-vs.length%8) vs rfl aligned
    (by unfold MEMORY_BYTES at fits; omega) run.bytes copied folded frame
  rw [run.heapRead node bounded] at bytes
  refine ⟨after,?_,epc,⟨?_,?_,?_,?_⟩,outside,keep⟩
  · rw [← cost]; exact erun
  · rw [List.length_append, List.length_singleton, ← width]; exact epos
  · rw [ecount, List.length_append, List.length_singleton]; congr 1
    by_cases h : vs.length%8=7
    · rw [if_pos (by omega)]; omega
    · rw [if_neg (by omega)]; omega
  · rw [List.length_append, List.length_singleton]; exact bytes
  · intro n hn
    rw [← run.heapRead n hn]
    apply read_congr; intro j hj
    have room := heap_room n hn j hj
    have large : proofBase<2^64 := by decide
    exact outside (capDigestAddress n+j) (by omega) (Or.inl (by omega))

/-- An unmarked node: lookup, the stub at 702, the emit block and the return to the advance block at 703. -/
theorem walk_unmarked (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (vs : List (BitVec 256)) (state : MachineState) (node height : Nat) (span : CapSpan node height)
    (run : CapRun groups heap capStart vs state node) (pc : state.pc=0x1a54)
    (mark : capIsMarked groups node height=false) (separate : proofBase ≤ capStart) (aligned : capStart%2=0)
    (fits : capStart+capOffset (vs.length+1)+2 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (CapCopy.cycles (capStart+capOffset vs.length)+13+
        34*((vs.length+1)/8-vs.length/8)) ∧ after.pc=0x1afc ∧
      CapRun groups heap capStart (vs++[heap node]) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+1) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  obtain ⟨lookup, branch, looked, stable, _⟩ := lookup_block groups state node height _ span run.position pc
  have target : (cursorVisitPrefix state 4).pc=0x1af8 := by simpa [mark] using branch
  set l:=cursorVisitPrefix state 4 with hl
  have bounded := (cap_span_node node height span).2
  have runL : CapRun groups heap capStart vs l node :=
    ⟨looked, (visit_x30 state).trans run.counter, (bytes_mem stable _ _).trans run.bytes,
      fun n hn => (read_mem stable _ _).trans (run.heapRead n hn)⟩
  have runS : CapRun groups heap capStart vs (emitStub l) node := by
    refine CapRun.of_kept (after := emitStub l) runL ?_ rfl
    intro r member
    have : r ≠ .x18 := by intro e; subst e; simp at member
    simp [emitStub, Ne.symm this]
  have stubPC : (emitStub l).pc=0x1a70 := rfl
  obtain ⟨after, erun, epc, erunAfter, frame, keep⟩ :=
    emit_node emit groups heap capStart vs (emitStub l) node bounded runS stubPC separate aligned fits
  have link : after.getReg .x18=0x1afc := by
    rw [keep .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  let back := after.setPC 0x1afc
  have ret : RunsOpeningBlock after back 1 := fun fuel coins =>
    execute_emit_return after epc 0x1afc link (by decide) fuel coins
  refine ⟨back, ?_, rfl, erunAfter.of_kept (fun _ _ => rfl) rfl, ?_⟩
  · have chain := ((lookup.next (fun fuel coins => execute_emit_stub l target fuel coins)).next erun).next ret
    convert chain using 1; omega
  · intro a fit far
    rw [show back.getByte (BitVec.ofNat 64 a)=after.getByte (BitVec.ofNat 64 a) from rfl, frame a fit far]
    exact (byte_of_mem rfl _).trans (byte_of_mem stable _)

end TwoPermutationPrototype.GroupedOpening
