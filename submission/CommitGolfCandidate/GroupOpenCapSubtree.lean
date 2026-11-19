import CommitGolfCandidate.K3OpenCapStep
import CommitGolfCandidate.GroupOpenCapCost
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

/-! T238 cap cursor: the stackless DFS of K1x with the countdown `x30` and the packed frontier bytes. The cursor
moves (lookup, prune, descend, advance) keep `x30` and memory; each emitted node is one `EmitCap238` block, and
`cap_bytes_step` grows the cap bytes `foldNodes`. Generalized over the nodes `vs` already emitted from `capStart`. -/
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

theorem visit_x30 (state : MachineState) : (cursorVisitPrefix state 4).getReg .x30=state.getReg .x30 := by
  have code : (capWalkInstructions.drop 1).take 4=[.SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .LD .x28 .x7 0, .BEQ .x28 .x0 16] := rfl
  unfold cursorVisitPrefix; rw [code]
  apply instrs_preserve; intro op hop st
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl <;> first | exact beq_reg .. | simp [execInstrBr]

theorem known_x30 (state : MachineState) (n : Nat) (small : n ≤ 3) :
    (cursorKnownPrefix state n).getReg .x30=state.getReg .x30 := by
  unfold cursorKnownPrefix
  apply instrs_preserve; intro op hop st
  have code : (capWalkInstructions.drop 5).take 3=[.BGEU .x6 .x27 144, .SLLI .x6 .x6 1, .JAL .x0 2097128] := rfl
  have sub : op ∈ (capWalkInstructions.drop 5).take 3 := by
    rw [List.mem_iff_getElem] at hop ⊢
    obtain ⟨i,hi,e⟩ := hop
    refine ⟨i,by simp at hi ⊢; omega,?_⟩
    rw [← e]; simp [List.getElem_take]
  rw [code] at sub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sub
  rcases sub with rfl|rfl|rfl <;> first | exact bgeu_reg .. | exact jal_reg .. | simp [execInstrBr]

private theorem checks_x30 (state : MachineState) : (afterAdvanceChecks state).getReg .x30=state.getReg .x30 := by
  have c1 : (capWalkInstructions.drop 41).take 1=[.BEQ .x6 .x23 32] := rfl
  have c2 : (capWalkInstructions.drop 42).take 2=[.ANDI .x7 .x6 1, .BEQ .x7 .x0 16] := rfl
  unfold afterAdvanceChecks advancePrefix; rw [c1, c2]
  rw [instrs_preserve _ _ _ (by
    intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl|rfl <;> first | exact beq_reg .. | simp [execInstrBr])]
  apply instrs_preserve; intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl <;> exact beq_reg ..

theorem right_x30 (state : MachineState) : (advanceRight state).getReg .x30=state.getReg .x30 := by
  have c : (capWalkInstructions.drop 47).take 2=[.ADDI .x6 .x6 1, .JAL .x0 2096964] := rfl
  unfold advanceRight advancePrefix; rw [c, instrs_preserve _ _ _ (by
    intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl|rfl <;> first | exact jal_reg .. | simp [execInstrBr])]
  exact checks_x30 state

theorem up_x30 (state : MachineState) : (advanceUp state).getReg .x30=state.getReg .x30 := by
  have c : (capWalkInstructions.drop 44).take 2=[.SRLI .x6 .x6 1, .JAL .x0 2097136] := rfl
  unfold advanceUp advancePrefix; rw [c, instrs_preserve _ _ _ (by
    intro op hop st; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl|rfl <;> first | exact jal_reg .. | simp [execInstrBr])]
  exact checks_x30 state

private theorem lookup_block (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x1a54) :
    let after := cursorVisitPrefix state 4
    RunsOpeningBlock state after 4 ∧
    after.pc = (if capIsMarked groups node height then 0x1a64 else 0x1a70) ∧
    CapPosition groups after node dest ∧ after.mem = state.mem := by
  obtain ⟨_, target, nextNode, nextDest, memory, context⟩ :=
    cap_lookup state groups node height 0 false span position.context pc position.nodeWord
  exact ⟨fun fuel coins => (cap_lookup state groups node height fuel coins span position.context pc
    position.nodeWord).1, target, ⟨context, nextNode.trans position.nodeWord, nextDest.trans position.destWord⟩, memory⟩

private theorem byte_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Word) : a.getByte w=b.getByte w := by
  unfold MachineState.getByte MachineState.getMem; rw [h]

theorem read_congr (s t : MachineState) (address count : Nat)
    (same : ∀ j<count, t.getByte (BitVec.ofNat 64 (address+j))=s.getByte (BitVec.ofNat 64 (address+j))) :
    readBuffer t address count=readBuffer s address count := by
  unfold readBuffer; congr 1
  apply Finset.sum_congr rfl; intro j hj; rw [same j (Finset.mem_range.1 hj)]

private theorem bytes_mem {a b : MachineState} (h : a.mem=b.mem) (address count : Nat) :
    bytesAt a address count=bytesAt b address count :=
  bytes_at_congr _ _ _ _ (fun j _ => byte_of_mem h _)

private theorem read_mem {a b : MachineState} (h : a.mem=b.mem) (address count : Nat) :
    readBuffer a address count=readBuffer b address count :=
  read_congr _ _ _ _ (fun j _ => byte_of_mem h _)

private theorem heap_room (n : Nat) (hn : n<512) (j : Nat) (hj : j<32) : capDigestAddress n+j<proofBase := by
  unfold capDigestAddress Opening.trapdoorBase Opening.proofBase Opening.indicesBase Opening.trapdoorBytes
    LENGTH LOG_LENGTH
  omega

/-- What a cursor state at the start of a subtree carries. -/
structure CapRun (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat) (vs : List (BitVec 256))
    (state : MachineState) (node : Nat) : Prop where
  position : CapPosition groups state node (capStart+capOffset vs.length)
  counter : state.getReg .x30=BitVec.ofNat 64 (7-vs.length%8)
  bytes : bytesAt state capStart (capOffset vs.length)=foldNodes vs
  heapRead : ∀ n<512, readBuffer state (capDigestAddress n) 32=heap n

private theorem cap_offset_even (n : Nat) : capOffset n%2=0 := by unfold capOffset; omega

private theorem cap_offset_mono (n m : Nat) (h : n ≤ m) : capOffset n ≤ capOffset m := by
  unfold capOffset; omega

/-- An unmarked node: lookup, then one emitted node. -/
private theorem walk_unmarked (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (vs : List (BitVec 256)) (state : MachineState) (node height : Nat) (span : CapSpan node height)
    (run : CapRun groups heap capStart vs state node) (pc : state.pc=0x1a54)
    (mark : capIsMarked groups node height=false) (separate : proofBase ≤ capStart) (aligned : capStart%2=0)
    (fits : capStart+capOffset (vs.length+1)+2 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (CapCopy.cycles (capStart+capOffset vs.length)+13+
        34*((vs.length+1)/8-vs.length/8)) ∧ after.pc=0x1af4 ∧
      CapRun groups heap capStart (vs++[heap node]) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+1) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  obtain ⟨lookup, branch, looked, stable⟩ := lookup_block groups state node height _ span run.position pc
  have target : (cursorVisitPrefix state 4).pc=0x1a70 := by simpa [mark] using branch
  set l:=cursorVisitPrefix state 4 with hl
  have bounded := (cap_span_node node height span).2
  have lcount : l.getReg .x30=BitVec.ofNat 64 (7-vs.length%8) := (visit_x30 state).trans run.counter
  have succ := cap_offset_succ vs.length
  have big : vs.length%8=7 → 210 ≤ capOffset vs.length := by intro h; unfold capOffset; omega
  obtain ⟨after,erun,epc,epos,ecount,copied,folded,frame⟩ :=
    emit groups l node (capStart+capOffset vs.length) (7-vs.length%8) bounded looked lcount (by omega) target
      (by split <;> (rename_i h; first | (have := big (by omega); omega) | omega))
      (by have := cap_offset_even vs.length; omega)
      (by split at succ <;> omega)
  have zero : (7-vs.length%8=0) ↔ vs.length%8=7 := by omega
  have width : capStart+capOffset vs.length+(if 7-vs.length%8=0 then 28 else 30)=capStart+capOffset (vs.length+1) := by
    rw [succ]; by_cases h : vs.length%8=7 <;> simp [h, zero] <;> omega
  have cost : (if 7-vs.length%8=0 then CapCopy.cycles (capStart+capOffset vs.length)+43
      else CapCopy.cycles (capStart+capOffset vs.length)+9)=
        CapCopy.cycles (capStart+capOffset vs.length)+9+34*((vs.length+1)/8-vs.length/8) := by
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
    (frame a fit (fun t => by have := touched a t; omega)).trans (byte_of_mem stable _)
  have bytes := cap_bytes_step l after capStart node (7-vs.length%8) vs rfl aligned (by unfold MEMORY_BYTES at fits; omega)
    ((bytes_mem stable _ _).trans run.bytes) copied folded frame
  have value : readBuffer l (capDigestAddress node) 32=heap node :=
    (read_mem stable _ _).trans (run.heapRead node bounded)
  rw [value] at bytes
  refine ⟨after,?_,epc,⟨?_,?_,?_,?_⟩,outside⟩
  · have := lookup.next erun
    rw [cost] at this
    convert this using 1; omega
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
    have big : proofBase<2^64 := by decide
    exact outside (capDigestAddress n+j) (by omega) (Or.inl (by omega))

/-- The cursor emits the subtree's frontier with the T238 countdown, extending the packed cap bytes. -/
theorem cap_subtree_general (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (height : Nat) : ∀ (state : MachineState) (node : Nat) (vs : List (BitVec 256)),
    CapSpan node height → CapRun groups heap capStart vs state node → state.pc=0x1a54 →
    proofBase ≤ capStart → capStart%2=0 →
    capStart+capOffset (vs.length+(capFrontierNodes groups node height).length)+2 ≤ MEMORY_BYTES →
    ∃ after, RunsOpeningBlock state after (capWalkCycles groups node height capStart vs.length) ∧
      after.pc=0x1af4 ∧
      CapRun groups heap capStart (vs++(capFrontierNodes groups node height).map heap) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+(capFrontierNodes groups node height).length) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  induction height with
  | zero =>
    intro state node vs span run pc separate aligned fits
    cases mark : capIsMarked groups node 0
    · have one : (capFrontierNodes groups node 0)=[node] := by simp [capFrontierNodes, mark]
      rw [one] at fits ⊢
      obtain ⟨after,r,p,c,f⟩ := walk_unmarked emit groups heap capStart vs state node 0 span run pc mark separate aligned
        (by simpa using fits)
      refine ⟨after,?_,p,by simpa using c,by simpa using f⟩
      rw [cap_walk_unmarked groups node 0 capStart vs.length mark]
      exact r
    · have none : (capFrontierNodes groups node 0)=[] := by simp [capFrontierNodes, mark]
      obtain ⟨lookup, branch, looked, mem⟩ := lookup_block groups state node 0 _ span run.position pc
      have target : (cursorVisitPrefix state 4).pc=0x1a64 := by simpa [mark] using branch
      obtain ⟨prune, next, final, memAfter⟩ := cap_prune_step groups _ node _ looked span target
      have m : (cursorKnownPrefix (cursorVisitPrefix state 4) 1).mem=state.mem := memAfter.trans mem
      refine ⟨_,?_,next,⟨?_,?_,?_,?_⟩,?_⟩
      · simpa [capWalkCycles, capSubtreeCycles, capFrontierNodes, mark] using lookup.next prune
      · rw [none]; simpa using final
      · rw [none, List.map_nil, List.append_nil]
        exact (known_x30 _ 1 (by decide)).trans ((visit_x30 state).trans run.counter)
      · rw [none, List.map_nil, List.append_nil, bytes_mem m]; exact run.bytes
      · intro n hn; rw [read_mem m]; exact run.heapRead n hn
      · intro a _ _; exact byte_of_mem m _
  | succ height ih =>
    intro state node vs span run pc separate aligned fits
    cases mark : capIsMarked groups node (height+1)
    · have one : (capFrontierNodes groups node (height+1))=[node] := by simp [capFrontierNodes, mark]
      rw [one] at fits ⊢
      obtain ⟨after,r,p,c,f⟩ := walk_unmarked emit groups heap capStart vs state node (height+1) span run pc mark
        separate aligned (by simpa using fits)
      refine ⟨after,?_,p,by simpa using c,by simpa using f⟩
      rw [cap_walk_unmarked groups node (height+1) capStart vs.length mark]
      exact r
    · set left := capFrontierNodes groups (2*node) height with hleft
      set right := capFrontierNodes groups (2*node+1) height with hright
      have both : capFrontierNodes groups node (height+1)=left++right := by simp [capFrontierNodes, mark, left, right]
      rw [both] at fits ⊢
      simp only [List.length_append] at fits ⊢
      obtain ⟨lookup, branch, looked, mem⟩ := lookup_block groups state node (height+1) _ span run.position pc
      have target : (cursorVisitPrefix state 4).pc=0x1a64 := by simpa [mark] using branch
      obtain ⟨descend, leftPC, leftPos, memLeft⟩ := cap_descend_step groups _ node height _ looked span target
      obtain ⟨leftSpan, rightSpan⟩ := cap_span_children node height span
      have m0 : (cursorKnownPrefix (cursorVisitPrefix state 4) 3).mem=state.mem := memLeft.trans mem
      have run0 : CapRun groups heap capStart vs (cursorKnownPrefix (cursorVisitPrefix state 4) 3) (2*node) :=
        ⟨leftPos,(known_x30 _ 3 (by decide)).trans ((visit_x30 state).trans run.counter),
          (bytes_mem m0 _ _).trans run.bytes,fun n hn => (read_mem m0 _ _).trans (run.heapRead n hn)⟩
      obtain ⟨leftEnd, ranLeft, leftDone, runL, frameL⟩ :=
        ih _ (2*node) vs leftSpan run0 leftPC separate aligned (by
          rw [← hleft]
          have := cap_offset_mono (vs.length+left.length) (vs.length+(left.length+right.length)) (by omega); omega)
      rw [← hleft] at runL frameL
      have positive := (cap_span_node node (height+1) span).1
      obtain ⟨across, rightPC, rightPos, memRight⟩ := advance_left_to_right groups leftEnd node _
        positive (cap_span_node _ _ leftSpan).2 runL.position leftDone
      have runR : CapRun groups heap capStart (vs++left.map heap) (advanceRight leftEnd) (2*node+1) :=
        ⟨rightPos,(right_x30 _).trans runL.counter,(bytes_mem memRight _ _).trans runL.bytes,
          fun n hn => (read_mem memRight _ _).trans (runL.heapRead n hn)⟩
      have e1 : (vs++left.map heap).length=vs.length+left.length := by simp
      obtain ⟨rightEnd, ranRight, rightDone, runRR, frameR⟩ :=
        ih _ (2*node+1) (vs++left.map heap) rightSpan runR rightPC separate aligned (by
          rw [← hright, e1, show vs.length+left.length+right.length=vs.length+(left.length+right.length) by omega]
          exact fits)
      rw [← hright] at runRR frameR
      obtain ⟨up, finalPC, finalPos, memUp⟩ := advance_right_to_parent groups rightEnd node _
        positive (cap_span_node _ _ rightSpan).2 runRR.position rightDone
      have lists : vs++(left++right).map heap=(vs++left.map heap)++right.map heap := by
        rw [List.map_append, List.append_assoc]
      have e2 : vs.length+(left.length+right.length)=(vs++left.map heap).length+right.length := by rw [e1]; omega
      rw [lists, e2]
      refine ⟨advanceUp rightEnd, ?_, finalPC, ⟨finalPos,(up_x30 _).trans runRR.counter,
        (bytes_mem memUp _ _).trans runRR.bytes,fun n hn => (read_mem memUp _ _).trans (runRR.heapRead n hn)⟩, ?_⟩
      · have trace := ((((lookup.next descend).next ranLeft).next across).next ranRight).next up
        rw [cap_walk_branch groups node height capStart vs.length mark]
        rw [e1] at trace
        rw [← hleft]
        convert trace using 1
        omega
      · intro a fit far
        have mono := cap_offset_mono (vs.length+left.length) ((vs++left.map heap).length+right.length) (by omega)
        rw [byte_of_mem memUp, frameR a fit far, byte_of_mem memRight, frameL a fit (by
            rcases far with h|h
            · exact Or.inl h
            · right; omega)]
        exact byte_of_mem m0 _

/-- Root form (no node emitted before, countdown 7): the interface of `cap_subtree` (GroupOpenCapEmit). -/
theorem cap_subtree_of_emit (emit : EmitCap238) (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc=0x1a54) (separate : proofBase ≤ dest) (aligned : dest%2=0)
    (fits : dest+capOffset (capFrontierNodes groups node height).length+2 ≤ MEMORY_BYTES)
    (counter : state.getReg .x30=7#64) :
    ∃ after, RunsOpeningBlock state after (capWalkCycles groups node height dest 0) ∧
      after.pc=0x1af4 ∧
      CapPosition groups after node (dest+capOffset (capFrontierNodes groups node height).length) ∧
      (∀ address<2^64, address<dest ∨ dest+capOffset (capFrontierNodes groups node height).length ≤ address →
        after.getByte (BitVec.ofNat 64 address)=state.getByte (BitVec.ofNat 64 address)) ∧
      bytesAt after dest (capOffset (capFrontierNodes groups node height).length)=
        foldNodes ((capFrontierNodes groups node height).map (fun n => readBuffer state (capDigestAddress n) 32)) := by
  have start : CapRun groups (fun n => readBuffer state (capDigestAddress n) 32) dest [] state node :=
    ⟨by simpa [capOffset] using position, by simpa using counter,
      by simp [bytesAt, capOffset, fold_nodes_nil], fun n _ => rfl⟩
  obtain ⟨after,r,p,run,frame⟩ := cap_subtree_general emit groups _ dest height state node [] span start pc
    separate aligned (by simpa using fits)
  refine ⟨after,?_,p,?_,?_,?_⟩
  · simpa using r
  · simpa using run.position
  · simpa using frame
  · simpa using run.bytes

end TwoPermutationPrototype.GroupedOpening
