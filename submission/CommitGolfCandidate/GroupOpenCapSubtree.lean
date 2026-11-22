import CommitGolfCandidate.GroupOpenCapChunkRun

/-! Chunked T238 cap cursor: the stackless DFS of K1x over heights 8..3 with the countdown `x30` and the packed
frontier bytes. A marked level-5 node hands its subtree to the chunk code (`chunk_run`); an unmarked node is one
DFS emit (`walk_unmarked`). Every subtree walk ends in the advance block at 703 with the subtree root in `x6`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64
open Opening (CapSpan proofBase cap_span_node cap_span_children capDigestAddress)

/-- The cursor emits the frontier of a subtree of height `k+3`, extending the packed cap bytes. -/
theorem cap_subtree_general (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (k : Nat) : ∀ (state : MachineState) (node : Nat) (vs : List (BitVec 256)),
    1 < node → CapSpan node (k+3) → CapRun groups heap capStart vs state node → state.pc=0x1a54 →
    proofBase ≤ capStart → capStart%2=0 →
    capStart+capOffset (vs.length+(capFrontierNodes groups node (k+3)).length)+2 ≤ MEMORY_BYTES →
    ∃ after, RunsOpeningBlock state after (capWalkB groups node k capStart vs.length) ∧
      after.pc=0x1afc ∧
      CapRun groups heap capStart (vs++(capFrontierNodes groups node (k+3)).map heap) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+(capFrontierNodes groups node (k+3)).length) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  induction k with
  | zero =>
    intro state node vs nonroot span run pc separate aligned fits
    cases mark : capIsMarked groups node 3
    · have one : (capFrontierNodes groups node 3)=[node] := by simp [capFrontierNodes, mark]
      rw [one] at fits ⊢
      obtain ⟨after,r,p,c,f⟩ := walk_unmarked emit groups heap capStart vs state node 3 span run pc mark separate aligned
        (by simpa using fits)
      refine ⟨after,?_,p,by simpa using c,by simpa using f⟩
      rw [cap_walk_b_unmarked groups node 0 capStart vs.length mark]
      exact r
    · obtain ⟨lookup, branch, looked, mem, level⟩ := lookup_block groups state node 3 _ span run.position pc
      have target : (cursorVisitPrefix state 4).pc=0x1a64 := by simpa [mark] using branch
      obtain ⟨jump, jumped, levelJ⟩ := cap_chunk_step groups _ node _ looked span level target
      let j := (cursorVisitPrefix state 4).setPC 0x1b10
      have runJ : CapRun groups heap capStart vs j node :=
        ⟨jumped, (visit_x30 state).trans run.counter, (bytes_mem mem _ _).trans run.bytes,
          fun n hn => (read_mem mem _ _).trans (run.heapRead n hn)⟩
      obtain ⟨after, ran, done, runA, frame⟩ :=
        chunk_run emit groups heap capStart vs j node span runJ levelJ rfl mark separate aligned fits
      refine ⟨after, ?_, done, runA, ?_⟩
      · rw [cap_walk_b_chunk groups node capStart vs.length mark]
        have trace := (lookup.next jump).next ran
        convert trace using 1; omega
      · intro a fit far
        rw [frame a fit far]
        exact (byte_of_mem rfl _).trans (byte_of_mem mem _)
  | succ k ih =>
    intro state node vs nonroot span run pc separate aligned fits
    cases mark : capIsMarked groups node (k+4)
    · have one : (capFrontierNodes groups node (k+1+3))=[node] := by
        rw [show k+1+3=(k+3)+1 by omega]; simp [capFrontierNodes, show k+3+1=k+4 by omega, mark]
      rw [one] at fits ⊢
      obtain ⟨after,r,p,c,f⟩ := walk_unmarked emit groups heap capStart vs state node (k+1+3) span run pc
        (by rw [show k+1+3=k+4 by omega]; exact mark) separate aligned (by simpa using fits)
      refine ⟨after,?_,p,by simpa using c,by simpa using f⟩
      rw [cap_walk_b_unmarked groups node (k+1) capStart vs.length (by rw [show k+1+3=k+4 by omega]; exact mark)]
      exact r
    · set left := capFrontierNodes groups (2*node) (k+3) with hleft
      set right := capFrontierNodes groups (2*node+1) (k+3) with hright
      have both : capFrontierNodes groups node (k+1+3)=left++right := by
        rw [show k+1+3=(k+3)+1 by omega]; simp [capFrontierNodes, show k+3+1=k+4 by omega, mark, left, right]
      rw [both] at fits ⊢
      simp only [List.length_append] at fits ⊢
      have span4 : CapSpan node (k+4) := by simpa [show k+1+3=k+4 by omega] using span
      obtain ⟨lookup, branch, looked, mem, level⟩ := lookup_block groups state node (k+4) _ span4 run.position pc
      have target : (cursorVisitPrefix state 4).pc=0x1a64 := by simpa [mark] using branch
      obtain ⟨descend, leftPC, leftPos, memLeft⟩ := cap_descend_step groups _ node k _ looked span4 level target
      obtain ⟨leftSpan, rightSpan⟩ := cap_span_children node (k+3) (by simpa [show k+3+1=k+4 by omega] using span4)
      have m0 : (cursorKnownPrefix (cursorVisitPrefix state 4) 3).mem=state.mem := memLeft.trans mem
      have run0 : CapRun groups heap capStart vs (cursorKnownPrefix (cursorVisitPrefix state 4) 3) (2*node) :=
        ⟨leftPos,(known_x30 _ 3 (by decide)).trans ((visit_x30 state).trans run.counter),
          (bytes_mem m0 _ _).trans run.bytes,fun n hn => (read_mem m0 _ _).trans (run.heapRead n hn)⟩
      obtain ⟨leftEnd, ranLeft, leftDone, runL, frameL⟩ :=
        ih _ (2*node) vs (by omega) leftSpan run0 leftPC separate aligned (by
          rw [← hleft]
          have := cap_offset_mono (vs.length+left.length) (vs.length+(left.length+right.length)) (by omega); omega)
      rw [← hleft] at runL frameL
      have positive := (cap_span_node node (k+4) span4).1
      obtain ⟨across, rightPC, rightPos, memRight⟩ := advance_left_to_right groups leftEnd node _
        positive (cap_span_node _ _ leftSpan).2 runL.position leftDone
      have runR : CapRun groups heap capStart (vs++left.map heap) (advanceRight leftEnd) (2*node+1) :=
        ⟨rightPos,(right_x30 _).trans runL.counter,(bytes_mem memRight _ _).trans runL.bytes,
          fun n hn => (read_mem memRight _ _).trans (runL.heapRead n hn)⟩
      have e1 : (vs++left.map heap).length=vs.length+left.length := by simp
      obtain ⟨rightEnd, ranRight, rightDone, runRR, frameR⟩ :=
        ih _ (2*node+1) (vs++left.map heap) (by omega) rightSpan runR rightPC separate aligned (by
          rw [← hright, e1, show vs.length+left.length+right.length=vs.length+(left.length+right.length) by omega]
          exact fits)
      rw [← hright] at runRR frameR
      obtain ⟨up, finalPC, finalPos, memUp⟩ := advance_right_to_parent groups rightEnd node _
        nonroot (cap_span_node _ _ rightSpan).2 runRR.position rightDone
      have lists : vs++(left++right).map heap=(vs++left.map heap)++right.map heap := by
        rw [List.map_append, List.append_assoc]
      have e2 : vs.length+(left.length+right.length)=(vs++left.map heap).length+right.length := by rw [e1]; omega
      rw [lists, e2]
      refine ⟨advanceUp rightEnd, ?_, finalPC, ⟨finalPos,(up_x30 _).trans runRR.counter,
        (bytes_mem memUp _ _).trans runRR.bytes,fun n hn => (read_mem memUp _ _).trans (runRR.heapRead n hn)⟩, ?_⟩
      · have trace := ((((lookup.next descend).next ranLeft).next across).next ranRight).next up
        rw [cap_walk_b_branch groups node k capStart vs.length mark]
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

/-- The root (node 1, marked whenever a position is opened): lookup, descent, both children through
`cap_subtree_general`, the step across (row 660), and the root exit from its right child (703..707). -/
theorem cap_root_general (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (state : MachineState) (vs : List (BitVec 256))
    (span : CapSpan 1 8) (run : CapRun groups heap capStart vs state 1) (pc : state.pc=0x1a54)
    (mark : capIsMarked groups 1 8=true)
    (separate : proofBase ≤ capStart) (aligned : capStart%2=0)
    (fits : capStart+capOffset (vs.length+(capFrontierNodes groups 1 8).length)+2 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (capWalkB groups 1 5 capStart vs.length+1) ∧
      after.pc=0x1b14 ∧
      CapRun groups heap capStart (vs++(capFrontierNodes groups 1 8).map heap) after 1 ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+(capFrontierNodes groups 1 8).length) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  set left := capFrontierNodes groups (2*1) 7 with hleft
  set right := capFrontierNodes groups (2*1+1) 7 with hright
  have both : capFrontierNodes groups 1 8=left++right := by simp [capFrontierNodes, mark, left, right]
  rw [both] at fits ⊢
  simp only [List.length_append] at fits ⊢
  obtain ⟨lookup, branch, looked, mem, level⟩ := lookup_block groups state 1 8 _ span run.position pc
  have target : (cursorVisitPrefix state 4).pc=0x1a64 := by simpa [mark] using branch
  obtain ⟨descend, leftPC, leftPos, memLeft⟩ := cap_descend_step groups _ 1 4 _ looked span level target
  obtain ⟨leftSpan, rightSpan⟩ := cap_span_children 1 7 span
  have m0 : (cursorKnownPrefix (cursorVisitPrefix state 4) 3).mem=state.mem := memLeft.trans mem
  have run0 : CapRun groups heap capStart vs (cursorKnownPrefix (cursorVisitPrefix state 4) 3) (2*1) :=
    ⟨leftPos,(known_x30 _ 3 (by decide)).trans ((visit_x30 state).trans run.counter),
      (bytes_mem m0 _ _).trans run.bytes,fun n hn => (read_mem m0 _ _).trans (run.heapRead n hn)⟩
  obtain ⟨leftEnd, ranLeft, leftDone, runL, frameL⟩ :=
    cap_subtree_general emit groups heap capStart 4 _ (2*1) vs (by decide) leftSpan run0 leftPC separate aligned (by
      rw [← hleft]
      have := cap_offset_mono (vs.length+left.length) (vs.length+(left.length+right.length)) (by omega); omega)
  rw [← hleft] at runL frameL
  obtain ⟨across, rightPC, rightPos, memRight⟩ := advance_left_to_right groups leftEnd 1 _
    (by decide) (cap_span_node _ _ leftSpan).2 runL.position leftDone
  have runR : CapRun groups heap capStart (vs++left.map heap) (advanceRight leftEnd) (2*1+1) :=
    ⟨rightPos,(right_x30 _).trans runL.counter,(bytes_mem memRight _ _).trans runL.bytes,
      fun n hn => (read_mem memRight _ _).trans (runL.heapRead n hn)⟩
  have e1 : (vs++left.map heap).length=vs.length+left.length := by simp
  obtain ⟨rightEnd, ranRight, rightDone, runRR, frameR⟩ :=
    cap_subtree_general emit groups heap capStart 4 _ (2*1+1) (vs++left.map heap) (by decide) rightSpan runR
      rightPC separate aligned (by
        rw [← hright, e1, show vs.length+left.length+right.length=vs.length+(left.length+right.length) by omega]
        exact fits)
  rw [← hright] at runRR frameR
  obtain ⟨up, finalPC, finalPos, memUp⟩ := advance_right_to_root groups rightEnd _ runRR.position rightDone
  have lists : vs++(left++right).map heap=(vs++left.map heap)++right.map heap := by
    rw [List.map_append, List.append_assoc]
  have e2 : vs.length+(left.length+right.length)=(vs++left.map heap).length+right.length := by rw [e1]; omega
  rw [lists, e2]
  refine ⟨advanceRootExit rightEnd, ?_, finalPC, ⟨finalPos,(root_x30 _).trans runRR.counter,
    (bytes_mem memUp _ _).trans runRR.bytes,fun n hn => (read_mem memUp _ _).trans (runRR.heapRead n hn)⟩, ?_⟩
  · have trace := ((((lookup.next descend).next ranLeft).next across).next ranRight).next up
    have hb : capWalkB groups 1 5 capStart vs.length=14+capWalkB groups (2*1) 4 capStart vs.length+
        capWalkB groups (2*1+1) 4 capStart (vs.length+(capFrontierNodes groups (2*1) (4+3)).length) :=
      cap_walk_b_branch groups 1 4 capStart vs.length mark
    rw [hb]
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

/-- Root form (no node emitted before, countdown 7): the interface of `cap_root` (GroupOpenCapEmit). -/
theorem cap_root_of_emit (emit : EmitCap238) (groups : List Nat) (state : MachineState) (dest : Nat)
    (position : CapPosition groups state 1 dest) (marked : capIsMarked groups 1 8=true)
    (pc : state.pc=0x1a54) (separate : proofBase ≤ dest) (aligned : dest%2=0)
    (fits : dest+capOffset (capFrontierNodes groups 1 8).length+2 ≤ MEMORY_BYTES)
    (counter : state.getReg .x30=7#64) :
    ∃ after, RunsOpeningBlock state after (capWalkB groups 1 5 dest 0+1) ∧
      after.pc=0x1b14 ∧
      CapPosition groups after 1 (dest+capOffset (capFrontierNodes groups 1 8).length) ∧
      (∀ address<2^64, address<dest ∨ dest+capOffset (capFrontierNodes groups 1 8).length ≤ address →
        after.getByte (BitVec.ofNat 64 address)=state.getByte (BitVec.ofNat 64 address)) ∧
      bytesAt after dest (capOffset (capFrontierNodes groups 1 8).length)=
        foldNodes ((capFrontierNodes groups 1 8).map (fun n => readBuffer state (capDigestAddress n) 32)) := by
  have start : CapRun groups (fun n => readBuffer state (capDigestAddress n) 32) dest [] state 1 :=
    ⟨by simpa [capOffset] using position, by simpa using counter,
      by simp [bytesAt, capOffset, fold_nodes_nil], fun n _ => rfl⟩
  obtain ⟨after,r,p,run,frame⟩ := cap_root_general emit groups _ dest state [] Opening.cap_span_root start pc
    marked separate aligned (by simpa using fits)
  refine ⟨after,?_,p,?_,?_,?_⟩
  · simpa using r
  · simpa using run.position
  · simpa using frame
  · simpa using run.bytes

end TwoPermutationPrototype.GroupedOpening
