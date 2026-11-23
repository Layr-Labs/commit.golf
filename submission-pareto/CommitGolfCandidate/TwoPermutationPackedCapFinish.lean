import CommitGolfCandidate.TwoPermutationPackedCapWalk
import CommitGolfCandidate.TwoPermutationPackedCapRootRun
import CommitGolfCandidate.TwoPermutationPackedSearchPaths

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt cap_hash_count_tree cap_hash_count_root)

theorem cap_outside_digest {groups : List Nat} {node : Nat} {before after : MachineState}
    (frame : CapFrame groups node before after) (address : Nat)
    (above : 4096 ≤ address) (bounded : address+4 ≤ 2^61) :
    readBuffer after (8*address) 32 = readBuffer before (8*address) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  simp only [← Nat.mul_add]
  exact frame (address+word) (by omega) (Or.inr (Or.inl (by omega)))

private theorem root_test_memory (state : MachineState) : (capRootTest state).mem = state.mem := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12, MachineState.getReg_setPC,
      Opening.getReg_setReg, show state.getReg .x0 = 0#64 from rfl, root] <;> rfl

/-- One-byte search: u from the marks of leaves 510 and 511 (as `pickU` reads them in memory). -/
def groupPick (groups : List Nat) : Option Nat :=
  if capIsMarked groups 511 0 = false then (if capIsMarked groups 510 0 = false then some 255 else some 511)
  else (if capIsMarked groups 510 0 = false then some 510 else none)

structure CapFinished (oracle : Oracle) (groups : List Nat) (before : MachineState) (pointer claim fuel : Nat) : Prop where
  calls : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).2 ≤ 255+2040
  honestCalls : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).2 ≤ 8*groups.length ∨
    (pointer+capPackedBytes (capFrontierNodes groups 1 8).length = 13824430176+72160 ∧
      (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).2 ≤ 8*groups.length+2040)
  paths : let observed := checkEvaluation oracle (recordRows (execute packedImage fuel before false))
    observed.1.1.exit = .success → ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 →
      ProjectedPath observed.1.2 leaf 8 (capRootAt before leaf) (readBuffer before (8*claim) 32)
  terminates : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).1.1.exit ≠ .unfinished
  honest : ∀ heap, CapHeapCorrect oracle heap → CapContents groups before 1 8 pointer 0 heap →
    readBuffer before (8*claim) 32 = heap 1 →
    before.getReg .x22 = BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length) →
    (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).1.1.exit = .success
  /-- One-byte search: the frontier node u decoded as `w`, which differs from `heap u` only in the top
  doubleword, where trial g restores it. -/
  nearHonest : ∀ heap u w, CapHeapCorrect oracle heap →
    CapContents groups before 1 8 pointer 0 (fun n => if n = u then w else heap n) →
    readBuffer before (8*claim) 32 = heap 1 →
    before.getReg .x22 = BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length) →
    pointer+capPackedBytes (capFrontierNodes groups 1 8).length = 13824430176+72160 →
    groupPick groups = some u → (u = 255 → capIsMarked groups 127 2 = true) →
    (∀ k < 3, w.extractLsb' (64*k) 64 = (heap u).extractLsb' (64*k) 64) →
    (∃ g, 1 ≤ g ∧ g < 256 ∧ replaceHalfword (w.extractLsb' 192 64) 2
      (patchHalf (extractHalfword (w.extractLsb' 192 64) 2) (BitVec.ofNat 64 g)) = (heap u).extractLsb' 192 64) →
    (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).1.1.exit = .success

theorem group_pick_node {groups : List Nat} {u : Nat} (picked : groupPick groups = some u) :
    u = 255 ∨ u = 510 ∨ u = 511 := by
  unfold groupPick at picked
  split at picked <;> split at picked <;> cases picked <;> simp

theorem mark_word_zero (groups : List Nat) (n : Nat) (h : Opening.capHeight n = 0) :
    Opening.markWord groups n = 0 ↔ capIsMarked groups n 0 = false := by
  unfold Opening.markWord
  rw [h]
  cases capIsMarked groups n 0 <;> decide

/-- The search's pick from memory is the pick from the groups. -/
theorem pick_of_marks (groups : List Nat) (E : MachineState)
    (marks : ∀ n, 0 < n → n < 512 → memoryView E (512+n) = Opening.markWord groups n) :
    pickU E = groupPick groups := by
  have m510 : markWord E 510 = Opening.markWord groups 510 := marks 510 (by decide) (by decide)
  have m511 : markWord E 511 = Opening.markWord groups 511 := marks 511 (by decide) (by decide)
  have z510 := mark_word_zero groups 510 (by decide)
  have z511 := mark_word_zero groups 511 (by decide)
  unfold pickU groupPick
  rw [m510, m511]
  by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false
  · rw [if_pos (z511.mpr a), if_pos (z510.mpr b), if_pos a, if_pos b]
  · rw [if_pos (z511.mpr a), if_neg (fun h => b (z510.mp h)), if_pos a, if_neg b]
  · rw [if_neg (fun h => a (z511.mp h)), if_pos (z510.mpr b), if_neg a, if_pos b]
  · rw [if_neg (fun h => a (z511.mp h)), if_neg (fun h => b (z510.mp h)), if_neg a, if_neg b]

/-- The spine above u is marked (for the survivors of u's siblings). -/
theorem pick_spine (groups : List Nat) (u : Nat) (picked : groupPick groups = some u)
    (above : u = 255 → capIsMarked groups 127 2 = true) :
    ∀ i, i < depthOf u → capIsMarked groups (2^(i+1)-1) (8-i) = true := by
  have up (n h : Nat) (m : capIsMarked groups n h = true) : capIsMarked groups (n/2) (h+1) = true := by
    simp only [capIsMarked, List.any_eq_true, beq_iff_eq] at m ⊢
    obtain ⟨g, member, at_⟩ := m
    exact ⟨g, member, by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, at_]⟩
  have chain (n h : Nat) (m : capIsMarked groups n h = true) :
      ∀ t, capIsMarked groups (n/2^t) (h+t) = true := by
    intro t
    induction t with
    | zero => simpa using m
    | succ t ih =>
      have := up _ _ ih
      rwa [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at this
  have top255 : capIsMarked groups 255 1 = true ∨ u = 255 := by
    unfold groupPick at picked
    by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false <;>
      simp [a, b] at picked
    · right; exact picked.symm
    · left
      have := up 510 0 (by simpa using b)
      simpa using this
    · left
      have := up 511 0 (by simpa using a)
      simpa using this
  intro i hi
  rcases top255 with marked | is255
  · have node := group_pick_node picked
    have d8 : depthOf u ≤ 8 := depth_le u
    have := chain 255 1 marked (7-i)
    have i8 : i < 8 := by omega
    have e1 : 255/2^(7-i) = 2^(i+1)-1 := by interval_cases i <;> decide
    rw [e1, show 1+(7-i) = 8-i by omega] at this
    by_cases low : i ≤ 7
    · exact this
    · omega
  · subst is255
    have m := above rfl
    norm_num [depthOf] at hi
    have := chain 127 2 m (6-i)
    have e1 : 127/2^(6-i) = 2^(i+1)-1 := by interval_cases i <;> decide
    rw [e1, show 2+(6-i) = 8-i by omega] at this
    exact this

/-- A heap correct everywhere is correct below `node` for any heap that agrees with it on that subtree. -/
theorem heap_correct_at (oracle : Oracle) (groups : List Nat) (heap heap' : Nat → BitVec 256)
    (correct : CapHeapCorrect oracle heap) :
    ∀ h node, Opening.CapSpan node h → (∀ t, t ≤ h → ∀ n, n/2^t = node → heap' n = heap n) →
      CapHeapCorrectAt oracle groups heap' node h := by
  intro h
  induction h with
  | zero => intro _ _ _; simp [CapHeapCorrectAt]
  | succ h ih =>
    intro node span agree
    obtain ⟨leftSpan, rightSpan⟩ := Opening.cap_span_children node h span
    have positive := (Opening.cap_span_node node (h+1) span).1
    have internal := Opening.cap_span_is_internal node h span
    simp only [CapHeapCorrectAt]
    intro _
    have under (child : Nat) (which : child = 2*node ∨ child = 2*node+1) :
        ∀ t, t ≤ h → ∀ n, n/2^t = child → heap' n = heap n := by
      intro t ht n at_
      apply agree (t+1) (by omega) n
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, at_]
      omega
    refine ⟨?_, ih _ leftSpan (under _ (Or.inl rfl)), ih _ rightSpan (under _ (Or.inr rfl))⟩
    rw [agree 0 (by omega) node (by simp), agree 1 (by omega) (2*node+1) (by simp <;> omega),
      agree 1 (by omega) (2*node) (by simp <;> omega)]
    exact correct node positive internal

/-- u is a survivor of the walk when the spine above it is marked. -/
theorem node_survivor (groups : List Nat) (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511)
    (marks : ∀ i, i < depthOf u → capIsMarked groups (2^(i+1)-1) (8-i) = true) :
    CapSurvivor groups 1 8 u (8-depthOf u) := by
  rcases node with rfl | rfl | rfl
  · exact spine_lift groups 255 1 7 (by decide) (fun i hi => marks i (by simp [depthOf]; omega))
      (CapSurvivor.self _ _ _)
  · have mk : capIsMarked groups 255 (0+1) = true := marks 7 (by simp [depthOf])
    have base := survivor_left groups 255 0 mk
    exact spine_lift groups 510 0 7 (by decide) (fun i hi => marks i (by simp [depthOf]; omega)) base
  · exact spine_lift groups 511 0 8 (by decide) (fun i hi => marks i (by simp [depthOf]; omega))
      (CapSurvivor.self _ _ _)

/-- The siblings of u's path are survivors of the walk when the spine above u is marked; u is not below them. -/
theorem sibling_survivor (groups : List Nat) (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511)
    (marks : ∀ i, i < depthOf u → capIsMarked groups (2^(i+1)-1) (8-i) = true) (i : Nat) (hi : i < depthOf u) :
    ∃ hm, CapSurvivor groups 1 8 ((u/2^i) ^^^ 1) hm ∧ Opening.CapSpan ((u/2^i) ^^^ 1) hm ∧
      ∀ t, t ≤ hm → u/2^t ≠ (u/2^i) ^^^ 1 := by
  have spine (j : Nat) (hj : j ≤ 7) (c : Nat) (which : c = 2*(2^(j+1)-1) ∨ c = 2*(2^(j+1)-1)+1)
      (mk : ∀ i, i ≤ j → capIsMarked groups (2^(i+1)-1) (8-i) = true) : CapSurvivor groups 1 8 c (7-j) := by
    have mkj : capIsMarked groups (2^(j+1)-1) ((7-j)+1) = true := by
      rw [show (7-j)+1 = 8-j by omega]; exact mk j (le_refl _)
    have base : CapSurvivor groups (2^(j+1)-1) ((7-j)+1) c (7-j) := by
      rcases which with rfl | rfl
      · exact survivor_left groups _ _ mkj
      · exact survivor_up groups _ _ _ _ mkj (CapSurvivor.self _ _ _)
    rw [show (7-j)+1 = 8-j by omega] at base
    exact spine_lift groups c (7-j) j (by omega) (fun i hi => mk i (by omega)) base
  rcases node with rfl | rfl | rfl <;> simp [depthOf] at hi marks <;> interval_cases i
  · exact ⟨1, spine 6 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨2, spine 5 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨3, spine 4 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨4, spine 3 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨5, spine 2 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨6, spine 1 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨7, spine 0 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨0, spine 7 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨1, spine 6 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨2, spine 5 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨3, spine 4 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨4, spine 3 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨5, spine 2 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨6, spine 1 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨7, spine 0 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨0, spine 7 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨1, spine 6 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨2, spine 5 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨3, spine 4 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨4, spine 3 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨5, spine 2 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨6, spine 1 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩
  · exact ⟨7, spine 0 (by decide) _ (by decide) (fun k hk => marks k (by omega)),
      ⟨by decide, by decide, by decide⟩, by decide⟩

theorem execute_prepared_cap_suffix (codec : FrontierKernel) (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (position : CapPosition groups before 1 pointer 0)
    (pc : before.pc = 0x147c) (claimReg : before.getReg .x9 = wordAddress claim)
    (claimAbove : 4096 ≤ claim) (claimBound : claim+4 ≤ 2^33)
    (room : pointer+capPackedBytes (capFrontierNodes groups 1 8).length ≤ MEMORY_BYTES)
    (fuelBound : 70000 ≤ fuel) : CapFinished oracle groups before pointer claim fuel := by
  obtain ⟨walk⟩ := execute_cap_subtree codec oracle groups before 1 8 pointer 0 position pc Opening.cap_span_root
    (by simpa using room)
  have steps : walk.segment.steps ≤ 36281 := walk.steps
  have leftFuel : 18 ≤ fuel-walk.segment.steps := by omega
  have observed := walk.segment.checked (fuel-walk.segment.steps)
  rw [show walk.segment.steps+(fuel-walk.segment.steps) = fuel by omega] at observed
  have hashCount := walk.calls.trans (cap_hash_count_tree groups 1 8)
  have groupCount := walk.calls.trans (cap_hash_count_root groups)
  have loadedClaim := cap_outside_digest walk.frame claim claimAbove (by omega)
  by_cases done : walk.done = true
  · have actual := walk.position done
    have finishedPC : walk.state.pc = 0x1528 := by simpa [done] using walk.pc
    let W := walk.state
    let tested := capRootTest W
    have testedPC : tested.pc = 0x1560 := by
      rw [cap_root_post _ finishedPC, actual.heap]
      rfl
    have testedRoots : tested.getReg .x25 = wordAddress 2048 :=
      (root_test_register _ .x25 (by decide)).trans actual.context.controls.roots
    have testedClaim : tested.getReg .x9 = wordAddress claim :=
      (root_test_register _ .x9 (by decide)).trans ((walk.stable .x9 (by decide)).trans claimReg)
    have testedMarks : tested.getReg .x26 = 4096#64 :=
      (root_test_register _ .x26 (by decide)).trans actual.context.controls.markBase
    have testedEnd : tested.getReg .x22 = before.getReg .x22 :=
      (root_test_register _ .x22 (by decide)).trans (walk.stable .x22 (by decide))
    have testedCursor : tested.getReg .x21 = BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length) := by
      rw [root_test_register _ .x21 (by decide), actual.proof, Nat.zero_add]
    have testMem : tested.mem = W.mem := root_test_memory W
    have slotTested (n : Nat) (hn : n < 512) : capRootAt tested n = capRootAt W n := by
      unfold capRootAt
      exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun testMem _)
    have claimStayed : readBuffer tested (8*claim) 32 = readBuffer before (8*claim) 32 :=
      (read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun testMem _)).trans loadedClaim
    let testSeg : Segment oracle W tested := Segment.ordinary oracle 2 2 (execute_cap_root_test W finishedPC)
    have run1 := segment_run oracle testSeg (fuel-walk.segment.steps) (by show 2 ≤ _; omega)
    rw [show testSeg.steps = 2 from rfl] at run1
    rw [run1] at observed
    have lengthOK (ending : before.getReg .x22 =
        BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length)) :
        tested.getReg .x21 = tested.getReg .x22 := by
      rw [testedCursor, testedEnd, ending]
    have heapRootOf (heap : Nat → BitVec 256) (model : CapHeapCorrect oracle heap)
        (contents : CapContents groups before 1 8 pointer 0 heap) : capRootAt tested 1 = heap 1 :=
      (slotTested 1 (by decide)).trans (walk.realizes done heap model contents)
    rcases execute_root_check tested claim testedPC testedRoots testedClaim claimBound with
      ⟨lenNe, rejRun⟩ | ⟨lenEq, rootEq, result, accepted, calls0, accRun⟩ |
        ⟨lenEq, rootNe, E, c, cb, Epc, Emem, Eregs, Erun⟩
    · -- length mismatch: reject
      rw [show fuel-walk.segment.steps-2 = 4+(fuel-walk.segment.steps-2-4) by omega, rejRun, record_rows_pure,
        check_evaluation_pure] at observed
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [observed]; simpa [testSeg, Segment.ordinary] using hashCount.trans (by omega : 255 ≤ 255+2040)
      · left; rw [observed]; simpa [testSeg, Segment.ordinary] using groupCount
      · dsimp only; rw [observed]; intro impossible; simp [Execution.charge] at impossible
      · rw [observed]; simp [Execution.charge]
      · intro _ _ _ _ ending; exact absurd (lengthOK ending) lenNe
      · intro _ _ _ _ _ _ ending; exact absurd (lengthOK ending) lenNe
    · -- the root matches: accept
      rw [show fuel-walk.segment.steps-2 = 16+(fuel-walk.segment.steps-2-16) by omega, accRun, record_rows_pure,
        check_evaluation_pure] at observed
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [observed]; simpa [testSeg, Segment.ordinary, calls0] using hashCount.trans (by omega : 255 ≤ 255+2040)
      · left; rw [observed]; simpa [testSeg, Segment.ordinary, calls0] using groupCount
      · dsimp only
        rw [observed]
        intro _ leaf active low high
        have final := (slotTested 1 (by decide)).symm.trans (rootEq.trans claimStayed)
        have path := walk.authentic done leaf active low high (by omega)
        rw [final] at path
        simpa [testSeg, Segment.ordinary] using path
      · rw [observed]; simp [Execution.charge]; intro bad; rw [bad] at accepted; cases accepted
      · intro _ _ _ _ _; rw [observed]; simpa [Execution.charge] using accepted
      · intro _ _ _ _ _ _ _ _ _ _ _ _; rw [observed]; simpa [Execution.charge] using accepted
    · -- the root differs: the search
      let checkSeg : Segment oracle tested E := Segment.ordinary oracle c c Erun
      have run2 := segment_run oracle checkSeg (fuel-walk.segment.steps-2) (by show c ≤ _; omega)
      rw [show checkSeg.steps = c from rfl] at run2
      rw [run2] at observed
      have Eregs' (r : Reg) (a : r ≠ .x29) (b : r ≠ .x30) : E.getReg r = tested.getReg r := Eregs r a b
      have Emarks : E.getReg .x26 = 4096#64 := (Eregs' .x26 (by decide) (by decide)).trans testedMarks
      have Eroots : E.getReg .x25 = 16384#64 := by rw [Eregs' .x25 (by decide) (by decide), testedRoots]; rfl
      have Eclaim : E.getReg .x9 = wordAddress claim := (Eregs' .x9 (by decide) (by decide)).trans testedClaim
      have Eend : E.getReg .x22 = before.getReg .x22 := (Eregs' .x22 (by decide) (by decide)).trans testedEnd
      have EmemW : E.mem = W.mem := Emem.trans testMem
      have slotE (n : Nat) (hn : n < 512) : capRootAt E n = capRootAt W n := by
        unfold capRootAt
        exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun EmemW _)
      have claimE : readBuffer E (8*claim) 32 = readBuffer before (8*claim) 32 :=
        (read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun EmemW _)).trans loadedClaim
      have pickE : pickU E = groupPick groups := by
        apply pick_of_marks
        intro n pos bound
        rw [view_of_mem EmemW]
        exact actual.context.marked n pos bound
      obtain ⟨sterm, scalls, saccept, scomplete, szero⟩ :=
        search_facts oracle E claim Epc Emarks Eroots Eclaim claimAbove claimBound
          (fuel-walk.segment.steps-2-c) (by omega)
      have walkLen : walk.segment.rows.length ≤ 8*groups.length := groupCount
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [observed]
        simp only [testSeg, checkSeg, Segment.ordinary, List.length_nil, Nat.zero_add]
        have := hashCount
        omega
      · rw [observed]
        simp only [testSeg, checkSeg, Segment.ordinary, List.length_nil, Nat.zero_add]
        by_cases atEnd : E.getReg .x22 = searchEnd
        · right
          have small : pointer+capPackedBytes (capFrontierNodes groups 1 8).length < 2^64 := by
            have : MEMORY_BYTES < 2^64 := by decide
            omega
          have eqv := lenEq.trans
            ((Eregs' .x22 (by decide) (by decide)).symm.trans atEnd)
          rw [testedCursor] at eqv
          have nat := congrArg BitVec.toNat eqv
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at nat
          refine ⟨by rw [nat], by omega⟩
        · left
          rw [szero atEnd]
          omega
      · dsimp only
        rw [observed]
        intro success leaf active low high
        have searched : (checkEvaluation oracle (recordRows (execute packedImage
            (fuel-walk.segment.steps-2-c) E false))).1.1.exit = .success := by
          simpa [Execution.charge] using success
        obtain ⟨_, u, g, picked, glo, ghi, root, member⟩ := saccept searched
        rw [pickE] at picked
        have node := group_pick_node picked
        have unmarked : u = 255 → capIsMarked groups 510 0 = false ∧ capIsMarked groups 511 0 = false := by
          intro h; subst h
          unfold groupPick at picked
          by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false <;>
            simp_all
        have unmarkedLeaf : u ≠ 255 → capIsMarked groups u 0 = false := by
          intro h
          unfold groupPick at picked
          by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false <;>
            simp_all <;> (subst picked; assumption)
        let rows := walk.segment.rows ++ (testSeg.rows ++ (checkSeg.rows ++
          (checkEvaluation oracle (recordRows (execute packedImage
            (fuel-walk.segment.steps-2-c) E false))).1.2))
        have survivors : ∀ m hm, CapSurvivor groups 1 8 m hm → ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 →
            leaf/2^hm = m → ProjectedPath rows leaf hm (capRootAt before leaf) (capRootAt E m) := by
          intro m hm surv leaf' active' low' high' under
          have p := (walk.survivors done m hm surv).1 leaf' active' low' high' under
          have span := (CapSurvivor.span surv Opening.cap_span_root).1
          rw [slotE m (Opening.cap_span_node _ _ span).2]
          exact p.mono (fun _ found => List.mem_append_left _ found)
        have climbIn : ∀ row ∈ (climbFrom oracle (capRootAt E) (depthOf u) u (patchedSlot E u g)).1, row ∈ rows := by
          intro row found
          exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member row found)))
        have path := search_binding oracle groups (capRootAt E) rows (capRootAt before) u node unmarked unmarkedLeaf
          survivors (patchedSlot E u g) climbIn leaf active low high
        have rootEq : (climbFrom oracle (capRootAt E) (depthOf u) u (patchedSlot E u g)).2 =
            readBuffer before (8*claim) 32 := root.trans claimE
        rw [rootEq] at path
        simpa [rows, testSeg, checkSeg, Segment.ordinary] using path
      · rw [observed]; simpa [Execution.charge] using sterm
      · intro heap model contents rootClaim _
        have := heapRootOf heap model contents
        exact absurd (this.trans (rootClaim.symm.trans claimStayed.symm)) rootNe
      · intro heap u w model contents rootClaim ending atEnd picked above low top
        have node := group_pick_node picked
        have hu : u < 512 := by rcases node with rfl | rfl | rfl <;> decide
        have marks := pick_spine groups u picked above
        let heap' := fun n => if n = u then w else heap n
        have Eend' : E.getReg .x22 = searchEnd := by rw [Eend, ending, atEnd]
        have wSlot : capRootAt E u = w := by
          rw [slotE u hu]
          have surv := node_survivor groups u node marks
          have loc : CapHeapCorrectAt oracle groups heap' u (8-depthOf u) := by
            rcases node with rfl | rfl | rfl
            · -- 255 is unmarked: no internal condition applies
              simp only [depthOf, CapHeapCorrectAt]
              intro marked
              exfalso
              unfold groupPick at picked
              have ab : capIsMarked groups 511 0 = false ∧ capIsMarked groups 510 0 = false := by
                by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false <;>
                  simp [a, b] at picked
                exact ⟨a, b⟩
              obtain ⟨a, b⟩ := ab
              simp only [capIsMarked, List.any_eq_true, List.any_eq_false, beq_iff_eq] at marked a b
              obtain ⟨g, member, at_⟩ := marked
              have h1 := a g member
              have h2 := b g member
              simp at h1 h2 at_
              omega
            · simp [depthOf, CapHeapCorrectAt]
            · simp [depthOf, CapHeapCorrectAt]
          have := (walk.survivors done u _ surv).2 heap' loc contents
          simpa [heap'] using this
        obtain ⟨g, glo, ghi, gtop⟩ := top
        have patched : patchedSlot E u g = heap u :=
          patched_slot_eq E u g hu (heap u) (fun k hk => by rw [wSlot]; exact low k hk) (by rw [wSlot]; exact gtop)
        have sibs : ∀ i, i < depthOf u → capRootAt E ((u/2^i) ^^^ 1) = heap ((u/2^i) ^^^ 1) := by
          intro i hi
          obtain ⟨hm, surv, span, notBelow⟩ := sibling_survivor groups u node marks i hi
          have loc := heap_correct_at oracle groups heap heap' model hm _ span (by
            intro t ht n at_
            have : n ≠ u := by rintro rfl; exact notBelow t ht at_
            simp [heap', this])
          have := (walk.survivors done _ hm surv).2 heap' loc contents
          rw [slotE _ (Opening.cap_span_node _ _ span).2, this]
          have ne : (u/2^i) ^^^ 1 ≠ u := by
            intro same
            exact notBelow 0 (Nat.zero_le _) (by simpa using same.symm)
          simp [heap', ne]
        have correct : ∀ p, 0 < p → p < 256 → heap p = pad238 (oracle.compression (heap (2*p+1) ++ heap (2*p))) :=
          fun p pos bound => model p pos bound
        have trial := honest_trial oracle heap correct E u g node sibs patched
        have good := scomplete Eend' u (pickE.trans picked) ⟨g, glo, ghi, by rw [trial, claimE, rootClaim]⟩
        rw [observed]
        simpa [Execution.charge] using good
  · have falseDone : walk.done = false := Bool.eq_false_iff.mpr done
    have failed : walk.state.pc = 0x15b0 := by simpa [falseDone] using walk.pc
    have finalRun : execute packedImage (fuel-walk.segment.steps) walk.state false =
        pure ⟨.failure,rejectState walk.state,3,0⟩ := by
      rw [show fuel-walk.segment.steps = 3+(fuel-walk.segment.steps-3) by omega]
      exact execute_reject _ failed _
    rw [finalRun, record_rows_pure, check_evaluation_pure] at observed
    have unavailable (finish : before.getReg .x22 =
        BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length)) : False := by
      have fit : MEMORY_BYTES < 2^64 := by decide
      have enough : pointer+capPackedBytes (0+(capFrontierNodes groups 1 8).length) ≤ (before.getReg .x22).toNat := by
        rw [finish, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.zero_add]
      exact done (walk.available enough)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [observed]
      simpa using hashCount.trans (by omega : 255 ≤ 255+2040)
    · left
      rw [observed]
      simpa using groupCount
    · dsimp only
      rw [observed]
      intro impossible
      cases impossible
    · rw [observed]
      exact (show Exit.failure ≠ Exit.unfinished by decide)
    · intro _ _ _ _ finish
      exact (unavailable finish).elim
    · intro _ _ _ _ _ _ finish
      exact (unavailable finish).elim

end TwoPermutationPrototype.Packed.Checker
