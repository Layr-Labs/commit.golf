import CommitGolfCandidate.TwoPermutationPackedSearchRun

/-! # One-byte search: the trial loop

Trial g writes g into bits 230..237 of u's slot and climbs to the root. The slot u holds `patchedSlot E u g`: the
entry state's slot with the halfword at byte 28 replaced by `patchHalf h0 g`, where `h0` is the entry halfword; the
siblings of u's ancestors keep the entry values. So trial g's rows and root are those of
`climbFrom oracle (capRootAt E) (depthOf u) u (patchedSlot E u g)`. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- Levels from u to the root. -/
def depthOf (u : Nat) : Nat := if 256 ≤ u then 8 else 7

/-- The entry state with trial g's halfword in u's slot. -/
def patchedState (E : MachineState) (u g : Nat) : MachineState :=
  E.setHalfword (topHalf u) (patchHalf (E.getHalfword (topHalf u)) (BitVec.ofNat 64 g))

def patchedSlot (E : MachineState) (u g : Nat) : BitVec 256 := capRootAt (patchedState E u g) u

/-- Trial g's climb: its rows and its root. -/
def trialClimb (oracle : Oracle) (E : MachineState) (u g : Nat) : List PublicRow × BitVec 256 :=
  climbFrom oracle (capRootAt E) (depthOf u) u (patchedSlot E u g)

/-- The word holding bytes 24..31 of slot `u`. -/
abbrev topWord (u : Nat) : Nat := 2048+4*u+3

/-! ### Bits of the patched halfword -/

theorem extract_replace (w : Word) (h : BitVec 16) : extractHalfword (replaceHalfword w 2 h) 2 = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [extractHalfword, replaceHalfword]

theorem replace_replace (w : Word) (h k : BitVec 16) :
    replaceHalfword (replaceHalfword w 2 h) 2 k = replaceHalfword w 2 k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceHalfword]

theorem patch_patch (h : BitVec 16) (a b : Word) : patchHalf (patchHalf h a) b = patchHalf h b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [patchHalf, signExtend12]

/-! ### The halfword of a slot in memory -/

theorem top_half_align (u : Nat) (hu : u < 512) :
    alignToDword (topHalf u) = wordAddress (topWord u) ∧ byteOffset (topHalf u) / 2 = 2 := by
  have a := arm_align (8*(topWord u)) 4 (by omega) (by decide)
  have b := arm_byte_offset (8*(topWord u)) 4 (by omega) (by decide)
  have e : 8*topWord u+4 = 16384+32*u+28 := by unfold topWord; omega
  rw [e] at a b
  exact ⟨a, by rw [b]⟩

theorem get_top_half (s : MachineState) (u : Nat) (hu : u < 512) :
    s.getHalfword (topHalf u) = extractHalfword (memoryView s (topWord u)) 2 := by
  obtain ⟨a, b⟩ := top_half_align u hu
  simp only [MachineState.getHalfword, a, b, memoryView]

theorem set_top_half (s : MachineState) (u : Nat) (hu : u < 512) (v : BitVec 16) (word : Nat) (bound : word < 2^61) :
    memoryView (s.setHalfword (topHalf u) v) word =
      if word = topWord u then replaceHalfword (memoryView s (topWord u)) 2 v else memoryView s word := by
  obtain ⟨a, b⟩ := top_half_align u hu
  simp only [MachineState.setHalfword, a, b, memoryView]
  by_cases same : word = topWord u
  · subst same
    rw [if_pos rfl, MachineState.getMem_setMem_eq]
  · rw [if_neg same, MachineState.getMem_setMem_ne]
    unfold wordAddress
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    have tw : topWord u = 2048+4*u+3 := rfl
    omega

/-! ### One trial -/

/-- At the start of trial g: ready, and memory is the entry's except u's ancestors' slots and u's top word, which
holds the previous trial's halfword. -/
structure TrialInv (E s : MachineState) (u g claim : Nat) : Prop where
  ready : TrialReady s u g claim
  low : 1 ≤ g
  high : g < 256
  node : u = 255 ∨ u = 510 ∨ u = 511
  words : ∀ word < 2^61, (∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) word) → word ≠ topWord u →
    memoryView s word = memoryView E word
  top : memoryView s (topWord u) = if g = 1 then memoryView E (topWord u)
    else replaceHalfword (memoryView E (topWord u)) 2 (patchHalf (E.getHalfword (topHalf u)) (BitVec.ofNat 64 (g-1)))
  claimLow : 4096 ≤ claim
  claimHigh : claim+4 ≤ 2^33

/-- After a mismatching trial g, at word 1217. -/
structure TrialMiss (E s : MachineState) (u g claim : Nat) : Prop where
  pc : s.pc = spc 1217
  node : s.getReg .x18 = BitVec.ofNat 64 u
  trial : s.getReg .x19 = BitVec.ofNat 64 g
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  roots : s.getReg .x25 = 16384#64
  commitment : s.getReg .x9 = wordAddress claim
  words : ∀ word < 2^61, (∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) word) →
    memoryView s word = memoryView (patchedState E u g) word

theorem depth_range (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) :
    1 ≤ depthOf u ∧ 2^(depthOf u) ≤ u ∧ u < 2^(depthOf u+1) := by
  rcases node with rfl | rfl | rfl <;> decide

/-- Slot words of u and of the siblings of its ancestors are not slot words of its proper ancestors. -/
theorem off_ancestors (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) (m : Nat)
    (which : m = u ∨ ∃ i, i < depthOf u ∧ m = (u/2^i) ^^^ 1) (j : Nat) (small : j < 4) :
    ∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) (2048+4*m+j) := by
  intro i lo hi
  unfold SlotWord
  rcases which with rfl | ⟨k, kb, rfl⟩
  · rcases node with rfl | rfl | rfl <;> simp only [depthOf] at hi <;> norm_num at hi <;>
      interval_cases i <;> first | omega | (norm_num <;> omega)
  · rcases node with rfl | rfl | rfl <;> simp only [depthOf] at hi kb <;> norm_num at hi kb <;>
      interval_cases i <;> interval_cases k <;> first | omega | (norm_num <;> omega)

theorem sib_bound (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) (i : Nat) (small : i < depthOf u) :
    (u/2^i) ^^^ 1 < 512 := by
  rcases node with rfl | rfl | rfl <;> simp only [depthOf] at small <;> norm_num at small <;>
    interval_cases i <;> decide

theorem sib_not_top (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) (i : Nat) (small : i < depthOf u)
    (j : Nat) (jsmall : j < 4) : 2048+4*((u/2^i) ^^^ 1)+j ≠ topWord u := by
  unfold topWord
  rcases node with rfl | rfl | rfl <;> simp only [depthOf] at small <;> norm_num at small <;>
    interval_cases i <;> first | omega | (norm_num <;> omega)

theorem patched_view (E : MachineState) (u g : Nat) (hu : u < 512) (word : Nat) (bound : word < 2^61)
    (other : word ≠ topWord u) : memoryView (patchedState E u g) word = memoryView E word := by
  unfold patchedState
  rw [set_top_half E u hu _ word bound, if_neg other]

/-- Trial g from its invariant: the rows and the root of `trialClimb`, then accept (1214) on a match or
`TrialMiss` (1217). -/
theorem trial_step (oracle : Oracle) (E s : MachineState) (u g claim : Nat) (inv : TrialInv E s u g claim) :
    ∃ (t : MachineState) (seg : Segment oracle s t), seg.rows = (trialClimb oracle E u g).1 ∧
      seg.steps ≤ 116 ∧
      ((trialClimb oracle E u g).2 = readBuffer E (8*claim) 32 → t.pc = spc 1214) ∧
      ((trialClimb oracle E u g).2 ≠ readBuffer E (8*claim) 32 → TrialMiss E t u g claim) := by
  have hu : u < 512 := by rcases inv.node with rfl | rfl | rfl <;> decide
  obtain ⟨dlo, dpow, dhi⟩ := depth_range u inv.node
  obtain ⟨hhop, hpc, hmem, hx6, hregs⟩ := trial_head s inv.ready hu
  let h := trialHead s
  -- the head leaves the patched entry state outside the ancestors
  have headView : ∀ word < 2^61, (∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) word) →
      memoryView h word = memoryView (patchedState E u g) word := by
    intro word bound outside
    rw [view_of_mem hmem, set_top_half s u hu _ word bound]
    unfold patchedState
    rw [set_top_half E u hu _ word bound]
    by_cases top : word = topWord u
    · rw [if_pos top, if_pos top, get_top_half s u hu, inv.top]
      by_cases first : g = 1
      · rw [if_pos first, get_top_half E u hu]
      · rw [if_neg first, extract_replace, replace_replace, patch_patch]
    · rw [if_neg top, if_neg top]
      exact inv.words word bound outside top
  have ready : ClimbReady h u := by
    refine ⟨hpc, hx6, ?_, ?_, ?_, ?_, by rcases inv.node with rfl | rfl | rfl <;> decide, hu⟩
    · rw [hregs .x25 (by decide) (by decide) (by decide) (by decide), inv.ready.roots]
    · rw [hregs .x5 (by decide) (by decide) (by decide) (by decide), inv.ready.selector]
    · rw [hregs .x11 (by decide) (by decide) (by decide) (by decide), inv.ready.size]
    · rw [hregs .x13 (by decide) (by decide) (by decide) (by decide), inv.ready.primitive]
  have slotOf (m : Nat) (which : m = u ∨ ∃ i, i < depthOf u ∧ m = (u/2^i) ^^^ 1) (mb : m < 512) :
      capRootAt h m = capRootAt (patchedState E u g) m := by
    unfold capRootAt
    apply read_digest_congr _ _ _ (by omega)
    intro j small
    simp only [← Nat.mul_add]
    exact headView _ (by omega) (off_ancestors u inv.node m which j small)
  have value : capRootAt h u = patchedSlot E u g := slotOf u (Or.inl rfl) hu
  have sibs : ∀ i, i < depthOf u → capRootAt h ((u/2^i) ^^^ 1) = capRootAt E ((u/2^i) ^^^ 1) := by
    intro i small
    have mb : (u/2^i) ^^^ 1 < 512 := sib_bound u inv.node i small
    rw [slotOf _ (Or.inr ⟨i, small, rfl⟩) mb]
    unfold capRootAt
    apply read_digest_congr _ _ _ (by omega)
    intro j jsmall
    simp only [← Nat.mul_add]
    apply patched_view E u g hu _ (by omega)
    exact sib_not_top u inv.node i small j jsmall
  obtain ⟨t, climb, rows, steps, cycles, tpc, troot, tregs, tframe⟩ :=
    climb_run oracle (capRootAt E) (depthOf u) u (patchedSlot E u g) h ready dlo dpow dhi value sibs
  have keep (r : Reg) (a6 : r ≠ .x6) (a7 : r ≠ .x7) (a10 : r ≠ .x10) (a12 : r ≠ .x12) (a28 : r ≠ .x28)
      (a29 : r ≠ .x29) (a31 : r ≠ .x31) : t.getReg r = s.getReg r :=
    (tregs r a6 a7 a10 a12 a31).trans (hregs r a6 a7 a28 a29)
  have t25 : t.getReg .x25 = 16384#64 := (keep .x25 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans inv.ready.roots
  have t9 : t.getReg .x9 = wordAddress claim := (keep .x9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans inv.ready.commitment
  have tView : ∀ word < 2^61, (∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) word) →
      memoryView t word = memoryView (patchedState E u g) word := by
    intro word bound outside
    rw [tframe word bound outside, headView word bound outside]
  have claimOutside (j : Nat) (small : j < 4) : ∀ i, 1 ≤ i → i ≤ depthOf u → ¬ SlotWord (u/2^i) (claim+j) := by
    intro i lo hi
    unfold SlotWord
    have : u/2^i ≤ u := Nat.div_le_self _ _
    have := inv.claimLow
    omega
  have claimSame : readBuffer t (8*claim) 32 = readBuffer E (8*claim) 32 := by
    apply read_digest_congr _ _ _ (by have := inv.claimHigh; omega)
    intro j small
    simp only [← Nat.mul_add]
    show memoryView t (claim+j) = memoryView E (claim+j)
    rw [tView _ (by have := inv.claimHigh; omega) (claimOutside j small)]
    apply patched_view E u g hu _ (by have := inv.claimHigh; omega)
    unfold topWord
    have := inv.claimLow
    omega
  obtain ⟨t2, c2, c2b, chop, cmem, cregs, cpc⟩ := search_compare_scan t 4 (le_refl _)
    (by rw [tpc]) t25 ⟨claim, inv.claimHigh, t9⟩
  have words4 : (∀ i : Fin 4, 4-4 ≤ i.val → rootWordMatches t i) ↔ (trialClimb oracle E u g).2 = readBuffer E (8*claim) 32 := by
    rw [← claimSame, trialClimb, ← troot]
    simp only [Nat.sub_self, Nat.zero_le, forall_const]
    exact root_words_iff t claim (by rw [t25]; rfl) t9
  let head : Segment oracle s h := Segment.ordinary oracle 8 8 hhop
  let compare : Segment oracle t t2 := Segment.ordinary oracle c2 c2 chop
  refine ⟨t2, (head.append climb).append compare, ?_, ?_, ?_, ?_⟩
  · show ([] ++ climb.rows) ++ [] = _
    rw [rows]
    simp [trialClimb]
  · show 8 + climb.steps + c2 ≤ 116
    rw [steps]
    have : depthOf u ≤ 8 := by unfold depthOf; split <;> omega
    omega
  · intro matched
    rw [cpc, if_pos (words4.mpr matched)]
  · intro differs
    have t2regs (r : Reg) (a6 : r ≠ .x6) (a7 : r ≠ .x7) (a10 : r ≠ .x10) (a12 : r ≠ .x12) (a28 : r ≠ .x28)
        (a29 : r ≠ .x29) (a30 : r ≠ .x30) (a31 : r ≠ .x31) : t2.getReg r = s.getReg r :=
      (cregs r a29 a30).trans (keep r a6 a7 a10 a12 a28 a29 a31)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cpc, if_neg (fun h => differs (words4.mp h))]
    · rw [t2regs .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.node]
    · rw [t2regs .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.trial]
    · rw [t2regs .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.selector]
    · rw [t2regs .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.size]
    · rw [t2regs .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.primitive]
    · rw [t2regs .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.roots]
    · rw [t2regs .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        inv.ready.commitment]
    · intro word bound outside
      rw [view_of_mem cmem]
      exact tView word bound outside

/-! ### From one trial to the next -/

theorem trial_next (E s : MachineState) (u g claim : Nat) (miss : TrialMiss E s u g claim)
    (node : u = 255 ∨ u = 510 ∨ u = 511) (low : 1 ≤ g) (high : g < 256) (claimLow : 4096 ≤ claim)
    (claimHigh : claim+4 ≤ 2^33) :
    Hop s (nextState s) 3 3 ∧ (g+1 < 256 → TrialInv E (nextState s) u (g+1) claim) ∧
      (g+1 = 256 → (nextState s).pc = spc 1220) := by
  have hu : u < 512 := by rcases node with rfl | rfl | rfl <;> decide
  obtain ⟨hop, mem, x19, npc, regs⟩ := next_trial s g miss.pc miss.trial high
  refine ⟨hop, fun more => ?_, fun top => by rw [npc, if_pos top]⟩
  have keep (r : Reg) (a : r ≠ .x7) (b : r ≠ .x19) : (nextState s).getReg r = s.getReg r := regs r a b
  refine ⟨⟨by rw [npc, if_neg (by omega)], ?_, x19, ?_, ?_, ?_, ?_, ?_⟩, by omega, more, node, ?_, ?_, claimLow,
    claimHigh⟩
  · rw [keep .x18 (by decide) (by decide), miss.node]
  · rw [keep .x5 (by decide) (by decide), miss.selector]
  · rw [keep .x11 (by decide) (by decide), miss.size]
  · rw [keep .x13 (by decide) (by decide), miss.primitive]
  · rw [keep .x25 (by decide) (by decide), miss.roots]
  · rw [keep .x9 (by decide) (by decide), miss.commitment]
  · intro word bound outside other
    rw [view_of_mem mem, miss.words word bound outside, patched_view E u g hu word bound other]
  · have outside := off_ancestors u node u (Or.inl rfl) 3 (by decide)
    rw [view_of_mem mem, show topWord u = 2048+4*u+3 from rfl, miss.words _ (by omega) outside]
    unfold patchedState
    rw [set_top_half E u hu _ _ (by omega), if_pos rfl, if_neg (by omega), Nat.add_sub_cancel]

/-! ### The loop -/

theorem climb_rows_length (oracle : Oracle) (σ : Nat → BitVec 256) :
    ∀ d n v, (climbFrom oracle σ d n v).1.length = d := by
  intro d
  induction d with
  | zero => intro _ _; rfl
  | succ d ih => intro n v; simp [climbFrom, ih]

theorem depth_le (u : Nat) : depthOf u ≤ 8 := by unfold depthOf; split <;> omega

theorem segment_run (oracle : Oracle) {s t : MachineState} (seg : Segment oracle s t) (fuel : Nat)
    (enough : seg.steps ≤ fuel) :
    checkEvaluation oracle (recordRows (execute packedImage fuel s false)) =
      let next := checkEvaluation oracle (recordRows (execute packedImage (fuel-seg.steps) t false))
      ((next.1.1.charge seg.cycles seg.rows.length, seg.rows ++ next.1.2), seg.rows.length + next.2) := by
  have := seg.checked (fuel-seg.steps)
  rwa [show seg.steps+(fuel-seg.steps) = fuel by omega] at this

theorem trial_loop (oracle : Oracle) (E : MachineState) (u claim : Nat) :
    ∀ k g s, g+k = 256 → TrialInv E s u g claim → ∀ fuel, 124*k ≤ fuel →
      let obs := checkEvaluation oracle (recordRows (execute packedImage fuel s false))
      obs.1.1.exit ≠ .unfinished ∧ obs.2 ≤ depthOf u * k ∧
      (obs.1.1.exit = .success → ∃ g', g ≤ g' ∧ g' < 256 ∧ (trialClimb oracle E u g').2 = readBuffer E (8*claim) 32 ∧
          ∀ row ∈ (trialClimb oracle E u g').1, row ∈ obs.1.2) ∧
      ((∃ g', g ≤ g' ∧ g' < 256 ∧ (trialClimb oracle E u g').2 = readBuffer E (8*claim) 32) →
        obs.1.1.exit = .success) := by
  intro k
  induction k with
  | zero => intro g s sum inv; have := inv.high; omega
  | succ k ih =>
    intro g s sum inv fuel enough
    obtain ⟨t, seg, rows, steps, accept, miss⟩ := trial_step oracle E s u g claim inv
    have rowsLen : seg.rows.length = depthOf u := by rw [rows]; exact climb_rows_length _ _ _ _ _
    have run := segment_run oracle seg fuel (by omega)
    dsimp only
    rw [run]
    by_cases matched : (trialClimb oracle E u g).2 = readBuffer E (8*claim) 32
    · have tpc := accept matched
      have done := execute_search_accept t tpc (fuel-seg.steps-3)
      rw [show fuel-seg.steps = 3+(fuel-seg.steps-3) by omega, done, record_rows_pure, check_evaluation_pure]
      refine ⟨by simp [Execution.charge], ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_nil, Nat.add_zero]
        rw [rowsLen]
        exact Nat.le_mul_of_pos_right _ (by omega)
      · intro _
        refine ⟨g, le_refl _, inv.high, matched, ?_⟩
        intro row member
        rw [← rows] at member
        exact List.mem_append_left _ member
      · intro _
        rfl
    · have m := miss matched
      obtain ⟨nhop, nextInv, nextEnd⟩ := trial_next E t u g claim m inv.node inv.low inv.high inv.claimLow inv.claimHigh
      let step : Segment oracle t (nextState t) := Segment.ordinary oracle 3 3 nhop
      have run2 := segment_run oracle step (fuel-seg.steps) (by show 3 ≤ _; omega)
      rw [show step.steps = 3 from rfl] at run2
      rw [run2]
      by_cases more : g+1 < 256
      · have inv' := nextInv more
        obtain ⟨term, calls, acc, comp⟩ := ih (g+1) (nextState t) (by omega) inv' (fuel-seg.steps-3) (by omega)
        refine ⟨by simpa [Execution.charge] using term, ?_, ?_, ?_⟩
        · simp only [show step.rows = [] from rfl, List.length_nil, Nat.zero_add]
          rw [rowsLen]
          have : depthOf u * (k+1) = depthOf u + depthOf u * k := by ring
          omega
        · intro success
          obtain ⟨g', lo, hi, root, member⟩ := acc (by simpa [Execution.charge] using success)
          refine ⟨g', by omega, hi, root, ?_⟩
          intro row found
          exact List.mem_append_right _ (List.mem_append_right _ (member row found))
        · rintro ⟨g', lo, hi, root⟩
          have ne : g' ≠ g := by rintro rfl; exact matched root
          have := comp ⟨g', by omega, hi, root⟩
          simpa [Execution.charge] using this
      · have top : g+1 = 256 := by have := inv.high; omega
        have npc := nextEnd top
        obtain ⟨jhop, jpc⟩ := last_jump (nextState t) npc
        let jump : Segment oracle (nextState t) _ := Segment.ordinary oracle 1 1 jhop
        have run3 := segment_run oracle jump (fuel-seg.steps-3) (by show 1 ≤ _; omega)
        rw [show jump.steps = 1 from rfl] at run3
        rw [run3]
        have rejected := execute_reject _ jpc (fuel-seg.steps-3-1-3)
        rw [show fuel-seg.steps-3-1 = 3+(fuel-seg.steps-3-1-3) by omega, rejected,
          record_rows_pure, check_evaluation_pure]
        refine ⟨by simp [Execution.charge], ?_, ?_, ?_⟩
        · simp only [show step.rows = [] from rfl, show jump.rows = [] from rfl, List.length_nil, Nat.zero_add,
            Nat.add_zero]
          rw [rowsLen]
          exact Nat.le_mul_of_pos_right _ (by omega)
        · intro impossible
          simp [Execution.charge] at impossible
        · rintro ⟨g', lo, hi, root⟩
          have : g' = g := by omega
          subst this
          exact absurd root matched

/-! ### The whole search from its entry (word 1163) -/

theorem pick_node {s : MachineState} {u : Nat} (some_ : pickU s = some u) : u = 255 ∨ u = 510 ∨ u = 511 := by
  unfold pickU at some_
  split at some_ <;> split at some_ <;> cases some_ <;> simp

theorem pick_mem {a b : MachineState} (same : a.mem = b.mem) : pickU a = pickU b := by
  unfold pickU markWord MachineState.getMem
  rw [same]

/-- The search: it terminates within its fuel, makes at most 2,040 compressions, accepts only after a trial whose
climb reaches the commitment (its rows recorded), and accepts whenever some trial does. -/
theorem search_facts (oracle : Oracle) (E : MachineState) (claim : Nat) (pc : E.pc = spc 1163)
    (marks : E.getReg .x26 = 4096#64) (roots : E.getReg .x25 = 16384#64)
    (commitment : E.getReg .x9 = wordAddress claim) (claimLow : 4096 ≤ claim) (claimHigh : claim+4 ≤ 2^33)
    (fuel : Nat) (enough : 32000 ≤ fuel) :
    let obs := checkEvaluation oracle (recordRows (execute packedImage fuel E false))
    obs.1.1.exit ≠ .unfinished ∧ obs.2 ≤ 2040 ∧
    (obs.1.1.exit = .success → E.getReg .x22 = searchEnd ∧ ∃ u g, pickU E = some u ∧ 1 ≤ g ∧ g < 256 ∧
        (trialClimb oracle E u g).2 = readBuffer E (8*claim) 32 ∧ ∀ row ∈ (trialClimb oracle E u g).1, row ∈ obs.1.2) ∧
    (E.getReg .x22 = searchEnd → ∀ u, pickU E = some u →
      (∃ g, 1 ≤ g ∧ g < 256 ∧ (trialClimb oracle E u g).2 = readBuffer E (8*claim) 32) → obs.1.1.exit = .success) ∧
    (E.getReg .x22 ≠ searchEnd → obs.2 = 0) := by
  obtain ⟨ehop, epc, emem, eregs⟩ := entry_branch E pc
  let entry : Segment oracle E (entryBranch E) := Segment.ordinary oracle 4 4 ehop
  have run := segment_run oracle entry fuel (by show 4 ≤ fuel; omega)
  rw [show entry.steps = 4 from rfl] at run
  dsimp only
  rw [run]
  by_cases atEnd : E.getReg .x22 = searchEnd
  · rw [if_pos atEnd] at epc
    have keep (r : Reg) (n : r ≠ .x7) : (entryBranch E).getReg r = E.getReg r := eregs r n
    obtain ⟨none_, some_⟩ := search_pick (entryBranch E) claim epc ((keep .x26 (by decide)).trans marks)
      ((keep .x25 (by decide)).trans roots) ((keep .x9 (by decide)).trans commitment)
    have samePick : pickU (entryBranch E) = pickU E := pick_mem emem
    cases picked : pickU E with
    | none =>
      obtain ⟨t, thop, tpc⟩ := none_ (samePick.trans picked)
      let pickSeg : Segment oracle (entryBranch E) t := Segment.ordinary oracle 6 6 thop
      have run2 := segment_run oracle pickSeg (fuel-4) (by show 6 ≤ _; omega)
      rw [show pickSeg.steps = 6 from rfl] at run2
      rw [run2]
      have rejected := execute_reject t tpc (fuel-4-6-3)
      rw [show fuel-4-6 = 3+(fuel-4-6-3) by omega, rejected, record_rows_pure, check_evaluation_pure]
      refine ⟨by simp [Execution.charge], by simp [Execution.charge, entry, pickSeg, Segment.ordinary], ?_, ?_,
        fun bad => absurd atEnd bad⟩
      · intro impossible
        simp [Execution.charge] at impossible
      · intro _ u hu
        cases hu
    | some u =>
      obtain ⟨t, c, cb, thop, ready, tmem⟩ := some_ u (samePick.trans picked)
      have node := pick_node picked
      have inv : TrialInv E t u 1 claim := by
        refine ⟨ready, le_refl _, by decide, node, ?_, ?_, claimLow, claimHigh⟩
        · intro word _ _ _
          exact view_of_mem (tmem.trans emem) word
        · rw [if_pos rfl]
          exact view_of_mem (tmem.trans emem) _
      let pickSeg : Segment oracle (entryBranch E) t := Segment.ordinary oracle c c thop
      have run2 := segment_run oracle pickSeg (fuel-4) (by show c ≤ _; omega)
      rw [show pickSeg.steps = c from rfl] at run2
      rw [run2]
      obtain ⟨term, calls, acc, comp⟩ := trial_loop oracle E u claim 255 1 t (by decide) inv (fuel-4-c) (by
        show 124*255 ≤ fuel-4-c; omega)
      refine ⟨by simpa [Execution.charge] using term, ?_, ?_, ?_, fun bad => absurd atEnd bad⟩
      · simp only [show entry.rows = [] from rfl, show pickSeg.rows = [] from rfl, List.length_nil, Nat.zero_add]
        have := depth_le u
        have : depthOf u * 255 ≤ 2040 := by omega
        show _ ≤ 2040
        omega
      · intro success
        obtain ⟨g', lo, hi, root, member⟩ := acc (by simpa [Execution.charge] using success)
        refine ⟨atEnd, u, g', rfl, lo, hi, root, ?_⟩
        intro row found
        simpa [show entry.rows = [] from rfl, show pickSeg.rows = [] from rfl] using member row found
      · intro _ u' hu' ⟨g, lo, hi, root⟩
        cases hu'
        simpa [Execution.charge] using comp ⟨g, lo, hi, root⟩
  · rw [if_neg atEnd] at epc
    have rejected := execute_reject (entryBranch E) epc (fuel-4-3)
    rw [show fuel-4 = 3+(fuel-4-3) by omega, rejected, record_rows_pure, check_evaluation_pure]
    refine ⟨by simp [Execution.charge], by simp [Execution.charge, entry, Segment.ordinary], ?_, ?_,
      fun _ => by simp [Execution.charge, entry, Segment.ordinary]⟩
    · intro impossible
      simp [Execution.charge] at impossible
    · intro bad
      exact absurd bad atEnd

end TwoPermutationPrototype.Packed.Checker
