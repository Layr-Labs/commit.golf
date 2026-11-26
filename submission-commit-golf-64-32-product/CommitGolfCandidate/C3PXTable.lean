import CommitGolfCandidate.C3XTable
import CommitGolfCandidate.C3PXScan

/-! # The permutation side of the cross-oracle event, for any window shape

`C3XTable` with the two windows as parameters: `zField` is the window of a permutation input that
holds the compression reply, `digest` the window of a reply that the leaf keeps. The argument is
that of `C3XTable`. The counts need only that each window value has at most `2^1344` states
(`zFibre`, `digestFibre`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleSpec

set_option autoImplicit false
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false

/-- The bad events of the permutation table of a marked run. -/
def shapeSpec (zField digest : Block → BitVec 256) : BadSpec PermState where
  pair new old :=
    (new.dir = .fwd ∧ digest new.out = digest old.out) ∨
    (new.dir = .inv ∧ old.inp = c3Marker (zField new.inp))
  single _ := False

/-- The table of a marked run against the shape scan of its log. -/
structure ShapeInv (zField digest : Block → BitVec 256) (t : Trace PermState) (state : ScanState) : Prop where
  /-- Every compression reply seen has its marker input in the table. -/
  marked : ∀ c ∈ state.seen, ∃ m ∈ t, m.inp = c3Marker c
  /-- The field of every entry fixed by an inverse call is a target. -/
  targeted : ∀ e ∈ t, e.dir = .inv → zField e.inp ∈ state.targets
  /-- Every recorded permutation row is in the table. -/
  stored : ∀ x y, PublicRow.permutation x y ∈ state.rows → ∃ e ∈ t, e.inp = x ∧ e.out = y
  /-- Every recorded compression reply was seen. -/
  replies : ∀ source c, PublicRow.compression source c ∈ state.rows → c ∈ state.seen
  /-- The order clause, see the file header. -/
  fresh : ¬ state.flag → (shapeSpec zField digest).Good t → ∀ e ∈ t, e.dir = .inv → zField e.inp ∉ state.seen

theorem ShapeInv.init (zField digest : Block → BitVec 256) :
    ShapeInv zField digest ([] : Trace PermState) ScanState.init where
  marked := fun c hc => by simp [ScanState.init] at hc
  targeted := fun e he => by simp at he
  stored := fun x y h => by simp [ScanState.init] at h
  replies := fun source c h => by simp [ScanState.init] at h
  fresh := fun _ _ e he => by simp at he

theorem ShapeInv.forward {zField digest : Block → BitVec 256} {t : Trace PermState} {state : ScanState}
    (inv : ShapeInv zField digest t state)
    (x y : PermState) (allowed : y ∈ t.fwdAns x) :
    ShapeInv zField digest (t.stepF x y) (shapeStep zField state (.forward x y)) := by
  have grows : ∀ e ∈ t, e ∈ t.stepF x y := fun e he => (Trace.suffix_stepF t x y).subset he
  obtain ⟨new, hnew, hin, hout⟩ := Trace.mem_stepF_of_mem_fwdAns allowed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨m, hm, e⟩ := inv.marked c hc
    exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change zField e.inp ∈ state.targets
    rcases step_forward_cases t x y with same | cons
    · rw [same] at he
      exact inv.targeted e he dir
    · rw [cons] at he
      rcases List.mem_cons.1 he with rfl | old
      · exact absurd dir (by simp)
      · exact inv.targeted e old dir
  · intro a b present
    change PublicRow.permutation a b ∈ PublicRow.permutation x y :: state.rows at present
    rcases List.mem_cons.1 present with head | tail
    · cases head
      exact ⟨new, hnew, hin, hout⟩
    · obtain ⟨e, he, h1, h2⟩ := inv.stored a b tail
      exact ⟨e, grows e he, h1, h2⟩
  · intro source c present
    change PublicRow.compression source c ∈ PublicRow.permutation x y :: state.rows at present
    change c ∈ state.seen
    rcases List.mem_cons.1 present with head | tail
    · cases head
    · exact inv.replies source c tail
  · intro clear good e he dir
    change ¬ state.flag at clear
    change zField e.inp ∉ state.seen
    rcases step_forward_cases t x y with same | cons
    · rw [same] at he good
      exact inv.fresh clear good e he dir
    · rw [cons] at he good
      have goodTail := (((shapeSpec zField digest).good_cons_iff _ _).1 good).2.2
      rcases List.mem_cons.1 he with rfl | old
      · exact absurd dir (by simp)
      · exact inv.fresh clear goodTail e old dir

theorem ShapeInv.inverse {zField digest : Block → BitVec 256} {t : Trace PermState} {state : ScanState}
    (inv : ShapeInv zField digest t state)
    (x y : PermState) (allowed : x ∈ t.invAns y) :
    ShapeInv zField digest (t.stepI x y) (shapeStep zField state (.inverse x y)) := by
  have grows : ∀ e ∈ t, e ∈ t.stepI x y := fun e he => (Trace.suffix_stepI t x y).subset he
  obtain ⟨new, hnew, hin, hout⟩ := Trace.mem_stepI_of_mem_invAns allowed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨m, hm, e⟩ := inv.marked c hc
    exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change zField e.inp ∈ zField x :: state.targets
    rcases step_inverse_cases t x y with same | cons
    · rw [same] at he
      exact List.mem_cons_of_mem _ (inv.targeted e he dir)
    · rw [cons] at he
      rcases List.mem_cons.1 he with rfl | old
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (inv.targeted e old dir)
  · intro a b present
    change PublicRow.permutation a b ∈ PublicRow.permutation x y :: state.rows at present
    rcases List.mem_cons.1 present with head | tail
    · cases head
      exact ⟨new, hnew, hin, hout⟩
    · obtain ⟨e, he, h1, h2⟩ := inv.stored a b tail
      exact ⟨e, grows e he, h1, h2⟩
  · intro source c present
    change PublicRow.compression source c ∈ PublicRow.permutation x y :: state.rows at present
    change c ∈ state.seen
    rcases List.mem_cons.1 present with head | tail
    · cases head
    · exact inv.replies source c tail
  · intro clear good e he dir
    change ¬ state.flag at clear
    change zField e.inp ∉ state.seen
    rcases step_inverse_cases t x y with same | cons
    · rw [same] at he good
      exact inv.fresh clear good e he dir
    · rw [cons] at he good
      obtain ⟨noPair, -, goodTail⟩ := ((shapeSpec zField digest).good_cons_iff _ _).1 good
      rcases List.mem_cons.1 he with rfl | old
      · intro hit
        obtain ⟨m, hm, marker⟩ := inv.marked _ hit
        exact noPair m hm (Or.inr ⟨rfl, marker⟩)
      · exact inv.fresh clear goodTail e old dir

theorem ShapeInv.compression {zField digest : Block → BitVec 256} {t : Trace PermState} {state : ScanState}
    (inv : ShapeInv zField digest t state)
    (source : BitVec 512) (c : BitVec 256) (y : PermState)
    (allowed : y ∈ t.fwdAns (c3Marker c)) :
    ShapeInv zField digest (t.stepF (c3Marker c) y) (shapeStep zField state (.compression source c y)) := by
  have grows : ∀ e ∈ t, e ∈ t.stepF (c3Marker c) y :=
    fun e he => (Trace.suffix_stepF t (c3Marker c) y).subset he
  obtain ⟨new, hnew, hin, -⟩ := Trace.mem_stepF_of_mem_fwdAns allowed
  have oldEntry : ∀ e ∈ t.stepF (c3Marker c) y, e.dir = .inv → e ∈ t := by
    intro e he dir
    rcases step_forward_cases t (c3Marker c) y with same | cons
    · rw [same] at he
      exact he
    · rw [cons] at he
      rcases List.mem_cons.1 he with rfl | old
      · exact absurd dir (by simp)
      · exact old
  have goodOld : (shapeSpec zField digest).Good (t.stepF (c3Marker c) y) → (shapeSpec zField digest).Good t := by
    intro good
    rcases step_forward_cases t (c3Marker c) y with same | cons
    · rw [same] at good
      exact good
    · rw [cons] at good
      exact (((shapeSpec zField digest).good_cons_iff _ _).1 good).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    change d ∈ c :: state.seen at hd
    rcases List.mem_cons.1 hd with rfl | old
    · exact ⟨new, hnew, hin⟩
    · obtain ⟨m, hm, e⟩ := inv.marked d old
      exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change zField e.inp ∈ state.targets
    exact inv.targeted e (oldEntry e he dir) dir
  · intro a b present
    change PublicRow.permutation a b ∈ PublicRow.compression source c :: state.rows at present
    rcases List.mem_cons.1 present with head | tail
    · cases head
    · obtain ⟨e, he, h1, h2⟩ := inv.stored a b tail
      exact ⟨e, grows e he, h1, h2⟩
  · intro s d present
    change PublicRow.compression s d ∈ PublicRow.compression source c :: state.rows at present
    change d ∈ c :: state.seen
    rcases List.mem_cons.1 present with head | tail
    · cases head
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (inv.replies s d tail)
  · intro clear good e he dir
    change ¬ (state.flag ∨ (c ∉ state.seen ∧ c ∈ state.targets)) at clear
    change zField e.inp ∉ c :: state.seen
    have clearOld : ¬ state.flag := fun h => clear (Or.inl h)
    have old := oldEntry e he dir
    have notSeen := inv.fresh clearOld (goodOld good) e old dir
    intro hit
    rcases List.mem_cons.1 hit with eq | earlier
    · have target := inv.targeted e old dir
      rw [eq] at target notSeen
      exact clear (Or.inr ⟨notSeen, target⟩)
    · exact notSeen earlier

/-- **The invariant holds along every run of the marked program.** -/
theorem shape_table_invariant (zField digest : Block → BitVec 256) {α : Type} (compress : Compression)
    (program : OracleComp World α) (s : PState PermState) (state : ScanState)
    (inv : ShapeInv zField digest s.trace state) :
    (toStrat compress (markedRows program)).post s fun result finish =>
      ShapeInv zField digest finish.trace (shapeScan zField state result.2) := by
  induction program using OracleComp.inductionOn generalizing s state with
  | pure value => exact inv
  | query_bind query next ih =>
    rcases query with coins | input | input | output
    · rw [marked_rows_coins, to_strat_coins]
      intro answer
      exact ih answer s state inv
    · rw [marked_rows_compress, to_strat_compress, to_strat_permute]
      intro mark allowed
      try dsimp only
      rw [to_strat_map]
      refine Strat.post_bind (Strat.post_mono ?_
        (ih (compress input) ⟨s.trace.stepF (c3Marker (compress input)) mark, s.count + 1⟩
          (shapeStep zField state (.compression input (compress input) mark))
          (inv.compression input (compress input) mark allowed)))
      intro result finish kept
      exact kept
    · rw [marked_rows_permute, to_strat_permute]
      intro reply allowed
      try dsimp only
      rw [to_strat_map]
      refine Strat.post_bind (Strat.post_mono ?_
        (ih reply ⟨s.trace.stepF input reply, s.count + 1⟩ (shapeStep zField state (.forward input reply))
          (inv.forward input reply allowed)))
      intro result finish kept
      exact kept
    · rw [marked_rows_inverse, to_strat_inverse]
      intro answer allowed
      try dsimp only
      rw [to_strat_map]
      refine Strat.post_bind (Strat.post_mono ?_
        (ih answer ⟨s.trace.stepI answer output, s.count + 1⟩
          (shapeStep zField state (.inverse answer output)) (inv.inverse answer output allowed)))
      intro result finish kept
      exact kept

/-- **Extraction (deterministic).** With the invariant, a witness among the rows means that the
table is bad or the flag was raised. -/
theorem shape_witness_bad_or_flag {zField digest : Block → BitVec 256} {t : Trace PermState}
    {state : ScanState} (inv : ShapeInv zField digest t state)
    (witness : C3PShapeWitness zField digest state.rows) : ¬ (shapeSpec zField digest).Good t ∨ state.flag := by
  by_contra h
  rw [not_or, not_not] at h
  obtain ⟨good, clear⟩ := h
  obtain ⟨x₀, x₁, y₀, y₁, s₀, s₁, row₀, row₁, comp₀, comp₁, different, sameDigest⟩ := witness
  obtain ⟨e₀, he₀, in₀, out₀⟩ := inv.stored x₀ y₀ row₀
  obtain ⟨e₁, he₁, in₁, out₁⟩ := inv.stored x₁ y₁ row₁
  have distinct : e₀ ≠ e₁ := by
    rintro rfl
    exact different (in₀.symm.trans in₁)
  have seen₀ := inv.replies s₀ _ comp₀
  have seen₁ := inv.replies s₁ _ comp₁
  have inverse : ∀ e other : Permutation.Entry PermState,
      digest e.out = digest other.out → ¬ (shapeSpec zField digest).pair e other → e.dir = .inv := by
    intro e other same noPair
    cases dir : e.dir with
    | fwd => exact absurd (Or.inl ⟨dir, same⟩) noPair
    | inv => rfl
  rcases good.not_pair he₀ he₁ distinct with noPair | noPair
  · have dir := inverse e₀ e₁ (by rw [out₀, out₁]; exact sameDigest) noPair
    exact inv.fresh clear good e₀ he₀ dir (by rw [in₀]; exact seen₀)
  · have dir := inverse e₁ e₀ (by rw [out₀, out₁]; exact sameDigest.symm) noPair
    exact inv.fresh clear good e₁ he₁ dir (by rw [in₁]; exact seen₁)

/-! ### Counts -/

/-- A fresh forward reply is bad against one older entry for at most `2^1344` values. -/
theorem shape_forward_pairs (zField digest : Block → BitVec 256)
    (digestFibre : ∀ d : BitVec 256, (Finset.univ.filter fun s : PermState => digest s = d).card ≤ 2 ^ 1344)
    (x : PermState) (old : Permutation.Entry PermState) :
    ∃ F : Finset PermState, F.card ≤ 2 ^ 1344 ∧
      ∀ y, (shapeSpec zField digest).pair ⟨.fwd, x, y⟩ old → y ∈ F := by
  refine ⟨Finset.univ.filter fun s : PermState => digest s = digest old.out, digestFibre _,
    fun y bad => ?_⟩
  rcases bad with ⟨-, same⟩ | ⟨dir, -⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, same⟩
  · exact absurd dir (by simp)

/-- A fresh inverse reply is bad against one older entry for at most `2^1344` values. -/
theorem shape_inverse_pairs (zField digest : Block → BitVec 256)
    (zFibre : ∀ c : BitVec 256, (Finset.univ.filter fun s : PermState => zField s = c).card ≤ 2 ^ 1344)
    (y : PermState) (old : Permutation.Entry PermState) :
    ∃ F : Finset PermState, F.card ≤ 2 ^ 1344 ∧
      ∀ x, (shapeSpec zField digest).pair ⟨.inv, x, y⟩ old → x ∈ F := by
  by_cases marker : ∃ c, old.inp = c3Marker c
  · obtain ⟨c, hc⟩ := marker
    refine ⟨Finset.univ.filter fun s : PermState => zField s = c, zFibre c, fun x bad => ?_⟩
    rcases bad with ⟨dir, -⟩ | ⟨-, hit⟩
    · exact absurd dir (by simp)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (c3_marker_injective (hc.symm.trans hit)).symm⟩
  · refine ⟨∅, Nat.zero_le _, fun x bad => ?_⟩
    rcases bad with ⟨dir, -⟩ | ⟨-, hit⟩
    · exact absurd dir (by simp)
    · exact absurd ⟨_, hit⟩ marker

/-- **The union bound for the table of a marked run**, for any window shape with small fibres. -/
theorem shape_table_probability (zField digest : Block → BitVec 256)
    (zFibre : ∀ c : BitVec 256, (Finset.univ.filter fun s : PermState => zField s = c).card ≤ 2 ^ 1344)
    (digestFibre : ∀ d : BitVec 256, (Finset.univ.filter fun s : PermState => digest s = d).card ≤ 2 ^ 1344)
    {α : Type} (compress : Compression) (program : OracleComp World α) (calls : Nat)
    (fits : calls < 2 ^ 1600) (bounded : PublicQueryBound program calls) :
    (toStrat compress (markedRows program)).prob PState.init
        (fun result _ => C3PShapeWitness zField digest (shapeScan zField ScanState.init result.2).rows ∧
          ¬ (shapeScan zField ScanState.init result.2).flag) ≤
      ((calls : ℝ) * ((calls : ℝ) - 1) / 2 * ((2 ^ 1344 : ℕ) : ℝ) + (calls : ℝ) * ((0 : ℕ) : ℝ)) /
        (((2 ^ 1600 : ℕ) : ℝ) - calls) := by
  have budget : (toStrat compress (markedRows program)).QB calls := marked_strat_QB compress bounded
  have records := shape_table_invariant zField digest compress program PState.init ScanState.init
    (ShapeInv.init zField digest)
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have card : Fintype.card PermState = 2 ^ 1600 := c3_card_state
  have evidence : (toStrat compress (markedRows program)).prob PState.init
        (fun result _ => C3PShapeWitness zField digest (shapeScan zField ScanState.init result.2).rows ∧
          ¬ (shapeScan zField ScanState.init result.2).flag) ≤
      (toStrat compress (markedRows program)).prob PState.init
        (fun _ finish => ¬ (shapeSpec zField digest).Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    rintro result finish ⟨inv, -, count⟩ ⟨witness, clear⟩
    refine ⟨?_, by simpa [PState.init] using count⟩
    rcases shape_witness_bad_or_flag inv witness with bad | flag
    · exact bad
    · exact absurd flag clear
  have fitsCard : calls < Fintype.card PermState := card ▸ fits
  have raw := prob_not_good_le (shapeSpec zField digest) (2 ^ 1344) 0 calls fitsCard
    (shape_forward_pairs zField digest digestFibre)
    (fun _ => ⟨∅, Nat.zero_le _, fun _ bad => bad.elim⟩) (shape_inverse_pairs zField digest zFibre)
    (fun _ => ⟨∅, Nat.zero_le _, fun _ bad => bad.elim⟩) (toStrat compress (markedRows program))
  rw [card] at raw
  exact evidence.trans raw

end TwoPermutationPrototype.Sampling
