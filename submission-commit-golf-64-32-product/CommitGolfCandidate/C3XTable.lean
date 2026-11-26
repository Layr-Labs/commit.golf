import CommitGolfCandidate.C3XLog
import CommitGolfCandidate.S3PermBadEvent
import CommitGolfCandidate.S3LeafLayout

/-! # The permutation side of the cross-oracle event

The compression function is fixed and the permutation is sampled lazily (`Strat`, S3PermModel).
The table of the marked run is bad (`c3Spec`) when

* a fresh forward reply shares its first 256 bits with the output of an older entry, or
* a fresh inverse reply has, as its `t3` field, a value whose marker input is an older entry: the
  field equals a compression reply that was already made.

`C3Inv` relates the table to the scanned log. Its last clause is the order argument: while the
table is good and no flag was raised, no entry fixed by an inverse call has a `t3` field among the
compression replies seen. It is kept by every call:

* an inverse call whose fresh input has a seen field makes the table bad, because the marker of
  that field is an older entry;
* a compression call whose reply is the field of an entry fixed by an inverse call either repeats
  a reply seen before (impossible by the clause) or raises the flag.

`witness_bad_or_flag`: a `C3PermWitness` among the rows then means a bad table or a raised flag.
`marked_table_probability` is the union bound for the first alternative. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleSpec

set_option autoImplicit false
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false

/-- The bad events of the permutation table of a marked run. -/
def c3Spec : BadSpec PermState where
  pair new old :=
    (new.dir = .fwd ∧ outputDigest new.out = outputDigest old.out) ∨
    (new.dir = .inv ∧ old.inp = c3Marker (c3T3Field new.inp))
  single _ := False

theorem step_forward_cases (t : Trace PermState) (x y : PermState) :
    t.stepF x y = t ∨ t.stepF x y = ⟨.fwd, x, y⟩ :: t := by
  unfold Trace.stepF
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem step_inverse_cases (t : Trace PermState) (x y : PermState) :
    t.stepI x y = t ∨ t.stepI x y = ⟨.inv, x, y⟩ :: t := by
  unfold Trace.stepI
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The table of a marked run against the scan of its log. -/
structure C3Inv (t : Trace PermState) (state : ScanState) : Prop where
  /-- Every compression reply seen has its marker input in the table. -/
  marked : ∀ c ∈ state.seen, ∃ m ∈ t, m.inp = c3Marker c
  /-- The field of every entry fixed by an inverse call is a target. -/
  targeted : ∀ e ∈ t, e.dir = .inv → c3T3Field e.inp ∈ state.targets
  /-- Every recorded permutation row is in the table. -/
  stored : ∀ x y, PublicRow.permutation x y ∈ state.rows → ∃ e ∈ t, e.inp = x ∧ e.out = y
  /-- Every recorded compression reply was seen. -/
  replies : ∀ source c, PublicRow.compression source c ∈ state.rows → c ∈ state.seen
  /-- The order clause, see the file header. -/
  fresh : ¬ state.flag → c3Spec.Good t → ∀ e ∈ t, e.dir = .inv → c3T3Field e.inp ∉ state.seen

theorem C3Inv.init : C3Inv ([] : Trace PermState) ScanState.init where
  marked := fun c hc => by simp [ScanState.init] at hc
  targeted := fun e he => by simp at he
  stored := fun x y h => by simp [ScanState.init] at h
  replies := fun source c h => by simp [ScanState.init] at h
  fresh := fun _ _ e he => by simp at he

theorem C3Inv.forward {t : Trace PermState} {state : ScanState} (inv : C3Inv t state)
    (x y : PermState) (allowed : y ∈ t.fwdAns x) :
    C3Inv (t.stepF x y) (scanStep state (.forward x y)) := by
  have grows : ∀ e ∈ t, e ∈ t.stepF x y := fun e he => (Trace.suffix_stepF t x y).subset he
  obtain ⟨new, hnew, hin, hout⟩ := Trace.mem_stepF_of_mem_fwdAns allowed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨m, hm, e⟩ := inv.marked c hc
    exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change c3T3Field e.inp ∈ state.targets
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
    change c3T3Field e.inp ∉ state.seen
    rcases step_forward_cases t x y with same | cons
    · rw [same] at he good
      exact inv.fresh clear good e he dir
    · rw [cons] at he good
      have goodTail := ((c3Spec.good_cons_iff _ _).1 good).2.2
      rcases List.mem_cons.1 he with rfl | old
      · exact absurd dir (by simp)
      · exact inv.fresh clear goodTail e old dir

theorem C3Inv.inverse {t : Trace PermState} {state : ScanState} (inv : C3Inv t state)
    (x y : PermState) (allowed : x ∈ t.invAns y) :
    C3Inv (t.stepI x y) (scanStep state (.inverse x y)) := by
  have grows : ∀ e ∈ t, e ∈ t.stepI x y := fun e he => (Trace.suffix_stepI t x y).subset he
  obtain ⟨new, hnew, hin, hout⟩ := Trace.mem_stepI_of_mem_invAns allowed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨m, hm, e⟩ := inv.marked c hc
    exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change c3T3Field e.inp ∈ c3T3Field x :: state.targets
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
    change c3T3Field e.inp ∉ state.seen
    rcases step_inverse_cases t x y with same | cons
    · rw [same] at he good
      exact inv.fresh clear good e he dir
    · rw [cons] at he good
      obtain ⟨noPair, -, goodTail⟩ := (c3Spec.good_cons_iff _ _).1 good
      rcases List.mem_cons.1 he with rfl | old
      · intro hit
        obtain ⟨m, hm, marker⟩ := inv.marked _ hit
        exact noPair m hm (Or.inr ⟨rfl, marker⟩)
      · exact inv.fresh clear goodTail e old dir

theorem C3Inv.compression {t : Trace PermState} {state : ScanState} (inv : C3Inv t state)
    (source : BitVec 512) (c : BitVec 256) (y : PermState)
    (allowed : y ∈ t.fwdAns (c3Marker c)) :
    C3Inv (t.stepF (c3Marker c) y) (scanStep state (.compression source c y)) := by
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
  have goodOld : c3Spec.Good (t.stepF (c3Marker c) y) → c3Spec.Good t := by
    intro good
    rcases step_forward_cases t (c3Marker c) y with same | cons
    · rw [same] at good
      exact good
    · rw [cons] at good
      exact ((c3Spec.good_cons_iff _ _).1 good).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    change d ∈ c :: state.seen at hd
    rcases List.mem_cons.1 hd with rfl | old
    · exact ⟨new, hnew, hin⟩
    · obtain ⟨m, hm, e⟩ := inv.marked d old
      exact ⟨m, grows m hm, e⟩
  · intro e he dir
    change c3T3Field e.inp ∈ state.targets
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
    change c3T3Field e.inp ∉ c :: state.seen
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
theorem marked_table_invariant {α : Type} (compress : Compression) (program : OracleComp World α)
    (s : PState PermState) (state : ScanState) (inv : C3Inv s.trace state) :
    (toStrat compress (markedRows program)).post s fun result finish =>
      C3Inv finish.trace (scan state result.2) := by
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
          (scanStep state (.compression input (compress input) mark))
          (inv.compression input (compress input) mark allowed)))
      intro result finish kept
      exact kept
    · rw [marked_rows_permute, to_strat_permute]
      intro reply allowed
      try dsimp only
      rw [to_strat_map]
      refine Strat.post_bind (Strat.post_mono ?_
        (ih reply ⟨s.trace.stepF input reply, s.count + 1⟩ (scanStep state (.forward input reply))
          (inv.forward input reply allowed)))
      intro result finish kept
      exact kept
    · rw [marked_rows_inverse, to_strat_inverse]
      intro answer allowed
      try dsimp only
      rw [to_strat_map]
      refine Strat.post_bind (Strat.post_mono ?_
        (ih answer ⟨s.trace.stepI answer output, s.count + 1⟩
          (scanStep state (.inverse answer output)) (inv.inverse answer output allowed)))
      intro result finish kept
      exact kept

/-- The marked strategy makes as many permutation queries as the program makes public calls: a
compression call costs its marker query. -/
theorem marked_strat_QB {α : Type} (compress : Compression) {program : OracleComp World α}
    {budget : Nat} (bounded : PublicQueryBound program budget) :
    (toStrat compress (markedRows program)).QB budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => exact Strat.QB.done _ budget
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | input | input | output
    · rw [marked_rows_coins, to_strat_coins]
      exact Strat.QB.rand _ _ _ fun answer =>
        ih answer (by simpa [Oracle.callCost] using bounded.2 answer)
    · rw [marked_rows_compress, to_strat_compress, to_strat_permute]
      obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by
        have := bounded.1; simp only [Oracle.callCost] at this; omega⟩
      refine Strat.QB.fwd _ _ rest fun mark => ?_
      rw [to_strat_map]
      exact Strat.QB.bind (ih (compress input) (by simpa [Oracle.callCost] using bounded.2 _))
        fun _ => Strat.QB.done _ 0
    · rw [marked_rows_permute, to_strat_permute]
      obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by
        have := bounded.1; simp only [Oracle.callCost] at this; omega⟩
      refine Strat.QB.fwd _ _ rest fun reply => ?_
      rw [to_strat_map]
      exact Strat.QB.bind (ih reply (by simpa [Oracle.callCost] using bounded.2 reply))
        fun _ => Strat.QB.done _ 0
    · rw [marked_rows_inverse, to_strat_inverse]
      obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by
        have := bounded.1; simp only [Oracle.callCost] at this; omega⟩
      refine Strat.QB.inv _ _ rest fun answer => ?_
      rw [to_strat_map]
      exact Strat.QB.bind (ih answer (by simpa [Oracle.callCost] using bounded.2 answer))
        fun _ => Strat.QB.done _ 0

/-- **Extraction (deterministic).** With the invariant, a witness among the rows means that the
table is bad or the flag was raised. -/
theorem witness_bad_or_flag {t : Trace PermState} {state : ScanState} (inv : C3Inv t state)
    (witness : C3PermWitness state.rows) : ¬ c3Spec.Good t ∨ state.flag := by
  by_contra h
  rw [not_or, not_not] at h
  obtain ⟨good, clear⟩ := h
  obtain ⟨x₀, x₁, y₀, y₁, s₀, s₁, row₀, row₁, comp₀, comp₁, different, digest⟩ := witness
  obtain ⟨e₀, he₀, in₀, out₀⟩ := inv.stored x₀ y₀ row₀
  obtain ⟨e₁, he₁, in₁, out₁⟩ := inv.stored x₁ y₁ row₁
  have distinct : e₀ ≠ e₁ := by
    rintro rfl
    exact different (in₀.symm.trans in₁)
  have seen₀ := inv.replies s₀ _ comp₀
  have seen₁ := inv.replies s₁ _ comp₁
  have inverse : ∀ e other : Permutation.Entry PermState,
      outputDigest e.out = outputDigest other.out → ¬ c3Spec.pair e other → e.dir = .inv := by
    intro e other same noPair
    cases dir : e.dir with
    | fwd => exact absurd (Or.inl ⟨dir, same⟩) noPair
    | inv => rfl
  rcases good.not_pair he₀ he₁ distinct with noPair | noPair
  · have dir := inverse e₀ e₁ (by rw [out₀, out₁]; exact digest) noPair
    exact inv.fresh clear good e₀ he₀ dir (by rw [in₀]; exact seen₀)
  · have dir := inverse e₁ e₀ (by rw [out₀, out₁]; exact digest.symm) noPair
    exact inv.fresh clear good e₁ he₁ dir (by rw [in₁]; exact seen₁)

/-! ### Counts -/

theorem c3_state_lt (s : PermState) : s.toNat < 2 ^ 1600 := s.isLt

theorem c3_card_state : Fintype.card PermState = 2 ^ 1600 := s3_card_bitvec _

/-- At most `2^1344` states share their first 256 bits. -/
theorem c3_digest_fiber (d : BitVec 256) :
    (Finset.univ.filter fun s : PermState => outputDigest s = d).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun s : PermState => outputDigest s = d)
    (t := (Finset.univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 (s.toNat / 2 ^ 256))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [outputDigest, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
        BitVec.toNat_ofNat] at e1 e2
      have hA := c3_state_lt a
      have hB := c3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- At most `2^1344` states share their `t3` field. -/
theorem c3_field_fiber (c : BitVec 256) :
    (Finset.univ.filter fun s : PermState => c3T3Field s = c).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun s : PermState => c3T3Field s = c)
    (t := (Finset.univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [c3T3Field, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_ofNat] at e1 e2
      have hA := c3_state_lt a
      have hB := c3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- A fresh forward reply is bad against one older entry for at most `2^1344` values. -/
theorem c3_forward_pairs (x : PermState) (old : Permutation.Entry PermState) :
    ∃ F : Finset PermState, F.card ≤ 2 ^ 1344 ∧ ∀ y, c3Spec.pair ⟨.fwd, x, y⟩ old → y ∈ F := by
  refine ⟨Finset.univ.filter fun s : PermState => outputDigest s = outputDigest old.out,
    c3_digest_fiber _, fun y bad => ?_⟩
  rcases bad with ⟨-, same⟩ | ⟨dir, -⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, same⟩
  · exact absurd dir (by simp)

/-- A fresh inverse reply is bad against one older entry for at most `2^1344` values: its `t3`
field must be the value whose marker is the older input. -/
theorem c3_inverse_pairs (y : PermState) (old : Permutation.Entry PermState) :
    ∃ F : Finset PermState, F.card ≤ 2 ^ 1344 ∧ ∀ x, c3Spec.pair ⟨.inv, x, y⟩ old → x ∈ F := by
  by_cases marker : ∃ c, old.inp = c3Marker c
  · obtain ⟨c, hc⟩ := marker
    refine ⟨Finset.univ.filter fun s : PermState => c3T3Field s = c, c3_field_fiber c,
      fun x bad => ?_⟩
    rcases bad with ⟨dir, -⟩ | ⟨-, hit⟩
    · exact absurd dir (by simp)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (c3_marker_injective (hc.symm.trans hit)).symm⟩
  · refine ⟨∅, Nat.zero_le _, fun x bad => ?_⟩
    rcases bad with ⟨dir, -⟩ | ⟨-, hit⟩
    · exact absurd dir (by simp)
    · exact absurd ⟨_, hit⟩ marker

/-- **The union bound for the table of a marked run**, for every fixed compression function: a
witness without a raised flag has probability at most `Q (Q - 1) / 2 · 2^1344 / (2^1600 - Q)` when
the program makes at most `Q` public calls. -/
theorem marked_table_probability {α : Type} (compress : Compression)
    (program : OracleComp World α) (calls : Nat) (fits : calls < 2 ^ 1600)
    (bounded : PublicQueryBound program calls) :
    (toStrat compress (markedRows program)).prob PState.init
        (fun result _ => C3PermWitness (scan ScanState.init result.2).rows ∧
          ¬ (scan ScanState.init result.2).flag) ≤
      ((calls : ℝ) * ((calls : ℝ) - 1) / 2 * ((2 ^ 1344 : ℕ) : ℝ) + (calls : ℝ) * ((0 : ℕ) : ℝ)) /
        (((2 ^ 1600 : ℕ) : ℝ) - calls) := by
  have budget : (toStrat compress (markedRows program)).QB calls := marked_strat_QB compress bounded
  have records := marked_table_invariant compress program PState.init ScanState.init C3Inv.init
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have card : Fintype.card PermState = 2 ^ 1600 := c3_card_state
  have evidence : (toStrat compress (markedRows program)).prob PState.init
        (fun result _ => C3PermWitness (scan ScanState.init result.2).rows ∧
          ¬ (scan ScanState.init result.2).flag) ≤
      (toStrat compress (markedRows program)).prob PState.init
        (fun _ finish => ¬ c3Spec.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    rintro result finish ⟨inv, -, count⟩ ⟨witness, clear⟩
    refine ⟨?_, by simpa [PState.init] using count⟩
    rcases witness_bad_or_flag inv witness with bad | flag
    · exact bad
    · exact absurd flag clear
  have fitsCard : calls < Fintype.card PermState := card ▸ fits
  have raw := prob_not_good_le c3Spec (2 ^ 1344) 0 calls fitsCard c3_forward_pairs
    (fun _ => ⟨∅, Nat.zero_le _, fun _ bad => bad.elim⟩) c3_inverse_pairs
    (fun _ => ⟨∅, Nat.zero_le _, fun _ bad => bad.elim⟩) (toStrat compress (markedRows program))
  rw [card] at raw
  exact evidence.trans raw

end TwoPermutationPrototype.Sampling
