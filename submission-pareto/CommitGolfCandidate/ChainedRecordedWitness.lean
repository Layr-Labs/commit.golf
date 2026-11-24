import CommitGolfCandidate.ChainedSecurityBound
import CommitGolfCandidate.JointOracle238Recorded
import CommitGolfCandidate.TwoPermutationPinnedPeerLayout

/-! Recorded compression chains and pinned leaves expose terminal failure. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def stageInput (enc : Encoding) (h : Height) (seed : Seed) (values : Nat → Output) (j : Nat) : Input :=
  if j = 0 then enc.first h seed else enc.next h j (values (j-1))

structure RecordedChain (enc : Encoding) (calls : Height → Nat) (rows : List PublicRow)
    (h : Height) (seed : Seed) (values : Nat → Output) : Prop where
  positive : 0 < calls h
  bounded : calls h ≤ 8
  observed : ∀ j, j < calls h → PublicRow.compression (stageInput enc h seed values j) (values j) ∈ rows

def RecordedCollision (enc : Encoding) (calls width : Height → Nat) (rows : List PublicRow) : Prop :=
  ∃ h a b va vb, a ≠ b ∧ RecordedChain enc calls rows h a va ∧ RecordedChain enc calls rows h b vb ∧
    lowBits (width h) (va (calls h-1)) = lowBits (width h) (vb (calls h-1))

def RecordedFailure (enc : Encoding) (calls width : Height → Nat) (rows : List PublicRow) : Prop :=
  PinnedLeafWitnessW 238 rows ∨ RecordedCollision enc calls width rows

theorem RecordedChain.mono {enc calls earlier later h seed values}
    (included : ∀ row ∈ earlier, row ∈ later) (chain : RecordedChain enc calls earlier h seed values) :
    RecordedChain enc calls later h seed values :=
  ⟨chain.positive,chain.bounded,fun j inside => included _ (chain.observed j inside)⟩

theorem RecordedFailure.mono {enc calls width earlier later}
    (included : ∀ row ∈ earlier, row ∈ later) (failure : RecordedFailure enc calls width earlier) :
    RecordedFailure enc calls width later := by
  rcases failure with leaf | ⟨h,a,b,va,vb,different,left,right,same⟩
  · left
    obtain ⟨p,i,n,m,v,w,a₀,a₁,b₀,b₁,equal,distinct⟩ := leaf
    exact ⟨p,i,n,m,v,w,included _ a₀,included _ a₁,included _ b₀,included _ b₁,equal,distinct⟩
  · exact Or.inr ⟨h,a,b,va,vb,different,left.mono included,right.mono included,same⟩

theorem cache_has_row (trace : Chained.Trace) (input : Input) (value : Output)
    (stored : trace.cache input = some value) :
    ∃ i, trace.input i = input ∧ trace.output i = value := by
  classical
  have found : ∃ i, trace.input i = input := by
    by_contra absent
    rw [(trace.cache_none_iff input).mpr absent] at stored
    contradiction
  obtain ⟨i,same⟩ := found
  have output := (trace.cache_of_row i input same).symm.trans stored
  exact ⟨i,same,Option.some.inj output⟩

theorem recorded_chain_evaluation {enc calls rows h seed values} (trace : Chained.Trace)
    (stored : ∀ x y, PublicRow.compression x y ∈ rows → trace.cache x = some y)
    (chain : RecordedChain enc calls rows h seed values) :
    ∃ e : Evaluation enc calls trace, e.height = h ∧ e.seed = seed ∧
      trace.output (e.row (calls h-1)) = values (calls h-1) := by
  classical
  have found (j : Nat) (inside : j < calls h) :
      ∃ i, trace.input i = stageInput enc h seed values j ∧ trace.output i = values j :=
    cache_has_row trace _ _ (stored _ _ (chain.observed j inside))
  let row (j : Nat) : Fin trace.size :=
    if inside : j < calls h then (found j inside).choose else (found 0 chain.positive).choose
  have atRow (j : Nat) (inside : j < calls h) :
      trace.input (row j) = stageInput enc h seed values j ∧ trace.output (row j) = values j := by
    dsimp only [row]
    rw [dif_pos inside]
    exact (found j inside).choose_spec
  let e : Evaluation enc calls trace := {
    height := h
    seed := seed
    positive := chain.positive
    bounded := chain.bounded
    row := row
    first := by simpa [stageInput] using (atRow 0 chain.positive).1
    next := by
      intro j inside
      simpa [stageInput,(atRow j (by omega)).2] using (atRow (j+1) inside).1 }
  exact ⟨e,rfl,rfl,(atRow (calls h-1) (by have := chain.positive; omega)).2⟩

theorem recorded_collision_bad {enc calls width rows} (trace : Chained.Trace)
    (stored : ∀ x y, PublicRow.compression x y ∈ rows → trace.cache x = some y)
    (collision : RecordedCollision enc calls width rows) : FinalCollision enc calls width trace := by
  obtain ⟨h,a,b,va,vb,different,left,right,same⟩ := collision
  obtain ⟨ea,ha,sa,oa⟩ := recorded_chain_evaluation trace stored left
  obtain ⟨eb,hb,sb,ob⟩ := recorded_chain_evaluation trace stored right
  have ia : ea.identity = (h,a) := Prod.ext ha sa
  have ib : eb.identity = (h,b) := Prod.ext hb sb
  refine ⟨h,a,b,different,⟨ea,ia⟩,⟨eb,ib⟩,?_⟩
  have fa : finalOutput enc calls trace (h,a) = va (calls h-1) := by
    rw [← ia,finalOutput_of_evaluation]
    simpa only [ha] using oa
  have fb : finalOutput enc calls trace (h,b) = vb (calls h-1) := by
    rw [← ib,finalOutput_of_evaluation]
    simpa only [hb] using ob
  simpa only [fa,fb] using same

theorem recorded_failure_bad {enc calls width rows} (s : Observer.State) (valid : Observer.Valid s)
    (stored : ∀ row ∈ rows, JointOracle238.Stores s.base row)
    (failure : RecordedFailure enc calls width rows) : Stopped.rawBad enc calls width s := by
  rcases failure with leaf | collision
  · left
    apply pinned_witness_bad_width 238 (by decide)
      ⟨pinnedPeerSalt,pinned_first_peer,pinned_second_peer⟩ s.base.trace rows ?_ leaf
    exact fun x y present => stored _ present
  · right
    apply recorded_collision_bad s.graph ?_ collision
    intro x y present
    exact (congrArg (fun cache : CompressionCache => cache x) valid.1).symm.trans (stored _ present)

end CommitGolfCandidate.Chained
