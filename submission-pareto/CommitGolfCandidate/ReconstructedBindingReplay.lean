import CommitGolfCandidate.ReconstructedBindingProbability
import CommitGolfCandidate.JointOracle241Sampling
import CommitGolfCandidate.TwoPermutationPinnedLeafWidth
import CommitGolfCandidate.TwoPermutationPinnedPeerLayout

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.JointOracle241 TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def compressionRow : PublicRow → Option (Key × Digest)
  | .compression k y => some (decodeKey k,unpack y)
  | .permutation _ _ => none

def history (rows : List PublicRow) : History := rows.filterMap compressionRow

theorem mem_history (rows : List PublicRow) (k : Key) (v : Digest) :
    (k,v) ∈ history rows ↔ PublicRow.compression (encodeKey k) (pack v) ∈ rows := by
  constructor
  · intro hr
    obtain ⟨row,mem,eq⟩ := List.mem_filterMap.1 hr
    cases row with
    | compression a b =>
      change some (decodeKey a,unpack b) = some (k,v) at eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eq)
      simpa using mem
    | permutation _ _ => cases eq
  · intro mem
    exact List.mem_filterMap.2 ⟨.compression (encodeKey k) (pack v),mem,by simp [compressionRow]⟩

private theorem read_history {s : State} {rows : List PublicRow}
    (stored : ∀ row ∈ rows, Stores s row) {k : Key} {v : Digest} (h : (k,v) ∈ history rows) :
    table s k = some v := by
  have hv : cacheFn s (encodeKey k) = some (pack v) := stored _ ((mem_history rows k v).1 h)
  simp [table,hv]

private theorem read_probe {m : Table} {C : Compress} {k : Key} (n : Nat)
    (reads : ∀ j, j < n → m (lastKey C k j) = some (C (lastKey C k j))) :
    probe m k n = some (lastKey C k n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun j hj => reads j (by omega))
    simp [probe,lastKey,hp,reads n (by omega)]

private theorem finish_recorded {s : State} {rows : List PublicRow} {C : Compress}
    (stored : ∀ row ∈ rows, Stores s row)
    (seed : Seed) (trace : recorded (history rows) C seed.key (work seed.depth-1)) :
    finish (table s) seed = some (C (lastKey C seed.key (work seed.depth-1))) := by
  apply Option.bind_eq_some_iff.2
  refine ⟨_,read_probe _ (fun j h => read_history stored (trace j (by omega))),?_⟩
  exact read_history stored (trace _ le_rfl)

/-- A conflict witnessed by two complete authenticated paths or two pinned leaves.
The compression function is quantified because only its recorded evaluations are used. -/
def ReplayWitness (rows : List PublicRow) : Prop :=
  FullCollision (history rows) ∨ (∃ (C : Compress) (d : Fin 24), PaidCollision (history rows) C d) ∨
    PinnedLeafWitnessW 240 rows

theorem witness_bad {s : State} {rows : List PublicRow}
    (stored : ∀ row ∈ rows, Stores s row) (hit : ReplayWitness rows) : ¬ Good s := by
  intro good
  rcases hit with ⟨a,b,v,ne,ha,hb⟩ | ⟨C,d,l,r,l',r',cl,cr,cl',cr',ha,hb,ne,eq⟩ | leaf
  · exact ne (good.1 a b v (read_history stored ha) (read_history stored hb))
  · let a := Seed.ofPair d l r cr
    let b := Seed.ofPair d l' r' cr'
    have diff : a ≠ b := fun e => ne (congrArg (fun t : Seed => lastKey C t.key (work d-1)) e)
    exact good.2.1 ⟨a,b,_,_,diff,rfl,finish_recorded stored a ha,finish_recorded stored b hb,eq⟩
  · exact pinned_witness_bad_width 240 (by decide) ⟨pinnedPeerSalt,pinned_first_peer,pinned_second_peer⟩
      s.trace rows (fun x y h => stored (.permutation x y) h) leaf good.2.2

/-- Joint random-function / random-permutation probability for an adaptive adversary
and both checker replays. The event includes all 24 compression depths. -/
theorem joint_replay_bound {α : Type} (program : OracleComp World α) (q Q : Nat) (positive : 1 ≤ q)
    (replayed : Q ≤ q+2^32) (bounded : PublicQueryBound (recordRows program) Q) :
    Pr{let r ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
       ReplayWitness r.2] ≤ (q:ENNReal)/2^120 := by
  simp only [Oracle.sample,bind_assoc,pure_bind]
  rw [joint_sampling_probability]
  unfold lazyOut
  rw [prEvent_map]
  change Pr{let r ← model.run (recordRows program) State.empty}[ReplayWitness r.1.2] ≤ _
  refine (prEvent_mono_of_support _ _ _ (fun r hr hit =>
    witness_bad (recorded_stores program State.empty r hr).2 hit)).trans ?_
  exact lazy_replay_bound (recordRows program) q Q positive replayed bounded

end CommitGolfCandidate.Reconstruction.Binding
