import CommitGolfCandidate.ReconstructedHidingFrame
import CommitGolfCandidate.ReconstructedHidingHonestFlag

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1900000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler
attribute [local irreducible] blockSplit tapeFromReplies publicBlocks packedAddress

def oldRowHit (c : Cache) (v : Key × GenReplies) := ∃ r ∈ c.entries,prefixMark r v
def rawKeyHit (xs : List Reply) (v : Key × GenReplies) := ∃ x ∈ xs,keyHit x v.1
def oldTailHit (c : Cache) (v : Key × GenReplies) := ∃ j : Fin groupCount, ∃ i : Fin c.entries.length,
  signature ((blockSplit (v.2 j)).1)=tailSignature (outputTail c.entries[i].2)

def baseGood (c : Cache) (xs : List Reply) (v : Key × GenReplies) :=
  ¬oldRowHit c v ∧ ¬rawKeyHit xs v ∧ ¬oldTailHit c v ∧ Function.Injective (publicBlocks blockSplit v.2)

noncomputable def baseCost (seen raw : Nat) : ℝ := seen*(1/2^120+(groupCount:ℝ)/2^1600) + raw/2^192 +
  (groupCount:ℝ)*seen/2^360 + (groupCount:ℝ)*groupCount/2^1440

theorem real_event_or {A : Type} (d : ProbComp A) (P R : A → Prop) :
    (Pr{let a ← d}[P a ∨ R a]).toReal ≤ (Pr{let a ← d}[P a]).toReal + (Pr{let a ← d}[R a]).toReal := by
  have n := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _,prEvent_ne_top _⟩) (prEvent_or_le d P R)
  rwa [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at n

private theorem uniform_real_bound {X : Type} {sa sb : SampleableType X} {ev : X → Prop} {n : ℝ}
    (h : (Pr{let v ← @uniformSample X sa}[ev v]).toReal ≤ n) : (Pr{let v ← @uniformSample X sb}[ev v]).toReal ≤ n :=
  (congrArg ENNReal.toReal (@uniform_versions X sb sa ev)).le.trans h

theorem base_cost_bound (c : Cache) (xs : List Reply) :
    (Pr{let v ← $ᵗ (Key × GenReplies)}[¬baseGood c xs v]).toReal ≤ baseCost c.entries.length xs.length := by
  classical
  let D := ($ᵗ (Key × GenReplies))
  let P := oldRowHit c
  let R := rawKeyHit xs
  let T := oldTailHit c
  let F := fun v : Key × GenReplies => ¬Function.Injective (publicBlocks blockSplit v.2)
  have cover (v : Key × GenReplies) : (¬baseGood c xs v) ↔ (P v ∨ R v ∨ T v ∨ F v) := by
    simp only [baseGood,P,R,T,F]
    tauto
  have whole := real_event_or D P (fun v => R v ∨ T v ∨ F v)
  have mid := real_event_or D R (fun v => T v ∨ F v)
  have last := real_event_or D T F
  have pr : Pr{let v ← D}[P v] ≤ c.entries.length * (1/2^120 + (groupCount:ENNReal)/2^1600) :=
    uniform_bound_of (prefix_row_payment c)
  have rr : Pr{let v ← D}[R v] ≤ (xs.length:ENNReal)/2^192 := uniform_bound_of (prefix_key_payment xs)
  have tr : Pr{let v ← D}[T v] ≤ (groupCount:ENNReal)*c.entries.length/2^360 := uniform_bound_of (prefix_signature_payment c)
  have ff : (Pr{let v ← D}[F v]).toReal ≤ (groupCount:ℝ)*groupCount/2^1440 :=
    uniform_real_bound prefix_duplicate_payment
  have pp := ENNReal.toReal_mono (by finiteness) pr
  have rp := ENNReal.toReal_mono (by finiteness) rr
  have tp := ENNReal.toReal_mono (by finiteness) tr
  have plus : (1/2^120 + (groupCount:ENNReal)/2^1600).toReal = (1/2^120:ENNReal).toReal+((groupCount:ENNReal)/2^1600).toReal :=
    ENNReal.toReal_add (by finiteness) (by finiteness)
  simp only [plus,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,
    ENNReal.toReal_one] at pp rp tp
  have eq : (fun v => ¬baseGood c xs v) = fun v => P v ∨ R v ∨ T v ∨ F v :=
    funext (fun v => propext (cover v))
  rw [eq]
  unfold baseCost
  linarith only [whole,mid,last,pp,rp,tp,ff]

theorem base_gen_cache (c : Cache) (xs : List Reply) (v : Key × GenReplies) (ok : baseGood c xs v) :
    cacheAllow (genPermit v.1 v.2) c=true := by
  refine List.all_eq_true.mpr (fun row seen => (gen_permit_iff _ _ _ _).mpr ⟨?_,?_⟩)
  · intro j agree
    exact ok.1 ⟨row,seen,Or.inl (Or.inl (agree ▸ address_key_hit v.1 j))⟩
  · intro j agree
    exact ok.1 ⟨row,seen,Or.inr ⟨j,agree⟩⟩

theorem base_first_safe (c : Cache) (left right : Message) (v : Key × GenReplies)
    (ok : baseGood c (pinnedFirstAddresses left right) v) (b : Bool) (i : Index) :
    ¬keyHit (honestFirst (if b then right else left) i) v.1 :=
  fun bad => ok.2.1 ⟨_,pinned_first_address_mem left right b i,bad⟩

theorem base_replies_inj (c : Cache) (xs : List Reply) (v : Key × GenReplies) (ok : baseGood c xs v) :
    Function.Injective v.2 := by
  intro i j equal
  apply ok.2.2.2
  unfold publicBlocks
  exact congrArg (fun b => (blockSplit b).1) equal

theorem base_closed_safe (c : Cache) (xs : List Reply) (p : Finset Position) (v : VisibleGenerator p)
    (s : Secrets (ClosedIx p)) (ok : baseGood c xs ((openingGenerators p).symm (v,s))) :
    ¬prefixHit c Subtype.val s.1.2 := by
  rintro ⟨row,seen,i,htag,hval⟩
  have combined : tapeFromReplies (proposedReplies (knownBlocks p v.1 v.2) s) i.val = s.1.2 i := by
    rw [opening_salts]; exact dite_eq_right i.property
  exact ok.1 ⟨row,seen,Or.inl (Or.inr ⟨i.val,htag,hval.trans combined.symm⟩)⟩

end CommitGolfCandidate.Reconstruction.HidingTape
