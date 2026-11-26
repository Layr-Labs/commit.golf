import CommitGolfCandidate.ReconstructedHidingJointObserver

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 2100000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] jointFnSampler
attribute [local irreducible] jointSample jointRows drawRowSeed joinedRows permitSets blockSplit signature tailSignature
  cacheTrace pairedRows rowInputs rowOutputs
local instance lossDiscrete {α : Type} : MeasurableSpace α := ⊤

private theorem input_card (r : Paired) : (rowInputs r).card ≤ (r.1++r.2).length := by
  unfold rowInputs
  exact (List.toFinset_card_le _).trans_eq (List.length_map (f := Prod.fst))

private theorem output_card (r : Paired) : (rowOutputs r).card ≤ (r.1++r.2).length := by
  unfold rowOutputs
  exact (List.toFinset_card_le _).trans_eq (List.length_map (f := Prod.snd))

noncomputable def combinedPostError (n q : Nat) : ℝ :=
  (q:ℝ)*(rowRate n+(2*n+2*groupCount:ℝ)/((2:ℝ)^1600-2^122))

theorem joint_observer_loss {I A : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count) (pos : I → Position)
    (unique : Function.Injective pos) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256) (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (low : PinnedLowTape) (blocks : (I → Salt) → Group → SaltBlock) (gate : Secrets I → Prop)
    (gives : ∀ s, gate s → Function.Injective (blocks s.1.2) ∧
       ∀ g hi, (reverseUpper state.high hi).isSome → signature (blocks s.1.2 g) ≠ tailSignature hi)
    (excludes : ∀ row ∈ (state.high.realize low).entries, ∀ s, gate s → ∀ g,
      blockSplit.symm (blocks s.1.2 g,s.2 g) ≠ row.2)
    (c : Compression) (g : OracleComp World A) (q : Nat) (limited : QueryBounded g q) (small : q≤2^120) :
    let seeds := drawRowSeed state pos first msg digest
    let common := jointlyMarked c (state.high.realize low) seeds (joinedRows blocks gate) (fun s => gate s.1) g
    (Pr{let v ← common}[v.2=false]).toReal ≤
      (Pr{let s ← $ᵗ (Secrets I)}[¬gate s]).toReal + combinedPostError (Fintype.card I) q := by
  classical
  let seeds := drawRowSeed state pos first msg digest
  let p := jointSample state pos first msg digest blocks gate
  let rows := joinedRows blocks gate
  let ins := fun s => rowInputs (rows s)
  let outs := fun s => rowOutputs (rows s)
  let initial := fun s : RowSeed I => decide (gate s.1)
  let n := Fintype.card I
  let u := 2*n+2*groupCount
  have transport := joined_distribution state pos first msg digest blocks gate
  have mapped (e : Paired → Prop) : Pr{let s ← seeds}[e (rows s)] = Pr{let r ← p}[e r] := by
    have h := transport.prEvent_eq e
    rw [prEvent_map] at h
    exact h
  have size (s : RowSeed I) (seen : s ∈ support seeds) : ((rows s).1++(rows s).2).length ≤ u := by
    apply joint_number state pos first msg digest blocks gate
    rw [←support_eq_of_evalDistEq transport,support_map]
    exact ⟨s,seen,rfl⟩
  have payment (e : Paired → Prop) (max : Pr{let r ← p}[e r] ≤ 1/2^120+2*(n:ENNReal)/2^1343) :
      (Pr{let s ← seeds}[e (rows s)]).toReal ≤ rowRate n := by
    rw [mapped,←row_rate_real]
    exact ENNReal.toReal_mono (by finiteness) max
  have fits : (state.high.realize low).entries.length+q≤2^122 := by
    change (state.high.realize (fun _ => 0)).entries.length+_≤_ at enough
    rw [PinnedHighCache.entries_length] at enough ⊢
    omega
  have card : Fintype.card Reply=2^1600 := by rw [←FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
  have loss := marked_cache_loss c (state.high.realize low) seeds ins outs initial g q limited u (2^122)
    (rowRate n) (by unfold rowRate; positivity) (by rw [card]; decide) fits
    (fun s seen => (input_card (rows s)).trans (size s seen))
    (fun s seen => (output_card (rows s)).trans (size s seen))
    (fun x => payment (fun r => x ∈ rowInputs r) ((joint_input state pos first msg digest blocks gate unique x).trans le_self_add))
    (fun y => payment (fun r => y ∈ rowOutputs r) (joint_output state valid pos unique first msg digest enough blocks gate y gives))
    (fun x y known => payment (fun r => x ∈ rowInputs r ∨ y ∈ rowOutputs r) (joint_cached state valid pos unique first msg digest enough blocks gate low x y
      known (excludes (x,y) known)))
  have gateLaw := (seed_first_distribution state pos first msg digest).prEvent_eq (fun s => ¬gate s)
  rw [prEvent_map] at gateLaw
  have gateEq : (fun s : RowSeed I => initial s=false) = (fun s => ¬gate s.1) := by
    funext s; simp only [initial,decide_eq_false_iff_not]
  rw [gateEq,gateLaw,card] at loss
  simpa only [jointlyMarked,ins,outs,initial,rows,seeds,combinedPostError,Nat.cast_pow,Nat.cast_ofNat,u,Nat.cast_add,Nat.cast_mul,n]
    using loss

end CommitGolfCandidate.Reconstruction.HidingTape
