import CommitGolfCandidate.ReconstructedHidingProtected
import CommitGolfCandidate.ReconstructedHidingTrace

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
noncomputable local instance jointFnSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _

theorem address_key_hit (k : Key) (j : Fin groupCount) : keyHit (packedAddress k j) k := by
  refine ⟨(groupIndex j).1,(groupIndex j).2,?_⟩
  ·
    intro word within
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    let idx : Fin 1600 := ⟨64*word+b,by omega⟩
    have bit := packedAddress_bit k j idx
    simp only [BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
    rw [show 64*word+b=idx.val from rfl,bit]
    change _ = (inputWord _ _ k (idx.val/64)).getLsbD (idx.val%64)
    rw [show idx.val/64=word by dsimp [idx]; omega,show idx.val%64=b by dsimp [idx]; omega]

noncomputable def genRows {I : Type} (blocks : (I → Salt) → Group → SaltBlock) (s : Secrets I) : List Row :=
  List.ofFn fun i : Fin groupCount => (packedAddress s.1.1 i,blockSplit.symm (blocks s.1.2 (groupIndex i),s.2 (groupIndex i)))

theorem gen_input {I : Type} (blocks : (I → Salt) → Group → SaltBlock) (s : Secrets I) (e : Row)
    (member : e ∈ genRows blocks s) : keyHit e.1 s.1.1 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  exact address_key_hit s.1.1 i

theorem gen_output {I : Type} (blocks : (I → Salt) → Group → SaltBlock) (s : Secrets I) (e : Row)
    (member : e ∈ genRows blocks s) : ∃ g, blockSplit.symm (blocks s.1.2 g,s.2 g)=e.2 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  exact ⟨groupIndex i,rfl⟩

section Rows
variable {I : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256) (blocks : (I → Salt) → Group → SaltBlock)
    (gate : Secrets I → Prop)

def addRows (r : Paired) (extra : List Row) : Paired := (r.1++extra,r.2++extra)

theorem extra_member (r : Paired) (extra : List Row) (e : Row) :
    (e ∈ (addRows r extra).1++(addRows r extra).2) ↔ (e ∈ r.1++r.2 ∨ e ∈ extra) := by
  simp only [addRows,List.mem_append]
  tauto

noncomputable def jointRows (s : Secrets I) : ProbComp Paired := by
  classical exact if gate s then (fun r => addRows r (genRows blocks s)) <$> pairedRows state pos first msg digest s.1.2
    else pure ([],[])

noncomputable def jointSample := ($ᵗ (Secrets I)) >>= jointRows state pos first msg digest blocks gate

attribute [local irreducible] pairedRows pinnedRowsNonce tagHit keyHit genRows

theorem joint_number (rows : Paired) (seen : rows ∈ support (jointSample state pos first msg digest blocks gate)) :
    (rows.1++rows.2).length ≤ 2*Fintype.card I+2*groupCount := by
  classical
  unfold jointSample at seen
  obtain ⟨s,_,occurs⟩ := (mem_support_bind_iff _ _ _).mp seen
  unfold jointRows at occurs
  split at occurs
  · rw [support_map] at occurs
    obtain ⟨r,draw,rfl⟩ := occurs
    have bound := (paired_support state pos first msg digest s.1.2 r draw).1
    simp only [addRows,List.length_append,genRows,List.length_ofFn] at bound ⊢
    omega
  · simp only [support_pure,Set.mem_singleton_iff] at occurs
    subst rows
    exact Nat.zero_le _

theorem joint_input [DecidableEq I] (unique : Function.Injective pos) (x : Reply) :
    Pr{let rows ← jointSample state pos first msg digest blocks gate}[x ∈ rowInputs rows] ≤ 1/2^120 := by
  classical
  let latent := reverseUpper state.high
  let bad := chosenHit pos blocks latent (.forward x)
  have off (s : Secrets I) (_ : s ∈ support ($ᵗ (Secrets I))) (clean : ¬bad s) :
      Pr{let r ← jointRows state pos first msg digest blocks gate s}[x ∈ rowInputs r] ≤ 0 := by
    unfold jointRows
    split
    · rw [prEvent_map]
      apply le_of_eq
      apply prEvent_eq_zero_of_forall_mem_support
      intro r seen included
      obtain ⟨e,found,eq⟩ := (left_member _ x).mp included
      rcases (extra_member _ _ _).mp found with leaf|gen
      · exact clean (Or.inr (eq ▸ (paired_support state pos first msg digest s.1.2 r seen).2 e leaf))
      · exact clean (Or.inl (eq ▸ gen_input blocks s e gen))
    · simp [rowInputs]
      exact Finset.notMem_empty _
  have bound := prEvent_bind_le_prEvent_add_of_support ($ᵗ (Secrets I))
    (jointRows state pos first msg digest blocks gate) bad (fun r => x ∈ rowInputs r) off
  rw [add_zero] at bound
  exact bound.trans (chosen_endpoint_le pos unique blocks latent (.forward x))

end Rows

end CommitGolfCandidate.Reconstruction.HidingTape
