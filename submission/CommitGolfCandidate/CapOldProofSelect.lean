import CommitGolfCandidate.CapOldPathGeometry
import CommitGolfCandidate.CapOldProofSlots

namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

def CapOldSiblingWitness (positions : Positions) (height node : Nat) : Prop :=
  ∃ ordinal < positions.card,
    (((LENGTH+openingIndex positions ordinal)/2^(16+height)) ^^^ 1)=node

noncomputable def capOldBoundaryOrdinal (positions : Positions) (height node : Nat) : Nat := by
  classical
  exact if available : CapOldSiblingWitness positions height node then Nat.find available else 0

theorem cap_old_boundary_ordinal (positions : Positions) (height node : Nat)
    (available : CapOldSiblingWitness positions height node) :
    capOldBoundaryOrdinal positions height node < positions.card ∧
      (((LENGTH+openingIndex positions (capOldBoundaryOrdinal positions height node)) /
        2^(16+height)) ^^^ 1)=node := by
  classical
  rw [capOldBoundaryOrdinal,dif_pos available]
  exact Nat.find_spec available

noncomputable def capOldBoundaryBytes (positions : Positions) (proof : Proof) :
    Nat → Nat → Proof
  | 0, node =>
      if capOpenRequestedMarks positions node then []
      else capOldProofSlot proof (capOldBoundaryOrdinal positions 0 node) 17
  | height+1, node =>
      if capOpenRequestedMarks positions node then
        capOldBoundaryBytes positions proof height (2*node) ++
          capOldBoundaryBytes positions proof height (2*node+1)
      else capOldProofSlot proof (capOldBoundaryOrdinal positions (height+1) node)
        (17+(height+1))

private theorem child_bounds (height node : Nat)
    (lower : 256 ≤ node*2^(height+1)) (upper : (node+1)*2^(height+1) ≤ 512) :
    256 ≤ (2*node)*2^height ∧ (2*node+1)*2^height ≤ 512 ∧
      256 ≤ (2*node+1)*2^height ∧ (2*node+2)*2^height ≤ 512 := by
  have power := Nat.two_pow_pos height
  rw [pow_succ] at lower upper
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem unknown_slot (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (height node : Nat) (heightBound : height < 8)
    (lower : 256 ≤ node*2^height) (upper : (node+1)*2^height ≤ 512)
    (parent : capOpenRequestedMarks positions (node/2)=true)
    (absent : capOpenRequestedMarks positions node=false) :
    capOldProofSlot (referenceOpening heap salt positions)
      (capOldBoundaryOrdinal positions height node) (17+height) =
      digestBytes (heap node) := by
  have available := cap_unknown_old_sibling positions height node
    heightBound lower upper parent absent
  have selected := cap_old_boundary_ordinal positions height node available
  rw [cap_old_reference_slot heap salt positions _ _ selected.1 (by omega)]
  have part : 17+height≠0 := by omega
  have level : 17+height-1=16+height := by omega
  simp only [referenceOpeningDigest,if_neg part,level]
  exact congrArg (fun input => digestBytes (heap input)) selected.2

theorem cap_old_boundary_bytes (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (height node : Nat)
    (heightBound : height ≤ 8)
    (lower : 256 ≤ node*2^height) (upper : (node+1)*2^height ≤ 512)
    (active : capOpenRequestedMarks positions node=true ∨
      (height < 8 ∧ capOpenRequestedMarks positions (node/2)=true)) :
    capOldBoundaryBytes positions (referenceOpening heap salt positions) height node =
      capDigestEncoding
        ((capSubtreeBoundaries (capOpenRequestedMarks positions) height node).map heap) := by
  induction height generalizing node with
  | zero =>
    by_cases marked : capOpenRequestedMarks positions node=true
    · simp only [capOldBoundaryBytes,capSubtreeBoundaries,marked,ite_true,
        List.map_nil,capDigestEncoding,List.flatMap_nil]
    · have absent := Bool.eq_false_iff.mpr marked
      obtain ⟨small,parent⟩ := active.resolve_left marked
      simp only [capOldBoundaryBytes,capSubtreeBoundaries,absent,ite_false,
        List.map_cons,List.map_nil,capDigestEncoding,List.flatMap_cons,
        List.flatMap_nil,List.append_nil]
      exact unknown_slot heap salt positions 0 node small lower upper parent absent
  | succ height ih =>
    by_cases marked : capOpenRequestedMarks positions node=true
    · obtain ⟨ll,lu,rl,ru⟩ := child_bounds height node lower upper
      have leftParent : 2*node/2=node := by omega
      have rightParent : (2*node+1)/2=node := by omega
      rw [capOldBoundaryBytes,if_pos marked,capSubtreeBoundaries,if_pos marked,
        List.map_append]
      change _ = capDigestEncoding (_ ++ _)
      rw [capDigestEncoding,List.flatMap_append]
      rw [ih (2*node) (by omega) ll lu
        (Or.inr ⟨by omega,by simpa only [leftParent] using marked⟩),
        ih (2*node+1) (by omega) rl ru
        (Or.inr ⟨by omega,by simpa only [rightParent] using marked⟩)]
      rfl
    · have absent := Bool.eq_false_iff.mpr marked
      obtain ⟨small,parent⟩ := active.resolve_left marked
      simp only [capOldBoundaryBytes,capSubtreeBoundaries,absent,ite_false,
        List.map_cons,List.map_nil,capDigestEncoding,List.flatMap_cons,
        List.flatMap_nil,List.append_nil]
      exact unknown_slot heap salt positions (height+1) node
        small lower upper parent absent

end CommitGolfCandidate
