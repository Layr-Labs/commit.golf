import CommitGolfCandidate.TruncModel
namespace CommitGolfCandidate.Trunc
open CommitGolf

private theorem append_injective {left right left' right' : Digest}
    (h : right ++ left = right' ++ left') : left = left' ∧ right = right' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 0 256) h
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 256 256) h

attribute [local irreducible] storeNode

theorem pathWitness (H : Compression) (n : Nat) (v w : Digest) (p q : List (Bool × Digest))
    (dirs : p.map Prod.fst=q.map Prod.fst) (diff : v≠w) (same : climb H n v p=climb H n w q) :
    ∃ x∈pathInputs H n v p, ∃ y∈pathInputs H n w q, x≠y ∧ low240 (H x)=low240 (H y) := by
  induction p generalizing n v w q with
  | nil => cases q <;> simp_all [climb]
  | cons a ps ih =>
    cases q with
    | nil => simp at dirs
    | cons b qs =>
      obtain ⟨dir,dirs'⟩ := List.cons.inj dirs
      let x:=pathInput v a
      let y:=pathInput w b
      have ne : x≠y := by
        intro hit
        rcases a with ⟨r,l⟩
        rcases b with ⟨r',l'⟩
        change r=r' at dir
        subst r'
        cases r <;> simp only [x,y,pathInput,Bool.false_eq_true,ite_true,ite_false] at hit
        · exact diff (append_injective (padInput_injective hit)).1
        · exact diff (append_injective (padInput_injective hit)).2
      by_cases next : storeNode (n/2) (H x)=storeNode (n/2) (H y)
      · exact ⟨x,List.mem_cons_self ..,y,List.mem_cons_self ..,ne,(low_store _ _).symm.trans ((congrArg low240 next).trans (low_store _ _))⟩
      · obtain ⟨c,hc,d,hd,cd,low⟩ := ih (n/2) _ _ qs dirs' next same
        exact ⟨c,List.mem_cons_of_mem _ hc,d,List.mem_cons_of_mem _ hd,cd,low⟩

end CommitGolfCandidate.Trunc
