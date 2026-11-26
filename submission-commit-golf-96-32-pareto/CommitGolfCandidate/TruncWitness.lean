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

attribute [local irreducible] storeNode leafDigest

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

def openingInputs (H : Compression) (i : Index) (salt : Salt) (value : Entry) (p : List (Bool × Digest)) :=
  leafChainInputs H i salt value ++ pathInputs H (LENGTH+i.val) (leafDigest H i salt value) p

theorem openingWitness (H : Compression) (i : Index) (s t : Salt) (v w : Entry) (p q : List (Bool × Digest))
    (dirs : p.map Prod.fst=q.map Prod.fst) (diff : v≠w)
    (same : climb H (LENGTH+i.val) (leafDigest H i s v) p=climb H (LENGTH+i.val) (leafDigest H i t w) q) :
    ∃ x∈openingInputs H i s v p, ∃ y∈openingInputs H i t w q, x≠y ∧ low240 (H x)=low240 (H y) := by
  by_cases e : leafDigest H i s v=leafDigest H i t w
  · have eq0 : CommitGolfCandidate.climb H (leafDigest H i s v) []=CommitGolfCandidate.climb H (leafDigest H i t w) [] := e
    obtain ⟨x,hx,y,hy,d,he⟩ := collision_of_openings_eq H i s t v w [] [] rfl diff eq0
    have clean (a : Salt) (m : Entry) : CommitGolfCandidate.openingInputs H i a m []=leafChainInputs H i a m := by
      simp only [CommitGolfCandidate.openingInputs,CommitGolfCandidate.pathInputs,List.append_nil]
    rw [clean] at hx hy
    exact ⟨x,List.mem_append_left _ hx,y,List.mem_append_left _ hy,d,congrArg low240 he⟩
  · obtain ⟨x,hx,y,hy,d,he⟩ := pathWitness H _ _ _ p q dirs e same
    exact ⟨x,List.mem_append_right _ hx,y,List.mem_append_right _ hy,d,he⟩

end CommitGolfCandidate.Trunc
