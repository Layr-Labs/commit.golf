import CommitGolfCandidate.TruncPathWitness
import CommitGolfCandidate.LateBinding
namespace CommitGolfCandidate.Late
open CommitGolf

def openingInputs (H : Compression) (i : Index) (s : Salt) (v : CommitGolf.Entry) (p : List (Bool × Digest)) :=
  inputs H (i.val.testBit 0) s v ++ Trunc.pathInputs H (LENGTH+i.val) (leaf H (i.val.testBit 0) s v) p

theorem openingWitness (H : Compression) (i : Index) (s t : Salt) (v w : CommitGolf.Entry) (p q : List (Bool × Digest))
    (dirs : p.map Prod.fst=q.map Prod.fst) (diff : v≠w)
    (same : Trunc.climb H (LENGTH+i.val) (leaf H (i.val.testBit 0) s v) p =
      Trunc.climb H (LENGTH+i.val) (leaf H (i.val.testBit 0) t w) q) :
    ∃ x∈openingInputs H i s v p, ∃ y∈openingInputs H i t w q, x≠y ∧ low240 (H x)=low240 (H y) := by
  by_cases eq : leaf H (i.val.testBit 0) s v=leaf H (i.val.testBit 0) t w
  · obtain ⟨x,hx,y,hy,ne,collision⟩:=leaf_collision H _ s t v w diff eq
    exact ⟨x,List.mem_append_left _ hx,y,List.mem_append_left _ hy,ne,congrArg low240 collision⟩
  · obtain ⟨x,hx,y,hy,ne,collision⟩:=Trunc.pathWitness H _ _ _ _ _ dirs eq same
    exact ⟨x,List.mem_append_right _ hx,y,List.mem_append_right _ hy,ne,collision⟩
end CommitGolfCandidate.Late
