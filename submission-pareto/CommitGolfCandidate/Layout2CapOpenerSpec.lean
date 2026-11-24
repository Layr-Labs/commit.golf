import CommitGolfCandidate.Layout2CapCodec
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf
/-- It suffices to establish these local bytes, with no checker-state premises. -/
theorem encoder_of_blocks (p : Positions) (old actual : Proof)
    (length : actual.length=old.length)
    (records : ∀ j,j<old.length → j<534*p.card →
      actual[j]?.getD 0=(Quartet.encoder p old)[j]?.getD 0)
    (caps : ∀ g j, j<952 → 534*p.card+(952*g+j)<old.length →
      actual[534*p.card+(952*g+j)]?.getD 0 =
        gather enc (if g<(old.length-534*p.card)/952 then 32 else tag ((old.length-534*p.card)%952))
          (fun z=>(Quartet.encoder p old)[534*p.card+(952*g+z)]?.getD 0) j) :
    actual=encoder p old := by
  apply List.ext_getElem (by simpa using length)
  intro i hA hE
  have hi : i<old.length := length ▸ hA
  have val:=read_transform enc p.card (Quartet.encoder p old) i (by simpa using hi)
  have eq : actual[i]?.getD 0=(encoder p old)[i]?.getD 0 := by
    unfold encoder;rw [val,Quartet.encoder_length]
    by_cases done : 534*p.card ≤ i
    · rw [if_pos done]
      let x:=i-534*p.card
      let g:=x/952
      let j:=x%952
      have small : j<952 := by unfold j;omega
      have atI : 534*p.card+(952*g+j)=i := by dsimp [g,j,x];omega
      have atX : 952*g+j=x := by dsimp [g,j];omega
      have claim:=caps g j small (by rwa [atI])
      rw [atI] at claim
      change _=atByte enc _ _ x
      rw [←atX,at_chunk _ _ _ _ _ small]
      exact claim
    · rw [if_neg done];exact records i hi (by omega)
  simpa only [List.getElem?_eq_getElem hA,List.getElem?_eq_getElem hE,Option.getD_some] using eq
end CommitGolfCandidate.Layout2.Cap
