import CommitGolfCandidate.PairPrefix
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf
set_option maxRecDepth 8000
attribute [local irreducible] lowerHash

theorem consistentIfValid (H : Compression) (input : CheckInput) (valid : BatchValid H input)
    (a b : Nat) (ha : a<128) (hb : b<128)
    (same : openingIndex input.positions a / 65536 = openingIndex input.positions b / 65536) :
    lowerHash H input a = lowerHash H input b := by
  have parentEq : openingIndex input.positions a/131072=openingIndex input.positions b/131072 := by omega
  have sideEq : (openingIndex input.positions a).testBit 16=(openingIndex input.positions b).testBit 16 := by
    simp only [Nat.testBit_eq_decide_div_mod_eq,show (2:Nat)^16=65536 by decide,same]
  have e := pairAgreement valid a ha
  dsimp only at e
  rw [parentEq,sideEq] at e
  exact Option.some.inj (e.symm.trans (pairAgreement valid b hb))

theorem prefixWitness (H : Compression) (input : CheckInput) (n : Nat) (u : Fin 256) (d : Digest)
    (e : prefixNode H input n u=some d) :
    ∃ r<n, openingIndex input.positions r/65536=u.val ∧ lowerHash H input r=d := by
  unfold prefixNode at e
  cases h : (List.range n).find? (fun r => openingIndex input.positions r / 65536 == u.val) with
  | none => simp [h] at e
  | some r =>
    have test := List.find?_some (p:=fun k => openingIndex input.positions k/65536 == u.val) h
    exact ⟨r,List.mem_range.mp (List.mem_of_find?_eq_some h),beq_iff_eq.mp test,by simpa [h] using e⟩

theorem invalidMismatch (H : Compression) (input : CheckInput) (n : Nat) (hn : n<128)
    (u : Fin 256) (index : openingIndex input.positions n/65536 = u.val) (d : Digest)
    (seen : prefixNode H input n u=some d) (different : lowerHash H input n≠d) : ¬ BatchValid H input := by
  intro valid
  obtain ⟨r,earlier,slot,eqn⟩ := prefixWitness H input n u d seen
  exact different ((consistentIfValid H input valid n r hn (by omega) (index.trans slot.symm)).trans eqn)

end CommitGolfCandidate.PairCap.Batch
