import CommitGolfCandidate.RungARefBase
set_option Elab.async false
set_option maxHeartbeats 700000
namespace CommitGolfCandidate.RungA
open CommitGolf
open Late (levelCount node)
attribute [local irreducible] Late.treeNode rebuildDigest Late.initialList leafAt tree S4Hiding.tree Late.slice
private theorem honestCalc (H : Compression) (td : Late.Trapdoor) (base : Nat→Late.Digest)
    (rows : ∀ i : Index,H (Late.slice td (finalRowAddress i.val) 96)=base i.val)
    (gaps : ∀ h p k,Late.Padding h p k → Late.slice td (Late.unusedSlotAddr h p k) 32=0)
    (h j : Nat) (bound : h≤4) : rebuildDigest H td h j=Late.treeNode H base h j := by
  induction h generalizing j with
  | zero=>
    apply (r0 H td j).trans;apply Eq.trans _ (t0 H base j).symm
    apply ite_congr rfl _ (fun _=>rfl)
    intro real
    let i : Index:=⟨j,real⟩
    exact rows i
  | succ h ih=>
    apply (rn H td h j).trans;apply Eq.trans _ (tn H base h j).symm
    apply ite_congr rfl _ (fun _=>rfl)
    intro real
    apply congrArg (S4.retained S4.active (h+1));apply congrArg (fun x : Late.Block=>H x)
    let c:=Late.treeNode H base h
    have atLane (k : Nat) (bk:k<3) : physicalLane H td h j k=if k<S4.radix h then c (S4.radix h*j+k) else 0 := by
      unfold physicalLane
      by_cases legal:k<S4.radix h
      · rw [if_pos legal];by_cases rx:S4.radix h*j+k<levelCount h
        · rw [if_pos ⟨legal,rx⟩];exact ih _ (by omega)
        · rw [if_neg (by tauto)];exact (gaps _ _ _ ⟨by omega,real,bk,Or.inr (by omega)⟩).trans (Late.missing_node _ _ _ _ (by omega)).symm
      · rw [if_neg legal,if_neg (by tauto)];exact gaps _ _ _ ⟨by omega,real,bk,Or.inl (by omega)⟩
    unfold joined S4.row
    rw [atLane 2 (by decide),atLane 1 (by decide),atLane 0 (by decide)]
    cases h <;> simp only [S4.radix,ite_true,ite_false,reduceCtorEq,Nat.add_zero] <;> rfl
theorem honestDigest {o m r td} (f : FusedTrapdoor .twentyFour o m r td)
    (h j : Nat) (bound : h≤4) : rebuildDigest o.compression td h j=node (tree o m r) h j :=
  (honestCalc o.compression td (leafAt o m r) (fun i=>(congrArg o.compression (f.rows i)).trans (leafAt_eq o m r i).symm) f.gaps h j bound).trans (refNode o m r h j (by omega)).symm
end CommitGolfCandidate.RungA
