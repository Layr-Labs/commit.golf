import CommitGolfCandidate.R4bSchedule
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Open (targetAddr siblingAddress tdBase)
theorem binaryWord (g lo j : Nat) (bg : g<2) (bl : lo<128) (bj : j<7) :
    slotWord (1024*g+8*lo+j)= Late.rowAddress (7*g+j+1) (lo/2^(j+1))+32*(1-(lo/2^j)%2) := by
  unfold slotWord
  rw [if_pos (by omega),show (1024*g+8*lo+j)/1024=g by omega,
    show (1024*g+8*lo+j)%8=j by omega,if_neg (by omega),show (1024*g+8*lo+j)%1024/8=lo by omega]

private theorem ternaryWord (i q : Nat) (hq : q=1 ∨ q=2) :
    slotWord (virtualSlot i q)=32*((i%3+q)%3) := by
  have v : i%3<3:=Nat.mod_lt _ (by decide)
  rcases hq with rfl|rfl <;> interval_cases u:i%3 <;> simp [virtualSlot,slotWord,u]

private theorem bigWord (i h : Nat) (bh : h<14) :
    slotWord (virtualSlot i (h+3))=
    Late.rowAddress (h+1) ((blockIndex i (group h)%128)/2^(part h+1))+
      32*(1-((blockIndex i (group h)%128)/2^(part h))%2) := by
  simp only [virtualSlot,show ¬h+3<3 by omega,ite_false,Nat.add_sub_cancel,Nat.mod_eq_of_lt bh]
  unfold tableRow
  rw [binaryWord (group h) (blockIndex i (group h)%128) (part h) (by unfold group;omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  rw [show 7*group h+part h=h by unfold group part;omega]

theorem sourceEq (i : Index) (q : Nat) (bq : q<17) : logicalSource i.val q=targetAddr i q := by
  by_cases z:q=0
  · subst q;rfl
  by_cases bottom:q<3
  · have eqv : q=1 ∨ q=2:=by omega
    rw [logicalSource,if_neg z,if_pos bottom,ternaryWord _ _ eqv]
    rcases eqv with rfl|rfl <;>
      simp [targetAddr,siblingAddress,Late.rowAddress,Late.levelOffset,layerOffset,childPos,nodeIndex,span,radix,tdBase] <;> omega
  let h:=q-3
  have b:h<14:=by dsimp [h];omega
  have e:q=h+3:=by dsimp [h];omega
  rw [logicalSource,if_neg z,if_neg bottom,show virtualSlot i.val q=virtualSlot i.val (h+3) by rw [←e],bigWord _ _ b,e]
  let u : Fin 14:=⟨h,b⟩
  change Late.rowAddress (u.val+1) ((blockIndex i.val (group u.val)%128)/2^(part u.val+1))+
    32*(1-((blockIndex i.val (group u.val)%128)/2^(part u.val))%2)+high i.val ((u.val+3)-3)=targetAddr i (u.val+3)
  clear_value u
  fin_cases u <;> simp [Late.rowAddress,targetAddr,siblingAddress,nodeIndex,childPos,span,radix,high,part,group,blockIndex] <;> omega

end CommitGolfCandidate.R4b
