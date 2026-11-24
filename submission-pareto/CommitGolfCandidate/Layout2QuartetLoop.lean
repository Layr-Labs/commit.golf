import CommitGolfCandidate.Layout2QuartetCursor
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def payload (s : MachineState) (k : Nat) (qs : Selectors) (i : Nat) :=
  byte s (proofBase+index false k qs i)

def Indices (s : MachineState) (k : Nat) (qs : Selectors) :=
  ∀ j, j<k → s.getMem (addr (indicesBase+8*j)) &&& 3#64=addr (qs j).val

private theorem idx_pre {s m k qs} (indices : Indices s k qs) (j : Nat) (hj : j<k)
    (bound : k≤16777216) (wrote : Writes s m proofBase (534*j) (payload s k qs)) :
    m.getMem (addr (indicesBase+8*j)) &&& 3#64=addr (qs j).val := by
  let w:=1174405636+j
  have eq : 8*w=indicesBase+8*j := by dsimp [w,indicesBase];omega
  have words:=bword (s:=m) (t:=s) w (by dsimp [w,MEMORY_BYTES];omega)
    (fun b hb=>wrote.outside _ (by dsimp [w,MEMORY_BYTES];omega) (Or.inl (by dsimp [w,proofBase];omega)))
  change m.getMem (addr (8*w))=s.getMem (addr (8*w)) at words
  rw [eq] at words
  rw [words,indices j hj]

private theorem append_cell {s m t k j qs} (hj : j<k) (room : proofBase+534*k≤MEMORY_BYTES)
    (prior : Writes s m proofBase (534*j) (payload s k qs))
    (cell : Writes m t (proofBase+534*j) 534
      (fun x=>byte m (proofBase+534*j+within false (qs j) (window j) x))) :
    Writes s t proofBase (534*(j+1)) (payload s k qs) := by
  rw [show 534*(j+1)=534*j+534 by omega]
  apply prior.append
  intro a fit
  rw [cell a fit]
  dsimp only
  split
  · rename_i hit
    let x:=a-(proofBase+534*j)
    have small : x<534 := by dsimp [x];omega
    have inRange:=(within_facts false (qs j) (window j) x (by unfold window;omega) small).1
    change byte m (proofBase+534*j+within false (qs j) (window j) x)=payload s k qs (534*j+x)
    rw [prior.outside _ (by omega) (Or.inr (by omega))]
    simp only [payload,index,if_pos (show 534*j+x<534*k by omega),show (534*j+x)/534=j by omega,
      show (534*j+x)%534=x by omega,Nat.add_assoc]
  · rfl

theorem traverse {s k qs} (bound : k≤16777216) (room : proofBase+534*k≤MEMORY_BYTES)
    (indices : Indices s k qs) (n : Nat) (j : Nat) (len : k=j+n+1) (m : MachineState)
    (here : m.pc=pc 795) (cursor : Cursor m k j) (kept : Kept temps s m)
    (prior : Writes s m proofBase (534*j) (payload s k qs)) :
    ∃ t steps, steps≤65*(n+1) ∧ Runs checkImage m t steps steps ∧ t.pc=pc 786 ∧
      Writes s t proofBase (534*k) (payload s k qs) ∧ Kept temps s t := by
  induction n generalizing j m
  all_goals
    have hj : j<k := by omega
    let q:=qs j
    have valid : accessValid (m.getReg .x9) 8=true := by
      rw [cursor.ix];apply Layout2Writer.access8 <;> simp only [indicesBase,MEMORY_BYTES] <;> omega
    have sel : m.getMem (m.getReg .x9) &&& 3#64=addr q.val := by
      rw [cursor.ix];exact idx_pre indices j hj bound prior
    obtain ⟨a,ra,pa,ma,ka⟩:=dispatch m q here valid sel
    have ca:=cursor.lift (t:=a) (fun r h=>ka r (by rcases h with h|h|h|h <;> subst r <;> decide))
    obtain ⟨b,rb,pb,written,kb⟩:=cell_run a j q ca.dst (by omega) pa
    have cb:=ca.lift (t:=b) (fun r h=>kb r (by rcases h with h|h|h|h <;> subst r <;> decide)
      (by rcases h with h|h|h|h <;> subst r <;> decide))
    obtain ⟨c,rc,pcC,mc,kc⟩:=jumpTail b q pb
    have cc:=cb.lift (t:=c) (fun r _=>kc r)
    obtain ⟨d,rd,pd,md,newLeft,kd⟩:=remaining cc hj bound pcC
    have writes:= (append_cell hj room (prior.move rfl ma) written).move rfl (md.trans mc)
    have saved : Kept temps s d := by
      intro r f
      have h : r≠.x5 ∧ r≠.x28 ∧ r≠.x29 ∧ r≠.x18 := by cases r <;> simp_all [temps]
      rw [kd r h.2.2.2,kc r,kb r h.2.1 h.2.2.1,ka r h.1,kept r f]
    have ran:=((ra.thenDo rb).thenDo rc).thenDo rd
    have cost : dispatchCost q≤9 := by unfold dispatchCost;have:=q.isLt;split <;> omega
  case zero =>
    have last : j+1=k := by omega
    rw [if_pos last] at pd
    rw [last] at writes
    exact ⟨d,_,by omega,ran,pd,writes,saved⟩
  case succ n ih =>
    have more : j+1≠k := by omega
    rw [if_neg more] at pd
    obtain ⟨e,u,ub,ru,pe,me,ce,ke⟩:=bump
      (by rw [kd _ (by decide)];exact cc.dst) (by rw [kd _ (by decide)];exact cc.ix)
      newLeft (by rw [kd _ (by decide)];exact cc.phase) pd
    obtain ⟨z,f,fb,rf,pz,wz,kz⟩:=ih (j+1) (by omega) e pe ce (saved.trans ke) (writes.move rfl me)
    exact ⟨z,_,by omega,(ran.thenDo ru).thenDo rf,pz,wz,kz⟩

end CommitGolfCandidate.Layout2.Quartet
