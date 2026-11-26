import CommitGolfCandidate.PairArrive
import CommitGolfCandidate.PairSingle
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 300000
attribute [local irreducible] readBuffer childrenAt lowerHash execute

def pairCalls (s : MachineState) (p : Fin 128) : Nat := if flagL s p=0 ∧ flagR s p=0 then 0 else 1

theorem pairBody (o : Oracle) (input : CheckInput) (p : Fin 128) (s : MachineState)
    (inv : PairInvariant o.compression input p.val s) :
    ∃ t k,k≤20 ∧ Runs o s t k (pairCalls s p) ∧ PairEffect o.compression input p.val s t := by
  have pc : s.pc=5416 := by rw [inv.pc,if_neg (Nat.ne_of_lt p.isLt)]
  have a : Args p s := ⟨inv.slots,inv.marks,inv.source,inv.dest⟩
  have l := (inv.left p le_rfl).symm
  have r := (inv.right p le_rfl).symm
  unfold storedAt at l r
  rw [leftCell] at l;rw [rightCell] at r
  change (childrenAt o.compression input p.val).left = if flagL s p=0 then none else some (digestAt s (sourceRow p.val)) at l
  change (childrenAt o.compression input p.val).right = if flagR s p=0 then none else some (digestAt s (sourceRow p.val+32)) at r
  have ins := inv.ins p le_rfl
  have gap := inv.gap p le_rfl
  by_cases left : flagL s p=0
  · rw [if_pos left] at l
    by_cases right : flagR s p=0
    · rw [if_pos right] at r
      obtain ⟨m,run,same,atCopy⟩:=arrive00 o s p a pc left right
      have value : digestAt s (inSlot p.val)=parentAt o.compression input p.val := by
        unfold parentAt Children.parent;rw [l,r];exact ins
      obtain ⟨z,copy,eff⟩:=copySupplied o input p s m same a atCopy value
      exact ⟨z,12,by decide,by simpa [pairCalls,left,right] using runs_trans run copy,eff⟩
    · rw [if_neg right] at r
      obtain ⟨m,run,same,atCopy⟩:=arrive01 o s p a pc left right
      have value : parentAt o.compression input p.val=combine o.compression (digestAt s (inSlot p.val)) (digestAt s (sourceRow p.val+32)) := by
        unfold parentAt Children.parent;rw [l,r,ins]
      obtain ⟨t,fill,pre⟩:=singlePrepared o input p false s m same a atCopy gap value
      obtain ⟨z,hash,eff⟩:=executeParent o input p s t a pre
      have cost : pairCalls s p=1 := if_neg (fun h=>right h.2)
      exact ⟨z,19,by decide,by rw [cost];exact runs_trans (runs_trans run fill) hash,eff⟩
  · rw [if_neg left] at l
    by_cases right : flagR s p=0
    · rw [if_pos right] at r
      obtain ⟨m,run,same,atCopy⟩:=arrive10 o s p a pc left right
      have value : parentAt o.compression input p.val=combine o.compression (digestAt s (sourceRow p.val)) (digestAt s (inSlot p.val)) := by
        unfold parentAt Children.parent;rw [l,r,ins]
      obtain ⟨t,fill,pre⟩:=singlePrepared o input p true s m same a atCopy gap value
      obtain ⟨z,hash,eff⟩:=executeParent o input p s t a pre
      have cost : pairCalls s p=1 := if_neg (fun h=>left h.1)
      exact ⟨z,20,by decide,by rw [cost];exact runs_trans (runs_trans run fill) hash,eff⟩
    · rw [if_neg right] at r
      obtain ⟨m,run,same,atHash⟩:=arrive11 o s p a pc left right
      have val : o.compression (readBuffer m (sourceRow p.val) 96)=parentAt o.compression input p.val := by
        rw [read_buffer_memory_congr _ _ same.mem]
        unfold parentAt Children.parent;rw [l,r]
        exact parentValue o s p _ _ rfl rfl gap
      obtain ⟨z,hash,eff⟩ := executeParent o input p s m a ⟨atHash,same.regs,fun x _ _=>byteMem same.mem x,val⟩
      have cost : pairCalls s p=1 := if_neg (fun h=>left h.1)
      exact ⟨z,12,by decide,by rw [cost];exact runs_trans run hash,eff⟩

theorem allPairs (o : Oracle) (input : CheckInput) (left n : Nat) (total : n+left=128)
    (s : MachineState) (inv : PairInvariant o.compression input n s) :
    ∃ t k q,k≤26*left ∧ q≤left ∧ Runs o s t k q ∧ PairInvariant o.compression input 128 t := by
  induction left generalizing n s with
  | zero =>
    have eqn : n=128 := by omega
    subst n;exact ⟨s,0,0,by decide,by decide,fun fuel=>by simp,inv⟩
  | succ l ih =>
    let p : Fin 128 := ⟨n,by omega⟩
    obtain ⟨t,k,bound,body,eff⟩:=pairBody o input p s inv
    have qbound : pairCalls s p≤1 := by unfold pairCalls;split <;> decide
    have advance := nextPair p.isLt inv eff
    obtain ⟨z,j,r,jb,rb,tail,done⟩:=ih (n+1) (by omega) (pairLatch t) advance
    exact ⟨z,(k+6)+j,(pairCalls s p+0)+r,by omega,by omega,runs_trans (runs_trans body (latchRuns o t eff.pc)) tail,done⟩

end CommitGolfCandidate.PairCap.Batch
