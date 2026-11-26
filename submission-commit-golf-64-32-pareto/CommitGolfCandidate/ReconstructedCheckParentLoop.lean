import CommitGolfCandidate.ReconstructedCheckParentStep

namespace CommitGolfCandidate.Reconstruction.CheckParentLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix Binding CheckParentHeap CheckParentControl
open CheckParentStep TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
attribute [local irreducible] CheckParent.Cost CheckParentCallCopy.log

def children (s : MachineState) (child : Nat→Binding.Digest) (active : Nat→Bool) (first last : Nat) :=
  ∀ q,first≤q→q<last→active q=true→
    CommitParents.cell s (base (2*q))=child (2*q) ∧ CommitParents.cell s (base (2*q+1))=child (2*q+1)

def flags (s : MachineState) (active : Nat→Bool) (first last : Nat) :=
  ∀ q,first≤q→q<last→s.getByte (CheckCapScanData.flag q)=HonestFlagState.code (active q)

def log (o : Oracle) (e start count : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) :=
  (List.range' start count).flatMap (fun p=>rows o e p active child)

def Stored (o : Oracle) (e : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) (first last : Nat)
    (s t : MachineState) :=
  ∀ q,first≤q→q<last→
    (active q=true→CommitParents.cell t (base q)=nextDigest o e q child) ∧
    (active q=false→∀ i : Fin 4,t.getMem (wordAddress (word q+i.val))=s.getMem (wordAddress (word q+i.val)))

private theorem lane {s t : MachineState} {lo hi q : Nat} (fr : Frame lo hi s t) (fresh : q<lo ∨ hi≤q) (small : q<512)
    (i : Fin 4) : t.getMem (wordAddress (word q+i.val))=s.getMem (wordAddress (word q+i.val)) := by
  have b:=i.isLt
  apply fr <;> simp only [word,stackWord,temp] <;> omega

theorem run (o : Oracle) (e : Fin 24) (size p count : Nat) (bound : size≤256) (left : size≤p) (finish : p+count=2*size)
    (active : Nat→Bool) (child : Nat→Binding.Digest) (s : MachineState) (c : Word)
    (pc : s.pc=addr (here p (2*size))) (localS : Local s e.val size p) (ctx : Context s c)
    (bits : flags s active p (2*size)) (table : CheckParentGeometry.constants s) (kids : children s child active p (2*size)) :
    ∃ n t,n≤(24+CheckParent.Cost e)*count ∧ Segment o n s t (log o e p count active child) ∧
      t.pc=addr 629 ∧ Local t e.val size (2*size) ∧ Context t c ∧ Frame p (2*size) s t ∧
      Stored o e active child p (2*size) s t ∧ (∀ r∈preserve,t.getReg r=s.getReg r) := by
  induction count generalizing p s with
  | zero=>
    have h : p=2*size:=by omega
    refine ⟨0,s,by omega,CheckRecorded.empty o s,?_,h ▸ localS,ctx,identity _ _ _,fun q lo hi=>by omega,fun _ _=>rfl⟩
    simpa only [h,here,lt_self_iff_false,ite_false] using pc
  | succ count ih=>
    have before : p<2*size:=by omega
    rw [here,ite_eq_left before] at pc
    obtain ⟨a,u,ac,step,entry,ul,uc,fr,atP,inactive,kept⟩:=CheckParentStep.run o s e size p c active child bound before pc localS
      ctx (bits p le_rfl before) table (kids p le_rfl before)
    have restFlags : flags u active (p+1) (2*size):=fun q lo hi=>(flag fr (by omega) q (by omega)).trans (bits q (by omega) hi)
    have restKids : children u child active (p+1) (2*size) := by
      intro q lo hi on
      have original:=kids q (by omega) hi on
      exact ⟨(cell fr _ (by omega) (.inr (by omega))).trans original.1,(cell fr _ (by omega) (.inr (by omega))).trans original.2⟩
    obtain ⟨b,t,bc,more,done,finalL,finalC,rest,stored,carry⟩:=ih (p+1) (by omega) (by omega) u entry ul uc
      restFlags (CheckParentHeap.constants fr table) restKids
    have logs : log o e p (count+1) active child=rows o e p active child++log o e (p+1) count active child:=by
      simp only [log,List.range'_succ,List.flatMap_cons]
    refine ⟨a+b,t,?_,logs ▸ compose step more,done,finalL,finalC,CheckParentHeap.trans fr rest (by omega) (by omega),
      ?_,fun r h=>(carry r h).trans (kept r h)⟩
    · rw [Nat.mul_succ];omega
    · intro q lo hi
      by_cases equal : q=p
      · subst q
        refine ⟨fun on=>(cell rest _ (by omega) (.inl (by omega))).trans (atP on),?_⟩
        intro off i
        exact (lane rest (.inl (by omega)) (by omega) i).trans (congrFun (inactive off) _)
      · have past:=stored q (by omega) hi
        exact ⟨past.1,fun off i=>(past.2 off i).trans (lane fr (.inr (by omega)) (by omega) i)⟩

theorem length (o : Oracle) (e p count : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) :
    (log o e p count active child).length≤count*work e := by
  induction count generalizing p with
  | zero=>simp [log]
  | succ n ih=>
    have head : (rows o e p active child).length≤work e := by
      unfold rows;split
      · simp [CheckParentCallCopy.log,CheckParentExecution.rows]
      · simp
    have step:=ih (p+1)
    rw [Nat.succ_mul]
    change ((List.range' p (n+1)).flatMap _).length≤_
    rw [List.range'_succ,List.flatMap_cons,List.length_append]
    change (rows o e p active child).length+(log o e (p+1) n active child).length≤_
    omega

theorem observed (o : Oracle) (e p n q : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) (lo : p≤q) (hi : q<p+n)
    (on : active q=true) :
    CheckParentCallCopy.log o e (child (2*q)) (child (2*q+1)) ⊆ log o e p n active child := by
  intro row yes;apply List.mem_flatMap.mpr
  refine ⟨q,?_,?_⟩
  · exact List.mem_range'.mpr ⟨q-p,by omega,by omega⟩
  · simpa only [rows,on,ite_true] using yes

end CommitGolfCandidate.Reconstruction.CheckParentLoop

