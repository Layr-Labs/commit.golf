import CommitGolfCandidate.RungACache
namespace CommitGolfCandidate.RungA.Upper
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
theorem layer (o : Oracle) (s : MachineState) (d : Width) (env : Env s) (pc : s.pc=pcAt (stagePC d))
    (mask : d.val≠0 → s.getReg .x28=16383) (base : Nat→Digest)
    (low : 4≤d.val) (lev : Levels o.compression base d s) (gaps : Gaps s) :
    ∃ t,MRun o s (layerSteps d) t (layerCycles d) (nodes d) ∧ t.pc=pcAt (endPC d) ∧
      Pointers d (nodes d) t ∧ Levels o.compression base (d.val+1) t ∧ Gaps t ∧ Outside s t := by
  obtain ⟨u,entry,mem,ip,f,lim⟩:=enter o d s pc env mask
  obtain ⟨v,bulk,done,atTail⟩:=bulkRun o s u d (blocks d) le_rfl ip ⟨f,lim,mem⟩
  simp only [lt_self_iff_false,ite_false] at done
  have even : bulkCount d%2=0:=by dsimp [bulkCount];rw [Nat.mul_mod,((show ∀ x : Width, groupSize x%2=0 by decide) d),Nat.mul_zero,Nat.zero_mod]
  have left:=bankCount d
  obtain ⟨t,tail,edge,finish⟩:=bankRun o s v d true (bulkCount d) (tailSize d) even
    (by simp [bankSize,tailSize]) left.le done atTail
  rw [left] at finish
  have endAt : ∀ d : Width,lane d true (tailSize d)=endPC d:=by decide +kernel
  have same (a n : Nat) := readBuffer_of_mem_eq finish.memory a n
  refine ⟨t,?_,edge.trans (congrArg pcAt (endAt d)),finish.toPointers,?_,?_,?_⟩
  · have run:=(entry.trans bulk).trans tail
    simpa only [layerSteps,layerCycles,Nat.zero_add,show blocks d*groupSize d+tailSize d=nodes d from left] using run
  · intro h bottom bh i hi
    exact (same _ _).trans (retain_fill o.compression base s d d.isLt low lev gaps h bottom bh i hi)
  · intro h p k g
    exact (same _ _).trans (Late.level_keeps_gaps _ s d _ d.isLt le_rfl gaps h p k g)
  · intro a n fa rng;exact (same _ _).trans (outside_fill o s d low a n fa rng)

def bill (f : Width→Nat) : Nat→Nat | 0=>0 | k+1=>bill f k+f (idx (4+k))

theorem suffixChain (o : Oracle) (base : Nat→Digest) (s : MachineState) (env : Env s)
    (pc : s.pc=pcAt (R4.nextPC 4)) (mask : s.getReg .x28=16383)
    (leaf : Levels o.compression base 4 s) (gap : Gaps s) (k : Nat) (limit : k≤20) :
    ∃ t,MRun o s (bill layerSteps k) t (bill layerCycles k) (bill nodes k) ∧ t.pc=pcAt (R4.nextPC (4+k)) ∧
    Env t ∧ t.getReg .x28=16383 ∧ finishedPtr (4+k) t ∧ Levels o.compression base (4+k) t ∧ Gaps t ∧ Outside s t := by
  induction k with
  | zero=>exact ⟨s,DetRun.refl o (R4.submission.image .commit) s,pc,env,mask,fun h=>by omega,leaf,gap,fun _ _ _ _=>rfl⟩
  | succ k ih=>
    have lt : 4+k<24:=by omega
    have eqn : (idx (4+k)).val=4+k:=Nat.mod_eq_of_lt lt
    obtain ⟨u,run,ip,eu,mu,_,known,g,old⟩:=ih (by omega)
    rw [R4.nextPC,if_pos lt] at ip
    obtain ⟨t,pass,ed,f,new,g',fr⟩:=layer o u (idx (4+k)) eu ip (fun _=>mu) base (by omega) (eqn.symm ▸ known) g
    have dest : ∀ d : Width,endPC d=R4.nextPC (d.val+1):=by decide +kernel
    have ptr : finishedPtr (4+k+1) t:=by
      intro fin
      have last : idx (4+k)=23:=Fin.ext (by change (idx (4+k)).val=23;omega)
      have pos:=f.dst
      rw [last] at pos;exact pos
    rw [eqn] at new
    have dn:=dest (idx (4+k));rw [eqn] at dn
    exact ⟨t,run.trans pass,ed.trans (congrArg pcAt dn),f.toEnv,f.mask,ptr,new,g',
      fun a n fs rg=>(fr a n fs rg).trans (old a n fs rg)⟩
end CommitGolfCandidate.RungA.Upper
