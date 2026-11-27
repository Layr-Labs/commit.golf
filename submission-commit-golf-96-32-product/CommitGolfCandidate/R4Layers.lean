import CommitGolfCandidate.R4Bank
import CommitGolfCandidate.LateCachedTree

set_option Elab.async false
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt rowAddress nodeAddress layerHash fillLevel levelCount LevelsThrough Gaps)

def layerSteps (d : Width) := (header d).length+blocks d*blockSteps d+tailSize d*laneWidth d
def layerCycles (d : Width) := (header d).length+blocks d*blockCycles d+tailSize d*(laneWidth d+7)
def SaltMemory (s : MachineState) (salts : Late.SaltTape) := ∀ i : Index,readBuffer s (Late.sharedSaltAddr i) 24=salts i

theorem layer (o : Oracle) (s : MachineState) (d : Width) (env : Env s) (pc : s.pc=pcAt (stagePC d))
    (mask : d.val≠0 → s.getReg .x28=16383) (base : Nat→Digest) (salts : Late.SaltTape)
    (lev : LevelsThrough o.compression base d s) (gaps : Gaps s) (salt : SaltMemory s salts) :
    ∃ t,MRun o s (layerSteps d) t (layerCycles d) (nodes d) ∧ t.pc=pcAt (endPC d) ∧
      Pointers d (nodes d) t ∧ LevelsThrough o.compression base (d.val+1) t ∧ Gaps t ∧ SaltMemory t salts := by
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
  · intro h bh i hi
    exact (same _ _).trans (Late.fill_correct o.compression base s d d.isLt lev gaps h bh i hi)
  · intro h p k g
    exact (same _ _).trans (Late.level_keeps_gaps _ s d _ d.isLt le_rfl gaps h p k g)
  · intro i
    apply (same _ _).trans;apply Eq.trans _ (salt i)
    apply Late.fill_preserves _ _ _ _ _ _ le_rfl
    · have:=i.isLt;change i.val<16777216 at this;unfold Late.sharedSaltAddr Late.rowBase;omega
    · intro j hj
      exact Or.inr ((Late.parent_below_salts _ _ hj).trans (by unfold Late.sharedSaltAddr;omega))

def idx (n : Nat) : Width:=⟨n%24,Nat.mod_lt _ (by decide)⟩
def total (f : Width→Nat) : Nat→Nat | 0=>0 | n+1=>total f n+f (idx n)
def nextPC (n : Nat) := if n<24 then stagePC (idx n) else 262112
def finishedPtr (n : Nat) (s : MachineState) := n=24 → s.getReg .x12=Z (Late.nodeAddress 24 1)

theorem layerChain (o : Oracle) (base : Nat→Digest) (salts : Late.SaltTape) (s : MachineState) (env : Env s)
    (pc : s.pc=pcAt 180278) (leaf : LevelsThrough o.compression base 0 s) (gap : Gaps s) (salt : SaltMemory s salts)
    (n : Nat) (bound : n≤24) :
    ∃ t,MRun o s (total layerSteps n) t (total layerCycles n) (total nodes n) ∧ t.pc=pcAt (nextPC n) ∧
    Env t ∧ (n≠0 → t.getReg .x28=16383) ∧ finishedPtr n t ∧ LevelsThrough o.compression base n t ∧ Gaps t ∧ SaltMemory t salts := by
  induction n with
  | zero=>exact ⟨s,DetRun.refl o (submission.image .commit) s,pc,env,fun h=>(h rfl).elim,fun h=>by contradiction,leaf,gap,salt⟩
  | succ n ih=>
    have lt : n<24:=by omega
    have eqn : (idx n).val=n:=Nat.mod_eq_of_lt lt
    obtain ⟨u,run,ip,envU,mask,_,known,g,sa⟩:=ih lt.le
    rw [nextPC,if_pos lt] at ip
    obtain ⟨t,pass,edge,f,new,g',sa'⟩:=layer o u (idx n) envU ip (fun h=>mask (by rwa [eqn] at h)) base salts
      (eqn.symm ▸ known) g sa
    have dest : ∀ d : Width,endPC d=nextPC (d.val+1):=by decide +kernel
    have ptr : finishedPtr (n+1) t:=by
      intro fin
      have last : idx n=23:=Fin.ext (by change (idx n).val=23;omega)
      have pos:=f.dst
      rw [last] at pos;exact pos
    exact ⟨t,run.trans pass,edge.trans (congrArg pcAt (by rw [dest,eqn])),f.toEnv,fun _=>f.mask,ptr,eqn ▸ new,g',sa'⟩
end CommitGolfCandidate.R4
