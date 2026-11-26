import CommitGolfCandidate.ReconstructedCheckTailPadding
import CommitGolfCandidate.ReconstructedCheckTailReturn

namespace CommitGolfCandidate.Reconstruction.CheckTail
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckTailOps CheckTailPadding CheckTailReturn
set_option maxRecDepth 15000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def Accepts (s : MachineState) (c len stream : Nat) :=
  alignedBytes c=len ∧ (∀ j : Fin 4,CheckRoot.EqualAt s j) ∧ Padded c stream
instance (s : MachineState) (c len stream : Nat) : Decidable (Accepts s c len stream) := by unfold Accepts;infer_instance

structure Entry (s : MachineState) (c len stream : Nat) : Prop where
  pc : s.pc=addr 632
  stack : s.getReg .x2=W CheckLayout.sp
  fp : s.getReg .x8=W CheckLayout.fp
  cursor : s.getReg .x24=W c
  ret : s.getMem (W (CheckLayout.fp-8))=addr 20
  saved : s.getMem (W (CheckLayout.fp-2424))=W len
  proof : CheckLayout.StreamMemory s stream

private theorem rootAcross {s t} (f : Frame s t) : (∀ j : Fin 4,CheckRoot.EqualAt s j) ↔ (∀ j : Fin 4,CheckRoot.EqualAt t j) := by
  unfold CheckRoot.EqualAt
  simp only [f.mem]

private theorem reject {o : Oracle} {s t : MachineState} {n : Nat} (seg : Segment o n s t [])
    (at57 : t.pc=addr 57) (sp : t.getReg .x2=W CheckLayout.sp)
    (ret : t.getMem (W (CheckLayout.fp-8))=addr 20) (neg : t.getReg .x10=(-1)) : Finished o s (n+20) (-1) := by
  have f := finish57 o t at57 sp ret;rw [neg] at f;exact extend seg f

theorem run (o : Oracle) (s : MachineState) (c len stream : Nat) (bound : c≤70000000000)
    (size : len<2^64) (entry : Entry s c len stream) :
    ∃ n,n≤80 ∧ Finished o s n (if Accepts s c len stream then W len else -1) := by
  obtain ⟨u,pre,loc,neg,first⟩ := prefixRun o s c len bound size entry.pc entry.cursor entry.fp entry.saved
  have stack := (first.regs .x2 (by decide)).trans entry.stack
  have ret := (first.mem _).trans entry.ret
  by_cases sizeOK : alignedBytes c=len
  · rw [ite_eq_left sizeOK] at loc
    obtain ⟨v,n,lim,root,atRoot,mem,regs⟩ := CheckRoot.positive o u loc
    have sv := (regs .x2 (by decide)).trans stack
    have rv := (mem _).trans ret
    have nv := (regs .x10 (by decide)).trans neg
    by_cases equal : ∀ j : Fin 4,CheckRoot.EqualAt s j
    · rw [ite_eq_left ((rootAcross first).mp equal)] at atRoot
      have cv := (regs .x24 (by decide)).trans ((first.regs .x24 (by decide)).trans entry.cursor)
      have svBits : CheckLayout.StreamMemory v stream := fun i hi => (mem _).trans ((first.mem _).trans (entry.proof i hi))
      obtain ⟨t,m,mLim,pad,atPad,rv10,last⟩ := CheckTailPadding.run o v c stream bound atRoot cv svBits
      have all_ : Segment o (8+n+m) s t [] := compose (compose pre root) pad
      have ts := (last.regs .x2 (by decide)).trans sv
      have tr := (last.mem _).trans rv
      by_cases ok : Padded c stream
      · have accept : Accepts s c len stream := ⟨sizeOK,equal,ok⟩
        rw [ite_eq_left ok] at atPad
        rw [ite_eq_left accept]
        have tf := (last.regs .x8 (by decide)).trans ((regs .x8 (by decide)).trans ((first.regs .x8 (by decide)).trans entry.fp))
        have sl := (last.mem _).trans ((mem _).trans ((first.mem _).trans entry.saved))
        exact ⟨8+n+m+24,by omega,extend all_ (accept668 o t len atPad ts tf tr sl)⟩
      · rw [ite_eq_right ok] at atPad
        rw [ite_eq_right (fun h : Accepts s c len stream => ok h.2.2)]
        exact ⟨8+n+m+20,by omega,reject all_ atPad ts tr (rv10.trans nv)⟩
    · rw [ite_eq_right (fun h=>equal ((rootAcross first).mpr h))] at atRoot
      rw [ite_eq_right (fun h : Accepts s c len stream => equal h.2.1)]
      exact ⟨8+n+20,by omega,reject (compose pre root) atRoot sv rv nv⟩
  · rw [ite_eq_right sizeOK] at loc
    rw [ite_eq_right (fun h : Accepts s c len stream => sizeOK h.1)]
    exact ⟨8+20,by decide,reject pre loc stack ret neg⟩

theorem negative : CheckHalt.exit (-1)=.failure := rfl

theorem nonnegative (len : Nat) (bounded : len<2^63) : CheckHalt.exit (W len)=.success := by
  unfold CheckHalt.exit
  have small : 2*(W len).toNat<2^64 := by change 2*(len%2^64)<2^64;omega
  have signed : (W len).slt (0 : Word)=false := by
    rw [BitVec.slt_eq_decide];apply decide_eq_false
    rw [BitVec.toInt_eq_toNat_of_lt small,show (0 : Word).toInt=0 by decide];omega
  rw [signed];rfl

end CommitGolfCandidate.Reconstruction.CheckTail
