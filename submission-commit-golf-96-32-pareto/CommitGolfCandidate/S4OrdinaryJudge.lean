import CommitGolfCandidate.S4CheckedRow
import CommitGolfCandidate.S4CompareLoop
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
structure ContinueOrdinary (o : Oracle) (x : CheckInput) (s t : MachineState) (r n : Nat) : Prop where
  run : CheckRuns o s t n 28
  pc : t.pc=pcAt (if r+1<x.positions.card then rowStart false else endOfRows false)
  env : Env x t
  cursor : Cursor x t (r+1)

def rootOK (o : Oracle) (x : CheckInput) (r : Nat) :=
  recordAt .byte o.compression (readView x) r 24 ((readView x).peers r)=x.commitment

private theorem pendingMore {x : CheckInput} {s t : MachineState} {r : Nat} (f : PendingRow x s r) (mem : t.mem=s.mem)
    (reg : ∀ v,v∉[Reg.x6,.x7,.x14] → t.getReg v=s.getReg v) : PendingRow x t r :=
  ⟨⟨(reg _ (by decide)).trans f.mode,(reg _ (by decide)).trans f.kind,(reg _ (by decide)).trans f.width,
      (reg _ (by decide)).trans f.three,(reg _ (by decide)).trans f.root,f.data.regs mem⟩,
    (reg _ (by decide)).trans f.index,(reg _ (by decide)).trans f.value,(reg _ (by decide)).trans f.proof,(reg _ (by decide)).trans f.count⟩

attribute [local irreducible] pathPrice recordAt readBuffer
set_option maxRecDepth 5000 in
theorem ordinaryRecordStep (o : Oracle) (x : CheckInput) (s : MachineState) (r : Nat) (br : r<x.positions.card)
    (ordinary : x.positions.card≠BATCH) (pc : s.pc=pcAt (rowStart false)) (env : Env x s) (cur : Cursor x s r) :
    (¬rootOK o x r ∧ ∃ n≤3000,Finishes o s n 28 .failure) ∨
    (rootOK o x r ∧ ∃ t n,n≤3000 ∧ ContinueOrdinary o x s t r n) := by
  obtain ⟨u,run,at2634,frame,_,_,digest⟩:=checkedRow o x false r s br (decide_eq_false ordinary).symm pc env cur
  let v:=execInstrBr u (.ADDI .x14 .x0 256)
  have addr:=stepAdd .check u 2634 .x14 .x0 256 (by decide) at2634 (by rfl)
  have rf (reg : Reg) (ne : reg≠.x14) : v.getReg reg=u.getReg reg:=keepAdd u .x14 .x0 reg _ (Ne.symm ne)
  have bound : recordFuel false≤2711:=by change 111+pathPrice false 24≤111+2600;exact Nat.add_le_add_left pathEnd.2.2.1 111
  have input : readBuffer v rootBase 32=x.commitment:=((frame.data.regs (show v.mem=u.mem from rfl)).read
    rootBase 32 (by decide) (by decide)).trans (loaded_root x)
  have value : readBuffer v 256 32=recordAt .byte o.compression (readView x) r 24 ((readView x).peers r):=
    (read_buffer_memory_congr v u rfl 256 32).trans digest
  have go:=run.trans (ofRuns o addr)
  rcases compareDigest .ordinary o v 256 rootBase (addPC _ _ _ at2634) rfl ((rf _ (by decide)).trans frame.root)
      ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ with ⟨same,z,endC⟩|⟨different,n,hn,finished⟩
  · have nextFrame : PendingRow x z r:=pendingMore frame endC.mem (fun v h=>by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact (endC.regs v h.1 h.2.1).trans (rf v h.2.2))
    obtain ⟨t,n,nb,advance⟩:=advanceRow o x false z r br endC.pc nextFrame
    refine Or.inr ⟨value.symm.trans (same.trans input),t,recordFuel false+1+12+n,?_,?_⟩
    · change recordFuel false+1+12+n≤3000;omega
    · exact ⟨(go.trans endC.run).trans advance.run,advance.pc,advance.env,advance.cursor⟩
  · exact Or.inl ⟨fun eqv=>different (value.trans (eqv.trans input.symm)),recordFuel false+1+n,by change recordFuel false+1+n≤3000;omega,go.finish finished⟩
end CommitGolfCandidate.S4.Machine
