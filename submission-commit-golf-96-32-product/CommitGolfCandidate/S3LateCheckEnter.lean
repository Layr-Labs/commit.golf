import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.S3LateCheckLeafEnd
import CommitGolfCandidate.LateCheckInputs

namespace CommitGolfCandidate.Late.Check3.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W)
set_option maxRecDepth 4000
attribute [local irreducible] Runs Normal.Runs readBuffer

inductive Row where | normal | batch deriving DecidableEq
def Row.start : Row → Nat | .normal=>207 | .batch=>207
def Row.link : Row → Nat | .normal=>218 | .batch=>218
def Row.jump : Row → BitVec 21 | .normal=>BitVec.ofInt 21 (-252) | .batch=>BitVec.ofInt 21 (-252)
def Row.after (q : Row) (s : MachineState) :=
  ((s.setReg .x20 (s.getMem (s.getReg .x24))).setReg .x1 (pcAt q.link)).setPC (pcAt 384)

private theorem linkAddresses (q : Row) :
    pcAt (q.start+10)+4=pcAt q.link ∧ pcAt (q.start+10)+signExtend21 q.jump=pcAt 154 :=
  by cases q <;> exact ⟨rfl,rfl⟩

theorem enter (q : Row) (s : MachineState) (pc : s.pc=pcAt q.start) (safe : accessValid (s.getReg .x24) 8=true) :
    Runs s (q.after s) 4 4 := by
  let a:=s.setReg .x20 (s.getMem (s.getReg .x24))
  let t:=a.setPC (pcAt (q.start+1))
  let u:=a.setPC (pcAt (q.start+10))
  let v:=(a.setReg .x1 (pcAt q.link)).setPC (pcAt 154)
  have bound : q.start+10<433 := by cases q <;> decide
  have h : Runs s t 1 1 := by
    apply one q.start (by omega) (.LD .x20 .x24 0) (by cases q <;> rfl) _ _ pc
    have ok : memoryArgumentsValid s (.LD .x20 .x24 0)=true := by change accessValid (s.getReg .x24+0) 8=true;simpa using safe
    have zero : s.getReg .x24+signExtend12 0=s.getReg .x24 := BitVec.add_zero _
    simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,zero,pc]
    change some (a.setPC (pcAt q.start+4))=some (a.setPC (pcAt (q.start+1)))
    rw [pc_succ]
  have j : Runs t u 1 1 := by
    apply one (q.start+1) (by omega) (.JAL .x0 36) (by cases q <;> rfl) _ _ rfl
    change some (t.setPC (pcAt (q.start+1)+signExtend21 36))=some u
    cases q <;> rfl
  have k : Runs u v 1 1 := by
    apply one (q.start+10) (by omega) (.JAL .x1 q.jump) (by cases q <;> rfl) _ _ rfl
    change some ((u.setReg .x1 (pcAt (q.start+10)+4)).setPC (pcAt (q.start+10)+signExtend21 q.jump))=_
    obtain ⟨link,target⟩:=linkAddresses q
    rw [link,target];rfl
  have l : Runs v (q.after s) 1 1 := one 154 (by decide) (.JAL .x0 920) (by rfl) _ _ rfl rfl
  exact ((h.trans j).trans k).trans l

theorem Row.keep (q : Row) (s : MachineState) (r : Reg) (idx : Reg.x20≠r) (ret : Reg.x1≠r) :
    (q.after s).getReg r=s.getReg r := by
  simp only [Row.after,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ idx,MachineState.getReg_setReg_ne _ _ _ _ ret]

structure RowLeaf (o : Oracle) (q : Row) (s t : MachineState) (i : Index) (salt : Salt) (v : CommitGolf.Entry) (a p n : Nat) : Prop where
  budget : n≤54
  run : Normal.Runs o s t n 4
  pc : t.pc=pcAt q.link
  idx : t.getReg .x20=W i.val
  value : t.getReg .x8=W (a+256)
  proof : t.getReg .x25=W (p+24)
  keep : ∀ reg∈[Reg.x19,.x21,.x24,.x26,.x27,.x30], t.getReg reg=s.getReg reg
  high : High s t
  digest : readBuffer t 256 32=leaf o.compression (i.val.testBit 0) salt v

theorem rowLeaf (o : Oracle) (q : Row) (s : MachineState) (a p : Nat) (i : Index) (salt : Salt) (v : CommitGolf.Entry)
    (pc : s.pc=pcAt q.start) (safe : accessValid (s.getReg .x24) 8=true)
    (ix : s.getMem (s.getReg .x24)=W i.val) (value : s.getReg .x8=W a) (proof : s.getReg .x25=W p)
    (scratch : s.getReg .x21=256) (ar : Open.AddrOK a 256) (pr : Open.AddrOK p 24) (ah : 448≤a) (ph : 448≤p)
    (vread : readBuffer s a 256=v) (sread : readBuffer s p 24=salt) :
    ∃ t n, RowLeaf o q s t i salt v a p n := by
  let beginState:=q.after s
  have eq : beginState.getReg .x20=W i.val := ix
  have rr:=leafRun o beginState i salt v a p q.link rfl ((q.keep s _ (by decide) (by decide)).trans value) eq
    ((q.keep s _ (by decide) (by decide)).trans proof) ((q.keep s _ (by decide) (by decide)).trans scratch) rfl
    (by cases q <;> simp [Row.link]) ar pr ah ph
    ((read_congr_mem beginState s a 256 rfl).trans vread) ((read_congr_mem beginState s p 24 rfl).trans sread)
  obtain ⟨t,n,result⟩:=rr
  refine ⟨t,4+n,by have :=result.budget;omega,(Normal.deterministic o (enter q s pc safe)).trans result.runs,
    result.pc,(result.keep _ (by decide)).trans eq,result.valPtr,result.proofPtr,?_,?_,result.digest⟩
  · intro reg hr
    have valid : reg∈stable := (by intro r;cases r <;> decide : ∀ r : Reg,r∈[Reg.x19,.x21,.x24,.x26,.x27,.x30] → r∈stable) reg hr
    have un : reg≠.x20 ∧ reg≠.x1 := (by intro r;cases r <;> decide : ∀ r : Reg,r∈[Reg.x19,.x21,.x24,.x26,.x27,.x30] → r≠.x20 ∧ r≠.x1) reg hr
    exact (result.keep reg valid).trans (q.keep s reg un.1.symm un.2.symm)
  · exact (High.memory (show beginState.mem=s.mem from rfl)).trans result.high

end CommitGolfCandidate.Late.Check3.Micro
