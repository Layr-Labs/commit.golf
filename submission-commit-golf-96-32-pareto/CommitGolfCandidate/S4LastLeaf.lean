import CommitGolfCandidate.S4SaltAssembly
import CommitGolfCandidate.S4Header
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Salt Digest)
private def regbit (b : Bool) : Word:=if b then 1 else 0

private theorem indexParity (i : Index) : W i.val &&& 1=regbit (i.val.testBit 0) := by
  rw [parity,Nat.testBit_eq_decide_div_mod_eq];simp only [Nat.pow_zero,Nat.div_one]
  rcases (show i.val%2=0 ∨ i.val%2=1 by omega) with e|e <;> rw [e] <;> rfl

theorem assembleSalt (o : Oracle) (s : MachineState) (b : Bool) (i : Index) (salt : Salt) (a d : Digest)
    (pc : s.pc=pcAt (rowStart b+77)) (index : s.getReg .x20=W i.val) (left : readBuffer s 352 32=a)
    (right : readBuffer s 384 32=d) (salted : readBuffer s 416 24=salt) :
    ∃ t,LeafEffect o s t 31 0 ∧ t.pc=pcAt (rowStart b+137) ∧ readBuffer t 512 96=Late.finalBlock (i.val.testBit 0) salt a d := by
  let n:=rowStart b
  let u:=execInstrBr s (.ANDI .x6 .x20 1)
  have size : n+140≤Code.check.count:=by cases b <;> decide
  have code:=leafSites b
  have mask : Runs .check s u 1 1:=one (by omega) pc _ code.parity.head rfl
  have res : u.getReg .x6=regbit (i.val.testBit 0):=by
    change s.getReg .x20 &&& 1=_
    rw [index];exact indexParity i
  have at78 : u.pc=pcAt (n+78):=(congrArg (·+4) pc).trans (Late.pc_succ ..).symm
  have control:=alternate .check (n+78) (n+80) (n+109) .x6 .x0 true code.even code.odd rfl u at78
  let odd:=i.val.testBit 0
  have test : ((u.getReg .x6==u.getReg .x0)==true)=(!odd):=by rw [res];change ((regbit odd==(0 : Word))==true)=_;cases odd <;> rfl
  rw [test] at control
  let v:=u.setPC (pcAt (oddStart b odd))
  have go : CheckRuns o s v (if odd then 3 else 2) 0:=by
    cases e : odd
    · rw [e] at control;unfold v oddStart;rw [e];exact (ofRuns o mask).trans (ofRuns o control)
    · rw [e] at control;unfold v oddStart;rw [e];exact (ofRuns o mask).trans (ofRuns o control)
  have mem : v.mem=s.mem:=rfl
  obtain ⟨t,arm,finished,data⟩:=saltArm o v b odd salt a d rfl
    ((read_buffer_memory_congr _ _ mem _ _).trans left) ((read_buffer_memory_congr _ _ mem _ _).trans right)
    ((read_buffer_memory_congr _ _ mem _ _).trans salted)
  have start : LeafEffect o s v (if odd then 3 else 2) 0:=by
    refine ⟨go,unchangedBytes mem _ _,?_⟩
    intro r hr
    have ne : Reg.x6≠r:=by rintro rfl;exact hr (by decide)
    exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne))
  have m:=start.next arm
  have price : (if odd then 3 else 2)+(if odd then 28 else 29)=31:=by cases odd <;> decide
  rw [price] at m;exact ⟨t,m,finished,data⟩

theorem hashLeaf (o : Oracle) (s : MachineState) (b : Bool) (i : Index) (e : Entry) (salt : Salt) (a : Nat)
    (pc : s.pc=pcAt (rowStart b+51)) (idx : s.getReg .x20=W i.val) (ptr : s.getReg .x9=W a)
    (al : a%8=0) (low : 32768≤a) (hi : a+256≤MEMORY_BYTES) (value : readBuffer s a 256=e)
    (sread : readBuffer s 416 24=salt) (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96) :
    ∃ t,LeafEffect o s t 60 4 ∧ t.pc=pcAt (rowStart b+140) ∧
      readBuffer t 256 32=Late.leaf o.compression (i.val.testBit 0) salt e := by
  obtain ⟨u,mid⟩:=prehashRun o s b a e salt pc ptr al low hi value sread mode kind len
  obtain ⟨v,arm,at137,data⟩:=assembleSalt o u b i salt _ _ mid.pc ((mid.effect.keep _ (by decide)).trans idx) mid.first mid.second mid.salt
  have before:=mid.effect.next arm
  have bound : rowStart b+140≤Code.check.count:=by cases b <;> decide
  have last:=compressRun o v (rowStart b+137) .x0 512 512 256 false (by intro e;cases e) bound at137 (leafSites b).final
    ((before.keep _ (by decide)).trans mode) ((before.keep _ (by decide)).trans kind) ((before.keep _ (by decide)).trans len)
    rfl rfl ⟨by decide,by decide⟩ ⟨by decide,by decide⟩
  exact ⟨_,before.next (hashEffect last (by decide) (by decide)),last.pc,last.value.trans (congrArg o.compression data)⟩
end CommitGolfCandidate.S4.Machine
