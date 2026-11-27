import CommitGolfCandidate.S4LeafLayout
import CommitGolfCandidate.S4RowValues

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
def copyPair (s : MachineState) (src dst n : Nat) :=
  transferN (execInstrBr (execInstrBr s (ptrCode .x14 src)) (ptrCode .x15 dst)) n
structure FixedMoved (s t : MachineState) (pc src dst n : Nat) : Prop where
  run : Runs .check s t (2+2*n) (2+2*n)
  pc : t.pc=pcAt (pc+(2+2*n))
  keep : ∀ r,r≠.x6 → r≠.x14 → r≠.x15 → t.getReg r=s.getReg r
  moved : Moved s t src dst (8*n)

private theorem smallImm : ∀ n : Fin 609,signExtend12 (BitVec.ofNat 12 n.val)=W n.val:=by
  set_option maxRecDepth 10000 in decide
theorem fixedMove (s : MachineState) (site src dst n : Nat) (pc : s.pc=pcAt site) (room : site+(2+2*n)≤Code.check.count)
    (code : Matches .check site (fixedCopy src dst n)) (sb : src+8*n≤608) (db : dst+8*n≤608)
    (small : 8*n≤256) (sa : src%8=0) (da : dst%8=0) (separate : src+8*n≤dst ∨ dst+8*n≤src) :
    FixedMoved s (copyPair s src dst n) site src dst n := by
  let u:=execInstrBr s (ptrCode .x14 src);let v:=execInstrBr u (ptrCode .x15 dst)
  have head : Matches .check site [ptrCode .x14 src,ptrCode .x15 dst]:=code.left
  have a:=stepAdd .check s site .x14 .x0 _ (by omega) pc head.head
  have b:=stepAdd .check u (site+1) .x15 .x0 _ (by omega) (addPC .x14 .x0 _ pc) head.tail.head
  have r1 : v.getReg .x14=W src:=by
    apply (keepAdd u .x15 .x0 .x14 _ (by decide)).trans
    apply (getAfterAdd s .x14 .x0 _ (by decide)).trans
    exact (BitVec.zero_add _).trans (smallImm ⟨src,by omega⟩)
  have r2 : v.getReg .x15=W dst:=by
    apply (getAfterAdd u .x15 .x0 _ (by decide)).trans
    exact (BitVec.zero_add _).trans (smallImm ⟨dst,by omega⟩)
  have cp:=copyN v (site+2) src dst n (addPC .x15 .x0 _ (addPC .x14 .x0 _ pc)) (by omega) code.right r1 r2 sa da small
    (by unfold MEMORY_BYTES;omega) (by unfold MEMORY_BYTES;omega) separate
  refine ⟨(a.trans b).trans cp.run,cp.endPC.trans (congrArg pcAt (by omega)),?_,cp.bytes.congr rfl rfl⟩
  intro r f g h;exact (cp.regs r (Ne.symm f)).trans ((keepAdd u .x15 .x0 r _ (Ne.symm h)).trans (keepAdd s .x14 .x0 r _ (Ne.symm g)))

def putGap (s : MachineState) (off : Nat) := execInstrBr (execInstrBr s (ptrCode .x14 512)) (.SD .x14 .x0 (BitVec.ofNat 12 off))
theorem gapRun (s : MachineState) (site off : Nat) (oneOf : off=24 ∨ off=64) (pc : s.pc=pcAt site)
    (room : site+2≤Code.check.count)
    (code : Matches .check site [ptrCode .x14 512,.SD .x14 .x0 (BitVec.ofNat 12 off)]) :
    let t:=putGap s off
    Runs .check s t 2 2 ∧ t.pc=pcAt (site+2) ∧ (∀ r,r≠.x14 → t.getReg r=s.getReg r) ∧
    Wrote s t (512+off) 8 (fun _=>0) ∧ readBuffer t (512+off) 8=0 := by
  let u:=execInstrBr s (ptrCode .x14 512)
  have a:=stepAdd .check s site .x14 .x0 512 (by omega) pc code.head
  have ptr : u.getReg .x14+signExtend12 (BitVec.ofNat 12 off)=W (512+off):=by
    rw [show u.getReg .x14=W 512 from (getAfterAdd s .x14 .x0 512 (by decide)).trans rfl,
      show signExtend12 (BitVec.ofNat 12 off)=W off from smallImm ⟨off,by omega⟩]
    exact (BitVec.ofNat_add ..).symm
  have b:=zeroRun (by omega) (addPC .x14 .x0 512 pc) code.tail.head ptr
    (show Safe (512+off) 8 from by rcases oneOf with rfl|rfl <;> exact ⟨by decide,by decide⟩)
  obtain ⟨run,endPC,regs,w⟩:=b
  have write : Wrote s (putGap s off) (512+off) 8 (fun _=>0):=by intro q b;exact w q b
  refine ⟨a.trans run,endPC,fun r ne=>(regs r).trans (keepAdd s .x14 .x0 r _ (Ne.symm ne)),write,?_⟩
  have val (j : Nat) (bj : j<8) : (putGap s off).getByte (W (512+off+j))=(0 : Word).extractLsb' (8*(0+j)) 8:=by
    have h:=write (512+off+j) (by omega)
    rw [if_pos (by omega)] at h
    exact h.trans BitVec.extractLsb'_zero.symm
  exact (read_serialized_slice _ _ _ 0 8 val).trans BitVec.extractLsb'_eq_self
end CommitGolfCandidate.S4.Machine
