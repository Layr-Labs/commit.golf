import CommitGolfCandidate.S4PairLoad

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
def chosenAddress (j : Nat) (right : Bool) (v : Option Digest) := childPtr (capAddr (2*j)+selectOffset right) v
structure PickResult (s t : MachineState) (side : Bool) (j : Nat) (v : Option Digest) : Prop where
  run : Runs .check s t 11 11
  pc : t.pc=pcAt (selectPart side+12)
  keep : ∀ r,r≠.x6 → r≠.x15 → t.getReg r=s.getReg r
  copy : Moved s t (chosenAddress j side v) (512+selectOffset side) 32

set_option maxRecDepth 5000 in
set_option maxHeartbeats 800000 in
theorem pickChild (s : MachineState) (right : Bool) (j : Nat) (val : Option Digest) (bj : j<171)
    (pc : s.pc=pcAt (selectPart right)) (dst : s.getReg .x14=W 512) (cap : s.getReg .x29=W (capAddr (2*j)))
    (hit : s.getReg (selectReg right)=flagBit val.isSome) : ∃ t,PickResult s t right j val := by
  let n:=selectPart right;let off:=selectOffset right;let a:=chosenAddress j right val
  have limit : n+12≤Code.check.count:=by cases right <;> decide
  let u:=execInstrBr s (choosePtr right)
  have enc : decodeInstruction (Code.check.word n)=some (.base (choosePtr right)):=by
    cases right with | false=>exact pairSites.left.head | true=>exact pairSites.right.head
  have first:=stepAdd .check s n .x15 .x29 (BitVec.ofNat 12 off) (by omega) pc enc
  have old (r : Reg) (ne : r≠.x15) : u.getReg r=s.getReg r:=keepAdd s .x15 .x29 r _ (Ne.symm ne)
  have ptr : u.getReg .x15=W (capAddr (2*j)+off):=by
    apply (getAfterAdd s .x15 .x29 _ (by decide)).trans;rw [cap,show signExtend12 (BitVec.ofNat 12 off)=W off by cases right <;> decide]
    exact (BitVec.ofNat_add ..).symm
  obtain ⟨cmp,far,fill,copy⟩:=pairSites.choices right
  have branch:=alternate .check (n+1) (n+3) (n+4) (selectReg right) .x0 true cmp far rfl u (addPC _ _ _ pc)
  have isMissing : ((u.getReg (selectReg right)==u.getReg .x0)==true)=val.isNone:=by
    rw [old _ (by cases right <;> decide),hit];cases val <;> rfl
  rw [isMissing] at branch
  have ready : ∃ v,Runs .check s v 3 3 ∧ v.pc=pcAt (n+4) ∧ v.getReg .x15=W a ∧ v.mem=s.mem ∧
      ∀ r,r≠.x15 → v.getReg r=s.getReg r:=by
    cases eqv : val with
    | none=>
      rw [eqv] at branch
      let w:=u.setPC (pcAt (n+3))
      let v:=execInstrBr w (ptrCode .x15 352)
      have load:=stepAdd .check w (n+3) .x15 .x0 352 (by omega) rfl (stood fill)
      refine ⟨v,(first.trans branch).trans load,addPC _ _ _ (show w.pc=pcAt (n+3) from rfl),?_,rfl,?_⟩
      · unfold a chosenAddress childPtr;rw [eqv];rfl
      · intro r neq;exact (keepAdd w .x15 .x0 r 352 (Ne.symm neq)).trans (MachineState.getReg_setPC.trans (old r neq))
    | some d=>
      rw [eqv] at branch
      let v:=u.setPC (pcAt (n+4))
      refine ⟨v,first.trans branch,rfl,?_,rfl,fun r neq=>MachineState.getReg_setPC.trans (old r neq)⟩
      unfold a chosenAddress childPtr;rw [eqv];exact ptr
  obtain ⟨v,load,atCopy,src,mem,regs⟩:=ready
  have range : a%8=0 ∧ a+32≤MEMORY_BYTES ∧ (a+32≤512+off ∨ 512+off+32≤a):=by
    have all : ∀ k : Fin 171,∀ side yes : Bool,
        let off:=selectOffset side
        let p:=if yes then capAddr (2*k.val)+off else 352
        p%8=0 ∧ p+32≤MEMORY_BYTES ∧ (p+32≤512+off ∨ 512+off+32≤p) := by decide
    exact all ⟨j,bj⟩ right val.isSome
  have c:=dwordBlock .check v .x15 .x14 (n+4) a 512 0 off 4 (by decide) (by decide) atCopy (by omega) (matchesListed copy)
    src ((regs _ (by decide)).trans dst) range.1 (by cases right <;> decide) (by decide) (by cases right <;> decide)
    range.2.1 (by cases right <;> decide) range.2.2
  exact ⟨_,⟨load.trans c.run,c.endPC.trans (congrArg pcAt (by omega)),fun r h6 h15=>(c.regs r (Ne.symm h6)).trans (regs r h15),
    c.bytes.congr mem.symm rfl⟩⟩
end CommitGolfCandidate.S4.Machine
