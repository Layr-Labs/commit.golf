import CommitGolfCandidate.S4Pieces
import CommitGolfCandidate.S4ReadField
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)
def clearCount (n : Nat) := if n=30 then 1 else 0
def addressOp (dst : Nat) := Instr.ADDI .x14 .x0 (BitVec.ofNat 12 dst)
def zeroWord := Instr.SD .x14 .x0 24
def loadPrefix (dst n : Nat) : List Instr := addressOp dst::(if n=30 then [zeroWord] else [])
def prepState (s : MachineState) (dst n : Nat) :=
  let t:=execInstrBr s (addressOp dst)
  if n=30 then execInstrBr t zeroWord else t

structure LoadPrefixResult (s t : MachineState) (site dst n : Nat) : Prop where
  run : Runs .check s t (1+clearCount n) (1+clearCount n)
  pc : t.pc=pcAt (site+(1+clearCount n))
  pointer : t.getReg .x14=W dst
  keep : ∀ r,Reg.x14≠r → t.getReg r=s.getReg r
  outside : SameOutside s t dst 32
  high : n=30 → ∀ j,30≤j → j<32 → byte t (dst+j)=0

theorem loadPrep (s : MachineState) (site dst n : Nat) (start : s.pc=pcAt site) (room : site+2≤Code.check.count)
    (imm : signExtend12 (BitVec.ofNat 12 dst)=W dst) (scratch : Safe (dst+24) 8)
    (code : Matches .check site (loadPrefix dst n)) :
    LoadPrefixResult s (prepState s dst n) site dst n := by
  let t:=execInstrBr s (addressOp dst)
  have first : Runs .check s t 1 1:=stepAdd _ _ _ _ _ _ (by omega) start code.head
  have ptr : t.getReg .x14=W dst:=by
    rw [show t.getReg .x14=s.getReg .x0+signExtend12 (BitVec.ofNat 12 dst) from getAfterAdd s .x14 .x0 _ (by decide),imm]
    change (0 : Word)+_=_
    exact BitVec.zero_add _
  have after : t.pc=pcAt (site+1):=addPC .x14 .x0 _ start
  have regs (r : Reg) (ne : Reg.x14≠r) : t.getReg r=s.getReg r:=keepAdd s .x14 .x0 r _ ne
  by_cases cut : n=30
  · subst n
    have actual : Matches .check (site+1) [zeroWord]:=by simpa only [loadPrefix,ite_true] using code.tail
    have add : t.getReg .x14+signExtend12 24=W (dst+24):=by rw [ptr];exact (BitVec.ofNat_add ..).symm
    obtain ⟨run,pc,keep,w⟩:=zeroRun (c:=.check) (by omega) after actual.head add scratch
    have frame : SameOutside s (execInstrBr t zeroWord) dst 32:=fun q b sep=>(w.frame q b (by omega))
    simp only [prepState,ite_true,clearCount]
    refine ⟨first.trans run,pc,(keep _).trans ptr,fun r ne=>(keep r).trans (regs r ne),frame,?_⟩
    intro _ j lo hi;exact (w (dst+j) (by have:=scratch.1;unfold MEMORY_BYTES at this;omega)).trans (if_pos (by omega))
  · have z : clearCount n=0:=if_neg cut
    have eqv : prepState s dst n=t:=if_neg cut
    rw [eqv]
    refine ⟨?_,?_,ptr,regs,fun _ _ _=>rfl,fun e=>False.elim (cut e)⟩
    · rw [z,Nat.add_zero];exact first
    · rw [z,Nat.add_zero];exact after
end CommitGolfCandidate.S4.Machine
