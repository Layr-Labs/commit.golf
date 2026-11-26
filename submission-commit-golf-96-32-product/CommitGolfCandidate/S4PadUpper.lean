import CommitGolfCandidate.S4Table
import CommitGolfCandidate.S4Pieces
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def padOp (j : Nat) := Instr.SD .x14 .x0 (BitVec.ofNat 12 (8*j))
def padWords (n : Nat) := (List.range n).map padOp
def padState (s : MachineState) : Nat→MachineState | 0=>s | j+1=>execInstrBr (padState s j) (padOp j)
private structure ClearedPad (s t : MachineState) (pc a n : Nat) : Prop where
  run : Runs .check s t n n
  pc : t.pc=pcAt (pc+n)
  regs : ∀ r,t.getReg r=s.getReg r
  away : SameOutside s t a (8*n)
  zero : ∀ j<8*n,byte t (a+j)=0

private theorem loop (s : MachineState) (site a : Nat) (pc : s.pc=pcAt site) (ptr : s.getReg .x14=W a)
    (al : a%8=0) (bounded : a+32≤MEMORY_BYTES) (n : Nat) (hn : n≤4) (room : site+n≤Code.check.count)
    (code : Matches .check site (padWords n)) : ClearedPad s (padState s n) site a n:=by
  induction n with
  | zero=>exact ⟨Runs.refl .check s,pc,fun _=>rfl,fun _ _ _=>rfl,fun _ h=>False.elim (by omega)⟩
  | succ k ih=>
    have eqv : padWords (k+1)=padWords k++[padOp k]:=by simp only [padWords,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    rw [eqv] at code
    let t:=padState s k
    have f:=ih (by omega) (by omega) code.left
    have enc : decodeInstruction (Code.check.word (site+k))=some (.base (padOp k)):=by simpa only [padWords,List.length_map,List.length_range] using code.right.head
    have form : ∀ j : Fin 4,signExtend12 (BitVec.ofNat 12 (8*j.val))=W (8*j.val):=by decide
    have addr : t.getReg .x14+signExtend12 (BitVec.ofNat 12 (8*k))=W (a+8*k):=by
      rw [show t.getReg .x14=W a from (f.regs .x14).trans ptr,show signExtend12 (BitVec.ofNat 12 (8*k))=W (8*k) from form ⟨k,by omega⟩];exact (BitVec.ofNat_add ..).symm
    obtain ⟨run,after,regs,w⟩:=zeroRun (by omega) f.pc enc addr (show Safe (a+8*k) 8 from ⟨by omega,by omega⟩)
    refine ⟨f.run.trans run,after.trans (congrArg pcAt (by omega)),fun r=>(regs r).trans (f.regs r),f.away.combined w.frame (by omega),?_⟩
    intro j bj;have e:=w (a+j) (by unfold MEMORY_BYTES at bounded;omega)
    by_cases prev:j<8*k
    · exact e.trans ((if_neg (by omega)).trans (f.zero j prev))
    · exact e.trans (if_pos (by omega))

theorem upperPad (s : MachineState) (site a : Nat) (pc : s.pc=pcAt site) (ptr : s.getReg .x14=W a)
    (al : a%8=0) (cap : a+32≤MEMORY_BYTES) (room : site+4≤Code.check.count) (code : Matches .check site (padWords 4)) :
    let t:=padState s 4
    Runs .check s t 4 4 ∧ t.pc=pcAt (site+4) ∧ (∀ r,t.getReg r=s.getReg r) ∧ SameOutside s t a 32 ∧ readBuffer t a 32=0 := by
  have f:=loop s site a pc ptr al cap 4 le_rfl room code
  refine ⟨f.run,f.pc,f.regs,f.away,?_⟩
  have data (j : Nat) (bj : j<32) : (padState s 4).getByte (W (a+j))=(0 : Late.Digest).extractLsb' (8*(0+j)) 8:=
    (f.zero j bj).trans BitVec.extractLsb'_zero.symm
  exact (read_serialized_slice _ _ _ 0 32 data).trans BitVec.extractLsb'_eq_self
end CommitGolfCandidate.S4.Machine
