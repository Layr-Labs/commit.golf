import CommitGolfCandidate.S4Pieces
import CommitGolfCandidate.S4ReadField
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def clearAt (i : Nat) := Instr.SD .x14 .x0 (BitVec.ofNat 12 (64+8*i))
def zeroOps (n : Nat) := (List.range n).map clearAt
def clearState (s : MachineState) : Nat→MachineState | 0=>s | j+1=>execInstrBr (clearState s j) (clearAt j)
structure Cleared (s t : MachineState) (pc n : Nat) : Prop where
  run : Runs .check s t n n
  pc : t.pc=pcAt (pc+n)
  regs : ∀ r,t.getReg r=s.getReg r
  outside : SameOutside s t 576 (8*n)
  bytes : ∀ j<8*n,byte t (576+j)=0

private theorem along (s : MachineState) (site : Nat) (pc : s.pc=pcAt site) (ptr : s.getReg .x14=W 512)
    (n : Nat) (hn : n≤4) (room : site+n≤Code.check.count) (code : Matches .check site (zeroOps n)) :
    Cleared s (clearState s n) site n := by
  induction n with
  | zero=>exact ⟨Runs.refl .check s,pc,fun _=>rfl,fun _ _ _=>rfl,fun _ h=>False.elim (by omega)⟩
  | succ k ih=>
    have list : zeroOps (k+1)=zeroOps k++[clearAt k]:=by simp only [zeroOps,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    rw [list] at code
    let t:=clearState s k
    have before:=ih (by omega) (by omega) code.left
    have enc : decodeInstruction (Code.check.word (site+k))=some (.base (clearAt k)):=by
      simpa only [zeroOps,List.length_map,List.length_range] using code.right.head
    have addr : t.getReg .x14+signExtend12 (BitVec.ofNat 12 (64+8*k))=W (576+8*k):=by
      rw [before.regs,ptr]
      have e : ∀ j : Fin 4,W 512+signExtend12 (BitVec.ofNat 12 (64+8*j.val))=W (576+8*j.val):=by decide
      exact e ⟨k,by omega⟩
    have safe : Safe (576+8*k) 8:=⟨by change 576+8*k+8≤2^36;omega,by change (576+8*k)%8=0;omega⟩
    obtain ⟨run,after,regs,w⟩:=zeroRun (by omega) before.pc enc addr safe
    refine ⟨before.run.trans run,after.trans (congrArg pcAt (by omega)),fun r=>(regs r).trans (before.regs r),
      before.outside.combined w.frame (by omega),?_⟩
    intro j bj;rw [show byte (clearState s (k+1)) (576+j)=_ from w (576+j) (by omega)]
    by_cases lo : j<8*k
    · rw [if_neg (by omega)];exact before.bytes j lo
    · exact if_pos (by omega)

theorem zeroRow (s : MachineState) (site : Nat) (pc : s.pc=pcAt site) (ptr : s.getReg .x14=W 512)
    (room : site+4≤Code.check.count) (code : Matches .check site (zeroOps 4)) :
    let t:=clearState s 4
    Cleared s t site 4 ∧ readBuffer t 576 32=0 := by
  have c:=along s site pc ptr 4 le_rfl room code
  refine ⟨c,?_⟩
  have bytes (j : Nat) (bj : j<32) : (clearState s 4).getByte (W (576+j))=(0 : Late.Digest).extractLsb' (8*(0+j)) 8:=
    (c.bytes j bj).trans BitVec.extractLsb'_zero.symm
  exact (read_serialized_slice _ _ _ 0 32 bytes).trans BitVec.extractLsb'_eq_self
end CommitGolfCandidate.S4.Machine
