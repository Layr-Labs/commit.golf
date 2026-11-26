import CommitGolfCandidate.LateDraws

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] writeBits

theorem read_congr_mem (s t : MachineState) (r n : Nat) (eq : s.mem = t.mem) :
    readBuffer s r n = readBuffer t r n := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, eq]

private theorem br_mem (q : MachineState) : (branchBack q).mem = q.mem := by
  have choose (cond : Bool) (yes no : Word) :
      (if cond then q.setPC yes else q.setPC no).mem = q.mem := by cases cond <;> rfl
  exact choose (q.getReg .x20 != q.getReg .x0) (q.pc+signExtend13 6140) (q.pc+4)

private theorem add_mem (q : MachineState) (dst src : Reg) (imm : BitVec 12) :
    (execInstrBr q (.ADDI dst src imm)).mem = q.mem := by cases dst <;> rfl

attribute [local irreducible] branchBack

theorem next_memory (p : Nat) (s : MachineState) (w : PairCoins) :
    (nextPair p s w).mem = (writeBits s (s.getReg .x10) w).mem := by
  let r := randomStep s w
  have step : r.mem = (writeBits s (s.getReg .x10) w).mem := add_mem _ .x10 .x10 192
  by_cases e : p%256 = 255
  · change (if p%256 = 255 then branchBack (decrement r) else r).mem = _
    rw [if_pos e]
    exact (br_mem (decrement r)).trans ((add_mem r .x20 .x20 4095).trans step)
  · simpa only [nextPair, if_neg e] using step

theorem read_next (p : Nat) (s : MachineState) (w : PairCoins) (r n : Nat) (a : AtPair s p) :
    readBuffer (nextPair p s w) r n =
      readBuffer (writeBits s (BitVec.ofNat 64 (pairAddress p)) w) r n :=
  read_congr_mem _ _ _ _ ((next_memory p s w).trans
    (congrArg (fun addr => (writeBits s addr w).mem) a.dest))

end CommitGolfCandidate.Late
