import CommitGolfCandidate.PairNextFrame
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4000
set_option maxHeartbeats 90000

private theorem regCongr {t u : MachineState} (m : u.regs=t.regs) (r : Reg) :
    u.getReg r=t.getReg r := by simp only [MachineState.getReg,m]

theorem latchCursor {H : Compression} {input : CheckInput} {p : Nat} {s t v u : MachineState}
    (inv : PairInvariant H input p s) (keep : Carries s t)
    (ctl : u.pc=(if p+1=128 then 5592 else 5416) ∧ u.regs=v.regs ∧ v.getReg .x27=BitVec.ofNat 64 (128-(p+1)))
    (delta : ∀ r∈pairRegs, v.getReg r=t.getReg r+pairStride r) : PairCursor (p+1) u := by
  have step (r : Reg) (hr : r∈pairRegs) : u.getReg r=s.getReg r+pairStride r :=
    (regCongr ctl.2.1 r).trans ((delta r hr).trans (congrArg (fun x=>x+pairStride r) (keep r hr)))
  refine ⟨ctl.1,?_,?_,?_,?_,?_,(regCongr ctl.2.1 .x27).trans ctl.2.2⟩
  · exact (step .x19 (by decide)).trans ((congrArg (fun w : Word=>w+32) inv.slots).trans (ptrAdd 10871707680 32 p))
  · exact (step .x22 (by decide)).trans ((congrArg (fun w : Word=>w+2) inv.marks).trans (ptrAdd 12288 2 p))
  · exact (step .x23 (by decide)).trans ((congrArg (fun w : Word=>w+96) inv.source).trans (ptrAdd 16384 96 p))
  · exact (step .x24 (by decide)).trans ((congrArg (fun w : Word=>w+32) inv.dest).trans (ptrAdd 4608 32 p))
  · exact (step .x26 (by decide)).trans ((BitVec.add_zero _).trans inv.root)

theorem memDigest {s t : MachineState} (m : t.mem=s.mem) (a : Nat) : digestAt t a=digestAt s a :=
  read_buffer_memory_congr t s m a 32
end CommitGolfCandidate.PairCap.Batch
