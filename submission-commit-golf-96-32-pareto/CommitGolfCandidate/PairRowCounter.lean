import CommitGolfCandidate.PairBodyRegs
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

structure NextRegs (n : Nat) (s : MachineState) : Prop where
  pc : s.pc=if n=128 then 5276 else 4924
  ip : s.getReg .x24=BitVec.ofNat 64 (7650414624+8*n)
  vp : s.getReg .x8=BitVec.ofNat 64 (7784632352+256*n)
  pp : s.getReg .x25=BitVec.ofNat 64 (12079599648+536*n)
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-n)
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=16
  slots : s.getReg .x19=12079668256
  root : s.getReg .x26=4294971392

theorem remainingDec (m : MachineState) (n : Nat) (hn : n<128) (rem : m.getReg .x27=BitVec.ofNat 64 (128-n)) :
    m.getReg .x27 + signExtend12 4095 = BitVec.ofNat 64 (128-(n+1)) := by
    rw [rem,show 128-n=(128-(n+1))+1 by omega,BitVec.ofNat_add,BitVec.add_assoc,
      show BitVec.ofNat 64 1 + signExtend12 4095 = 0#64 by decide,BitVec.add_zero]

private theorem ifRegs (b : Bool) (s : MachineState) (x y : Word) :
    (if b then s.setPC x else s.setPC y).regs=s.regs := by cases b <;> rfl

theorem branchRegs (s : MachineState) :
    (execInstrBr s (.BNE .x27 .x0 7844)).regs=s.regs := by
  exact ifRegs (s.getReg .x27 != s.getReg .x0) s (s.pc+signExtend13 7844) (s.pc+4)

theorem latchRegs (m : MachineState) : (nextEdge m).regs=(recordNextState m).regs := branchRegs _

theorem latchValues (m : MachineState) :
    (recordNextState m).getReg .x27=m.getReg .x27+signExtend12 4095 ∧
    (recordNextState m).getReg .x24=m.getReg .x24+8#64 := by constructor <;> rfl
end CommitGolfCandidate.PairCap.Batch
