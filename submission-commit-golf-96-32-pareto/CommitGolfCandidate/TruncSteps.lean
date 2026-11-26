import CommitGolfCandidate.TruncWireImage
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 160000

def loc (i : Nat) := BitVec.ofNat 64 (4096+4*i)

def Runs (im : Image) (s t : MachineState) (steps cycles : Nat) := ∀ f coin,
  execute im (steps+f) s coin = (do let r←execute im f t coin;return r.charge cycles 0)

theorem runRefl (im : Image) (s : MachineState) : Runs im s s 0 0 := by
  intro f coin;simp [Execution.charge]

theorem chain {im s t u a b c d} (x : Runs im s t a b) (y : Runs im t u c d) :
    Runs im s u (a+c) (b+d) := by
  intro f coin;rw [Nat.add_assoc,x,y];simp [Execution.charge,← Nat.add_assoc,Nat.add_comm d b]

theorem one {im : Image} (i : Nat) (s t : MachineState) (op : Instr) (bound : i<2048)
    (pc : s.pc=loc i) (code : (im.code[i]?).bind decodeInstruction=some (.base op))
    (step : ordinaryStep s (.base op)=some t) (price : instructionCycles (.base op)=1) : Runs im s t 1 1 := by
  intro f coin;rw [Nat.add_comm 1 f,execute_ordinary_step _ _ _ _ _ _ (fetchAt im s i op bound pc code) step,price]

theorem jumpAt (im : Image) (s : MachineState) (i j : Nat) (off : BitVec 21) (bound : i<2048)
    (pc : s.pc=loc i) (code : (im.code[i]?).bind decodeInstruction=some (.base (.JAL .x0 off)))
    (offset : loc i+signExtend21 off=loc j) : Runs im s (s.setPC (loc j)) 1 1 := by
  apply one i _ _ (.JAL .x0 off) bound pc code _ rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,offset];rfl

end CommitGolfCandidate.Trunc
