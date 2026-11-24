import CommitGolfCandidate.ChainedFirstPackInput
import CommitGolfCandidate.ChainedContinuationEntry

/-! State and ABI frames for the delivered shared internal-hash call. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem first_pack_return_pc (s : MachineState) :
    (firstPackPrefix s 31).pc = (s.getReg .x1+signExtend12 0) &&& ~~~1#64 := by
  rfl

attribute [local irreducible] firstPackPrefix writeBits

def hashPackStart (s : MachineState) : MachineState := execInstrBr s (.JAL .x1 16)
def hashPacked (s : MachineState) : MachineState := firstPackPrefix (hashPackStart s) 31

def hashContinued (s : MachineState) (answer : Output) : MachineState :=
  execInstrBr (execInstrBr (writeBits (hashPacked s) 256 answer) (.ADDI .x1 .x19 0)) (.JAL .x0 128)

theorem hash_pack_start_pc (s : MachineState) (pc : s.pc = 186612) :
    (hashPackStart s).pc = 186628 := by
  change s.pc+signExtend21 16 = _
  rw [pc]
  decide

theorem hash_packed_pc (s : MachineState) (pc : s.pc = 186612) : (hashPacked s).pc = 186616 := by
  rw [hashPacked,first_pack_return_pc]
  change (s.pc+4+signExtend12 0) &&& ~~~1#64 = _
  rw [pc]
  decide

theorem LoopArgs.packStart {s : MachineState} (args : LoopArgs s 256) :
    LoopArgs (hashPackStart s) 256 :=
  ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
    args.inputValid,args.outputValid,args.access⟩

theorem LoopArgs.packed {s : MachineState} (args : LoopArgs s 256) :
    LoopArgs (hashPacked s) 256 := by
  have frame (r : Reg) (kept : r ∉ ([.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29] : List Reg)) :
      (hashPacked s).getReg r = (hashPackStart s).getReg r := first_pack_register _ r kept
  exact ⟨(frame .x10 (by decide)).trans args.packStart.source,
    (frame .x12 (by decide)).trans args.packStart.target,
    (frame .x5 (by decide)).trans args.packStart.selector,
    (frame .x11 (by decide)).trans args.packStart.size,
    (frame .x13 (by decide)).trans args.packStart.kind,
    args.aligned,args.inputValid,args.outputValid,args.access⟩

theorem hash_packed_register (s : MachineState) (reg : Reg)
    (kept : reg ∉ ([.x1,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29] : List Reg)) :
    (hashPacked s).getReg reg = s.getReg reg := by
  rw [hashPacked,first_pack_register _ reg (by simp_all)]
  cases reg <;> first | exact (kept (by decide)).elim | rfl

theorem hash_link_register (s : MachineState) (reg : Reg) (kept : reg ≠ .x1) :
    (execInstrBr (execInstrBr s (.ADDI .x1 .x19 0)) (.JAL .x0 128)).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept rfl).elim | rfl

theorem hash_continued_register (s : MachineState) (answer : Output) (reg : Reg) (kept : reg ≠ .x1) :
    (hashContinued s answer).getReg reg = (hashPacked s).getReg reg := by
  rw [hashContinued,hash_link_register _ reg kept,writeBits_register]

theorem hash_continued_link (s : MachineState) (answer : Output) :
    (hashContinued s answer).getReg .x1 = s.getReg .x19 := by
  change (writeBits (hashPacked s) 256 answer).getReg .x19+signExtend12 0 = _
  rw [writeBits_register,hash_packed_register s .x19 (by decide)]
  exact BitVec.add_zero _

theorem LoopArgs.continued {s : MachineState} (args : LoopArgs s 256) (answer : Output) :
    LoopArgs (hashContinued s answer) 256 := by
  have frame (reg : Reg) (kept : reg ≠ .x1) := hash_continued_register s answer reg kept
  exact ⟨(frame .x10 (by decide)).trans args.packed.source,
    (frame .x12 (by decide)).trans args.packed.target,
    (frame .x5 (by decide)).trans args.packed.selector,
    (frame .x11 (by decide)).trans args.packed.size,
    (frame .x13 (by decide)).trans args.packed.kind,
    args.aligned,args.inputValid,args.outputValid,args.access⟩

theorem hash_continued_pc (s : MachineState) (pc : s.pc = 186612) (answer : Output) :
    (hashContinued s answer).pc = 186752 := by
  change (writeBits (hashPacked s) 256 answer).pc+4+signExtend21 128 = _
  have written : (writeBits (hashPacked s) 256 answer).pc = (hashPacked s).pc+4 := by
    simp only [writeBits,MachineState.setPC]
  rw [written,hash_packed_pc s pc]
  decide

end CommitGolfCandidate.Chained.Native
