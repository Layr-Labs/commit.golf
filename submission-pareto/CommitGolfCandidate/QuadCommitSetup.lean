import CommitGolfCandidate.QuadCommitLeafLatch

/-! Pure register facts of the W3 setup prefix (words 0..9 are shared with the NonceChain image).
The image-level setup run of the NonceChain image is in `QuadNonceCommitSetup`. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 Leaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000


def initialInstructions : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,
   .LUI .x20 65537,.ADDI .x20 .x20 1768,.ADD .x20 .x9 .x20,
   .LUI .x22 442369,.ADDI .x22 .x22 0,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 0,.LUI .x11 65536,.ADDI .x11 .x11 0]


def readyInstructions : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.ADDI .x10 .x18 0,.SLLI .x7 .x13 11]


def setupOps := initialInstructions++[.ECALL]++readyInstructions


def initialPrefix (s : MachineState) (i : Nat) := (initialInstructions.take i).foldl execInstrBr s

def readyPrefix (s : MachineState) (i : Nat) := (readyInstructions.take i).foldl execInstrBr s


def readyState (s : MachineState) {bits : Nat} (coins : BitVec bits) :=
  readyPrefix (writeBits (initialPrefix s 13) (wordAddress (Leaves.leafSalt 0)) coins) 5


attribute [local irreducible] image leafCode quadCode quad2Code parentCode decodeInstruction execute writeBits


structure SetupRegisters (s : MachineState) : Prop where
  out : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  source : s.getReg .x18=4096
  leaves : s.getReg .x20=wordAddress (heapBase 0 0)
  salts : s.getReg .x22=wordAddress (Leaves.leafSalt 0)
  target : s.getReg .x10=wordAddress (Leaves.leafSalt 0)
  size : s.getReg .x11=268435456
  selector : s.getReg .x5=2


theorem setup_registers (s : MachineState) (entry : CommitEntry s) : SetupRegisters (initialPrefix s 13) := by
  constructor <;>
    dsimp [initialPrefix,initialInstructions,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x10=4096 from entry.message,
    show s.regs .x11=4294971392 from entry.commitment,show s.regs .x12=4294971424 from entry.heap]
  all_goals rfl


theorem setup_pc (s : MachineState) (pc : s.pc=4096) : (initialPrefix s 13).pc=4148 := by
  change s.pc+4+4+4+4+4+4+4+4+4+4+4+4+4=_
  rw [pc]
  rfl


def privateDraw (s : MachineState) : OracleComp World (BitVec (8*(s.getReg .x11).toNat)) :=
  liftM ($ᵗ BitVec (8*(s.getReg .x11).toNat) : ProbComp (BitVec (8*(s.getReg .x11).toNat)))


attribute [local irreducible] privateDraw


private theorem ready_prefix_register (s : MachineState) (r : Reg) :
    (readyPrefix s 5).getReg r = match r with
      | .x5 => 0 | .x7 => 2048 | .x10 => s.getReg .x18
      | .x11 => 200 | .x13 => 1 | _ => s.getReg r := by
  cases r <;> first | rfl | simp [readyPrefix,readyInstructions,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,Opening.getReg_setReg] <;> rfl

theorem ready_register (s : MachineState) {bits : Nat} (coins : BitVec bits) (r : Reg) :
    (readyState s coins).getReg r = match r with
      | .x5 => 0 | .x7 => 2048 | .x10 => (initialPrefix s 13).getReg .x18
      | .x11 => 200 | .x13 => 1 | _ => (initialPrefix s 13).getReg r := by
  unfold readyState
  rw [ready_prefix_register]
  cases r <;> simp only [CommitGolfCandidate.writeBits_register]

theorem ready_pc (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    (readyState s coins).pc=4172 := by
  change (writeBits (initialPrefix s 13) (wordAddress (Leaves.leafSalt 0)) coins).pc+4+4+4+4+4=4172
  rw [written_pc,setup_pc s entry.pc]
  rfl


theorem entry_regs (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    Regs (readyState s coins) 0 0 ∧
    (readyState s coins).getReg .x8=wordAddress (leafStart (2^24)+5) := by
  have r := setup_registers s entry
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [ready_register];exact r.source
  · rw [ready_register];exact r.leaves
  · rw [ready_register];exact r.salts
  · rw [ready_register]
  · rw [ready_register]
  · rw [ready_register]
  · rw [ready_register]
  · exact ready_pc s entry coins
  · rw [ready_register];exact r.out


theorem ready_memory (s : MachineState) {bits : Nat} (coins : BitVec bits) :
    (readyState s coins).mem = (writeBits (initialPrefix s 13) (wordAddress (Leaves.leafSalt 0)) coins).mem := rfl


theorem initial_memory (s : MachineState) : (initialPrefix s 13).mem=s.mem := rfl


end TwoPermutationPrototype.Quad.Commit
