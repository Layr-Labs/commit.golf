import CommitGolfCandidate.TwoPermutationPackedOperands
import CommitGolfCandidate.TwoPermutationPackedLowerControl
import CommitGolfCandidate.TwoPermutationPackedLowerRecursion
import CommitGolfCandidate.TwoPermutationPackedLowerHash

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

/-- Output projection of loop level `L` (`x29 = 14 - L`), whose node sits at tree level `21 - L`: the
level-21 node is whole, levels 20..17 keep 240 bits, levels 16..8 keep 238 bits. -/
inductive LevelKind | full | p240 | p238

def levelKind (level : Nat) : LevelKind := if level = 0 then .full else if level ≤ 4 then .p240 else .p238

/-- The 32-byte sibling path: loop counter `left ≥ 13` (loop levels 0 and 1). -/
def wideSibling (left : Nat) : Bool := decide (13 ≤ left)

/-- Ready for one step of loop levels 0..4 (counter `left` = 10..14). -/
structure LevelReady (s : MachineState) (node proof left : Nat) : Prop where
  pc : s.pc=4348
  nodeReg : s.getReg .x6=BitVec.ofNat 64 node
  proofReg : s.getReg .x21=BitVec.ofNat 64 proof
  counter : s.getReg .x29=BitVec.ofNat 64 left
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  selector : s.getReg .x5=0
  syscallBytes : s.getReg .x11=64
  syscallSelector : s.getReg .x13=0
  nodeBound : node<2^64
  leftLow : 10≤left
  leftBound : left≤14
  above : 32768≤proof
  even : proof%2=0
  room : proof+width (wideSibling left)≤MEMORY_BYTES

def levelPair (s : MachineState) (node proof left : Nat) :=
  pathPair node (readBuffer s 12288 32) (wire s proof (wideSibling left))

structure LevelFacts (oracle : Oracle) (s : MachineState) (node proof left : Nat) (block : RecordBlock) : Prop where
  pc : block.state.pc=(if left=1 then 5056 else 4348)
  nodeReg : block.state.getReg .x6=BitVec.ofNat 64 (node/2)
  proofReg : block.state.getReg .x21=BitVec.ofNat 64 (proof+width (wideSibling left))
  counter : block.state.getReg .x29=BitVec.ofNat 64 (left-1)
  syscallBytes : block.state.getReg .x11=64
  syscallSelector : block.state.getReg .x13=0
  saved : ∀ r, RecordSaved r → block.state.getReg r=s.getReg r
  frame : LowerFrame s block.state
  cost : block.steps≤116
  digest : readBuffer block.state 12288 32=levelProject left (oracle.compression (levelPair s node proof left))
  row : PublicRow.compression (levelPair s node proof left) (oracle.compression (levelPair s node proof left)) ∈ block.rows
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute packedImage (block.steps+fuel) s false)) =
      ((tail.1.1.charge block.cycles 1,block.rows++tail.1.2),1+tail.2)

end TwoPermutationPrototype.Packed.Checker
