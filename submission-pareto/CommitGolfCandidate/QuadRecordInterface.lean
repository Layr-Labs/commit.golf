import CommitGolfCandidate.QuadCollectTable
import CommitGolfCandidate.QuadGroupRun
import CommitGolfCandidate.QuadRecordGeometry
import CommitGolfCandidate.QuadLowerRecursion

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (honestIndex)
open TwoPermutationPrototype.Packed.Checker (RecordBlock RecordSaved)

open TwoPermutationPrototype.Quad.Honest (honestHeap)

structure RecordBlockFacts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (block : RecordBlock) : Prop where
  steps : block.steps ≤ 2025
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute packedImage (block.steps+fuel) before false)) =
      ((tail.1.1.charge block.cycles 17,block.rows++tail.1.2),17+tail.2)
  pc : block.state.pc=0x13c0
  node : block.state.getReg .x6=
    BitVec.ofNat 64 (Sampling.capGroup (honestIndex input.positions ordinal present).val)
  proof : block.state.getReg .x21=BitVec.ofNat 64 (checkProofByte (ordinal+1))
  saved : ∀ r, RecordSaved r → block.state.getReg r=before.getReg r
  frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
    (word < 1534 ∨ 1625 ≤ word) → memoryView block.state word=memoryView before word
  trace :
    let index := honestIndex input.positions ordinal present
    Nonempty (RecordedLower oracle index.val (input.values index) (readBuffer block.state 12288 32) block.rows)
  honest : ∀ message salts, input=honestCheckInput oracle message input.positions salts →
    readBuffer block.state 12288 32=honestHeap oracle message salts (Sampling.capGroup (honestIndex input.positions ordinal present).val)

def RecordRefines (record : Oracle → Nat → Index → MachineState → RecordBlock) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState), ProofWithin input → RecordCursor input ordinal state →
    RecordInputFrame input ordinal state →
    RecordBlockFacts oracle input ordinal present state
      (record oracle ordinal (honestIndex input.positions ordinal present).val state)

end TwoPermutationPrototype.Quad.Checker
