-- Pair-heads copy of TwoPermutationPackedRecordInterface (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCollectTable
import CommitGolfCandidate.PairCheckModel
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.PairCheckGroupRun

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame checkSourceWord honestIndex)
open TwoPermutationPrototype.PairCertificate (pairHonestCheckInput)
open TwoPermutationPrototype.PairCk.PackedHonest (honestHeap)

def ProofWithin (input : CheckInput) : Prop :=
  534*input.positions.card ≤ input.proof.length ∧ input.proof.length ≤ 8959041024

structure RecordBlock where
  state : MachineState
  steps : Nat
  cycles : Nat
  rows : List PublicRow

/-- Register values that the following mark-table insertion and the next record read. -/
def RecordSaved (r : Reg) : Prop :=
  r = .x3 ∨ r = .x4 ∨ r = .x5 ∨ r = .x8 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨
  r = .x20 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 ∨ r = .x27

instance (r : Reg) : Decidable (RecordSaved r) := by unfold RecordSaved; infer_instance

structure RecordBlockFacts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (block : RecordBlock) : Prop where
  steps : block.steps ≤ 2025
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute pairImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute pairImage (block.steps+fuel) before false)) =
      ((tail.1.1.charge block.cycles 17,block.rows++tail.1.2),17+tail.2)
  pc : block.state.pc=0x13c0
  node : block.state.getReg .x6=
    BitVec.ofNat 64 (capGroup (honestIndex input.positions ordinal present).val)
  proof : block.state.getReg .x21=BitVec.ofNat 64 (checkProofByte (ordinal+1))
  saved : ∀ r, RecordSaved r → block.state.getReg r=before.getReg r
  /- PAIR: the even leaf path also writes its scratch window, words 131053–131096 (bytes 0x100000−152 ..< 0x100000+200). -/
  frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
    (word < 1534 ∨ 1576 ≤ word) → (word < 1673 ∨ 1690 ≤ word) → (word < 131053 ∨ 131097 ≤ word) →
    memoryView block.state word=memoryView before word
  trace :
    let index := honestIndex input.positions ordinal present
    Nonempty (RecordedLower oracle index.val (input.values index) (readBuffer block.state 12288 32) block.rows)
  honest : ∀ message salts, input=pairHonestCheckInput oracle message input.positions salts →
    readBuffer block.state 12288 32=honestHeap oracle message salts (capGroup (honestIndex input.positions ordinal present).val)

def RecordRefines (record : Oracle → Nat → Index → MachineState → RecordBlock) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState), ProofWithin input → RecordCursor input ordinal state →
    RecordInputFrame input ordinal state →
    RecordBlockFacts oracle input ordinal present state
      (record oracle ordinal (honestIndex input.positions ordinal present).val state)

end TwoPermutationPrototype.PairCk.Packed.Checker
