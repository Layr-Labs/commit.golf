-- Pair-heads copy of TwoPermutationPackedRecordComposition (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckLowerRecursion
import CommitGolfCandidate.PairCheckBinding
import CommitGolfCandidate.PairCheckModel
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.QuadReplay
import CommitGolfCandidate.QuartetCheckHeap

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex checker_positions_bound checkSourceWord)
open TwoPermutationPrototype.PairCertificate (pairHonestCheckInput)
open TwoPermutationPrototype.PairCk.PackedHonest (honestHeap honestLeaves)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- PAIR: the leaf rows are the parity-dispatched `pairFirstRow`/`pairSecondRow`. -/
structure PackedLeafTrace (oracle : Oracle) (index : Index) (entry : Entry) (digest : Digest)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (pairFirstRow oracle.permutation index (entryWords entry)).1
    (pairFirstRow oracle.permutation index (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).1
    (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  quartet : BitVec 1024
  reply : Block
  child : quartet.extractLsb' (256 * (index.val % 4)) 256 =
    outputDigest (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2
  parentRow : PublicRow.permutation (quadNodeCall.enc quartet) reply ∈ rows
  output : quadNodeCall.trunc reply = digest

structure LeafBlockFacts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (block : RecordBlock) : Prop where
  /- PAIR: the even leaf path takes 37 more steps (205 with the quartet block). -/
  steps : block.steps ≤ 206
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute pairImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute pairImage (block.steps+fuel) before false)) =
      ((tail.1.1.charge block.cycles 3,block.rows++tail.1.2),3+tail.2)
  cursor : LowerCursor ordinal (honestIndex input.positions ordinal present).val 0 block.state
  saved : LowerSaved before block.state
  frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
    (word < 1534 ∨ 1576 ≤ word) → (word < 1673 ∨ 1690 ≤ word) → (word < 131053 ∨ 131097 ≤ word) →
    memoryView block.state word=memoryView before word
  trace :
    let index := honestIndex input.positions ordinal present
    Nonempty (PackedLeafTrace oracle index.val (input.values index) (readBuffer block.state 12288 32) block.rows)
  honest : ∀ message salts, input=pairHonestCheckInput oracle message input.positions salts →
    readBuffer block.state 12288 32 =
      honestHeap oracle message salts (Opening.lowerNode (honestIndex input.positions ordinal present).val 2)

def LeafBlockRefines (leaf : Oracle → Nat → Index → MachineState → RecordBlock) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState), ProofWithin input → RecordCursor input ordinal state → RecordInputFrame input ordinal state →
      LeafBlockFacts oracle input ordinal present state
        (leaf oracle ordinal (honestIndex input.positions ordinal present).val state)

def joinedRecord (leaf : Oracle → Nat → Index → MachineState → RecordBlock)
    (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (oracle : Oracle) (ordinal : Nat) (index : Index) (state : MachineState) : RecordBlock :=
  let early := leaf oracle ordinal index state
  let later := runLower step oracle ordinal index 14 0 early.state
  ⟨later.state,early.steps+later.steps,early.cycles+later.cycles,early.rows++later.rows⟩

private theorem leaf_sibling_frame (before after : MachineState) (input : CheckInput) (ordinal level : Nat)
    (present : ordinal < input.positions.card) (within : level<14)
    (frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
      (word < 1534 ∨ 1576 ≤ word) → (word < 1673 ∨ 1690 ≤ word) → (word < 131053 ∨ 131097 ≤ word) →
      memoryView after word = memoryView before word) :
    lowerWireSibling after ordinal level = lowerWireSibling before ordinal level := by
  apply lower_wire_sibling_frame
  intro digit inside
  have card := checker_positions_bound input
  by_cases first : level = 0
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_true] at inside ⊢
    unfold checkProofByte
    exact frame _ (by omega) (Or.inr (by unfold checkSourceWord; omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega))
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_false] at inside ⊢
    unfold checkProofByte
    exact frame _ (by omega) (Or.inr (by unfold checkSourceWord; omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega))

attribute [local irreducible] execute checkEvaluation readBuffer

theorem joined_record_refines (leaf : Oracle → Nat → Index → MachineState → RecordBlock)
    (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (leafKernel : LeafBlockRefines leaf) (lowerKernel : LowerStepRefines step) :
    RecordRefines (joinedRecord leaf step) := by
  intro oracle input ordinal present before fits cursor framed
  let item := honestIndex input.positions ordinal present
  let early := leaf oracle ordinal item.val before
  let later := runLower step oracle ordinal item.val 14 0 early.state
  have entry : LeafBlockFacts oracle input ordinal present before early :=
    leafKernel oracle input ordinal present before fits cursor framed
  have room := (packed_record_geometry input ordinal present fits).2.2.2.1
  have tail := run_lower_facts step lowerKernel oracle ordinal item.val 14 0 (by decide) room early.state entry.cursor
  refine ⟨?_,?_,tail.cursor.pc.trans (ite_eq_left rfl),?_,?_,?_,?_,?_,?_⟩
  · have leafCost : early.steps ≤ 206 := entry.steps
    have lowerCost : later.steps ≤ 116*14 := tail.steps
    change early.steps+later.steps ≤ 2025
    omega
  · intro fuel
    dsimp only [joinedRecord]
    change checkEvaluation oracle (recordRows (execute pairImage (early.steps+later.steps+fuel) before false)) = _
    rw [show early.steps+later.steps+fuel=early.steps+(later.steps+fuel) by omega,
      entry.run, tail.exact_run]
    simp only [Execution.charge,List.append_assoc,← Nat.add_assoc,show (3:Nat)+14=17 by decide]
    rfl
  · exact tail.cursor.node.trans (congrArg (BitVec.ofNat 64) (Opening.lower_node_cap_group item.val))
  · exact tail.cursor.proof.trans (congrArg (BitVec.ofNat 64) (lower_proof_byte_end ordinal))
  · intro r saved
    exact (tail.saved _ saved).trans (entry.saved _ saved)
  · intro word bounded staged scratch slots window
    have a : word < 1536 ∨ 1540 ≤ word := by omega
    have b : word < 1568 ∨ 1576 ≤ word := by omega
    exact (tail.frame _ bounded a b).trans (entry.frame _ bounded staged scratch slots window)
  · obtain ⟨leafTrace⟩ := entry.trace
    have witness := tail.path.mono (fun _ found => List.mem_append_right early.rows found)
    rw [← leafTrace.output] at witness
    have node : Opening.lowerNode item.val (0+2) = LENGTH / 4 + item.val.val / 4 := QuartetCheck.lower_node_two item.val
    rw [node] at witness
    exact ⟨⟨leafTrace.nonce, List.mem_append_left later.rows leafTrace.first,
      List.mem_append_left later.rows leafTrace.second, leafTrace.quartet, leafTrace.reply, leafTrace.child,
      List.mem_append_left later.rows leafTrace.parentRow, witness⟩⟩
  · intro message salts canonical
    have loaded : RecordInputFrame (pairHonestCheckInput oracle message input.positions salts) ordinal before :=
      Eq.mp (congrArg (fun data => RecordInputFrame data ordinal before) canonical) framed
    change readBuffer later.state 12288 32 = honestHeap oracle message salts (capGroup item.val)
    apply tail.honest _ (honestLeaves oracle message salts)
    · exact entry.honest message salts canonical
    · intro level _ within
      rw [leaf_sibling_frame before early.state input ordinal level present within entry.frame]
      exact canonical_lower_wire_sibling oracle message input.positions salts ordinal present before loaded level within

end TwoPermutationPrototype.PairCk.Packed.Checker
