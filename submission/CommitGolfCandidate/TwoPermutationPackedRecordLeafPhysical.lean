import CommitGolfCandidate.TwoPermutationPackedRecordLeafBlock

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (beginRecord beginLower record_setup_register lower_setup_post
  lower_setup_register lower_setup_mem checkIndexWord checkSourceWord checker_positions_bound
  RecordInputFrame honestIndex check_recorded_bind check_recorded_map)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute readBuffer checkEvaluation

structure PhysicalFacts (oracle : Oracle) (ordinal : Nat) (index : Index) (before : MachineState)
    (out : RecordBlock) : Prop where
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps+fuel) before false)) =
      ((tail.1.1.charge out.cycles 3,out.rows++tail.1.2),3+tail.2)
  cursor : LowerCursor ordinal (QuartetCheck.flipIndex index) 0 out.state
  saved : LowerSaved before out.state
  frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
    (word < 1152 ∨ 1576 ≤ word) → (word < 1673 ∨ 1690 ≤ word) → memoryView out.state word=memoryView before word

private theorem exact_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (fuel : Nat) :
    let out := block oracle ordinal (honestIndex input.positions ordinal h).val s
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps+fuel) s false)) =
      ((tail.1.1.charge out.cycles 3,out.rows++tail.1.2),3+tail.2) := by
  let idx := (honestIndex input.positions ordinal h).val
  let raw := rawLeaf oracle ordinal idx s
  let q := quartetBlock oracle raw.1
  have qentry := raw_quartet_entry oracle input ordinal h s fits cursor framed
  have enough : 2 ≤ q.steps := by
    show 2 ≤ qCallSteps raw.1 + 1 + 7
    omega
  have leaf := raw_run oracle input ordinal h s fits cursor framed (q.steps - 2 + fuel)
  have quartetRun := quartet_block_run qentry oracle fuel
  dsimp only at leaf quartetRun
  rw [show 2 + (q.steps - 2 + fuel) = q.steps + fuel by omega] at leaf
  change checkEvaluation oracle (recordRows (execute packedImage (leafSteps idx + q.steps + fuel) s false)) = _
  rw [show leafSteps idx + q.steps + fuel = leafSteps idx + (q.steps + fuel) by omega, leaf, quartetRun]
  simp only [block, List.append_assoc, raw, idx, q]
  refine Prod.ext (Prod.ext ?_ rfl) ?_
  · simp [Execution.charge, ← Nat.add_assoc]
  · dsimp only
    omega

private theorem saved_ordinary (r : Reg) (keep : RecordSaved r) :
    LeafKept r ∧ r≠.x21 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem physical_facts (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    PhysicalFacts oracle ordinal (honestIndex input.positions ordinal h).val s
      (block oracle ordinal (honestIndex input.positions ordinal h).val s) := by
  let idx := (honestIndex input.positions ordinal h).val
  let raw := (rawLeaf oracle ordinal idx s).1
  obtain ⟨pc,position,rawKept,wordFrame,_,_⟩ := raw_view oracle input ordinal h s fits cursor framed
  have qentry := raw_quartet_entry oracle input ordinal h s fits cursor framed
  let reply := oracle.permutation (qInput raw)
  obtain ⟨qcursor,qsaved⟩ := q_final_regs qentry reply
  obtain ⟨qframe,_⟩ := q_final_memory qentry reply
  have finalSaved : LowerSaved s (qFinal raw reply) := by
    intro r safe
    exact (qsaved r safe).trans (rawKept r (saved_ordinary r safe).1)
  refine ⟨exact_run oracle input ordinal h s fits cursor framed,qcursor,finalSaved,?_⟩
  · intro w wBound src scratch slots
    exact (qframe w wBound (by omega) slots).trans (wordFrame w wBound src scratch)

end TwoPermutationPrototype.Packed.RecordLeaf
