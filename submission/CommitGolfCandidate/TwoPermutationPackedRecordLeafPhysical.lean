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
  cursor : LowerCursor ordinal index 0 out.state
  saved : LowerSaved before out.state
  frame : ∀ word < 2^33, (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) →
    (word < 1534 ∨ 1576 ≤ word) → (word < 1673 ∨ 1690 ≤ word) → memoryView out.state word=memoryView before word

private theorem nonce_stage_run (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s) (fuel : Nat) :
    execute packedImage (16+fuel) (beginRecord s 6) false =
      (do let result ← execute packedImage fuel (staged s) false; return result.charge 16 0) :=
  copy_field_execute (fieldCode .nonce) _ _ _ (stage_ready input ordinal h s fits cursor) fuel false

private theorem exact_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (fuel : Nat) :
    let out := block oracle ordinal (honestIndex input.positions ordinal h).val s
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps+fuel) s false)) =
      ((tail.1.1.charge out.cycles 3,out.rows++tail.1.2),3+tail.2) := by
  let idx := (honestIndex input.positions ordinal h).val
  let query := leafQueries (staged s) (checkSourceWord ordinal) idx
  let raw := rawLeaf oracle ordinal idx s
  have entryPC := cursor.pc.trans (ite_eq_right (by omega))
  have card := checker_positions_bound input
  have access : accessValid (s.getReg .x8) 8 = true := by
    rw [cursor.index];apply aligned_access;unfold checkIndexWord;omega
  have counted : (checkEvaluation oracle (recordRows query)).2=2 := by
    dsimp only [query];rw [checker_leaf_rows]
  have qentry := raw_quartet_entry oracle input ordinal h s fits cursor framed
  change checkEvaluation oracle (recordRows (execute packedImage (168+fuel) s false)) = _
  rw [show 168+fuel=6+(16+(14+(132+fuel))) by omega,execute_record_setup s entryPC _ access]
  simp only [bind_pure_comp,check_recorded_map]
  rw [nonce_stage_run input ordinal h s fits cursor]
  simp only [bind_pure_comp,check_recorded_map]
  rw [execute_checker_leaf (leaf_ready input ordinal h s fits cursor framed),check_recorded_bind]
  simp only [bind_pure_comp,check_recorded_map]
  have quartetRun := quartet_block_run qentry oracle fuel
  change checkEvaluation oracle (recordRows (execute packedImage (132+fuel) raw.1 false)) = _ at quartetRun
  erw [quartetRun]
  change (let tail := checkEvaluation oracle (recordRows (execute packedImage fuel (quartetBlock oracle raw.1).state false))
          (((((tail.1.1.charge 139 1).charge 28 2).charge 16 0).charge 6 0,
              raw.2++((quartetBlock oracle raw.1).rows++tail.1.2)),(checkEvaluation oracle (recordRows query)).2+(1+tail.2))) = _
  rw [counted]
  simp only [Execution.charge,←Nat.add_assoc,Nat.reduceAdd,Nat.zero_add,Nat.add_zero]
  rw [show (block oracle ordinal idx s).rows = raw.2 ++ (quartetBlock oracle raw.1).rows from rfl, List.append_assoc]
  rfl

private theorem saved_ordinary (r : Reg) (keep : RecordSaved r) :
    r≠.x6 ∧ r≠.x28 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x21 ∧ r≠.x29 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem physical_facts (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    PhysicalFacts oracle ordinal (honestIndex input.positions ordinal h).val s
      (block oracle ordinal (honestIndex input.positions ordinal h).val s) := by
  let idx := (honestIndex input.positions ordinal h).val
  let raw := (rawLeaf oracle ordinal idx s).1
  obtain ⟨pc,position,rawKept,wordFrame⟩ := raw_view oracle input ordinal h s fits cursor framed
  have qentry := raw_quartet_entry oracle input ordinal h s fits cursor framed
  let reply := oracle.permutation (qInput raw)
  obtain ⟨qcursor,qsaved⟩ := q_final_regs qentry reply
  obtain ⟨qframe,_⟩ := q_final_memory qentry reply
  have finalSaved : LowerSaved s (qFinal raw reply) := by
    intro r safe
    obtain ⟨h6,h28,h10,h11,h13,h12,h31,h21,h29⟩ := saved_ordinary r safe
    exact (qsaved r safe).trans (rawKept r h6 h28 h10 h11 h13 h12 h31)
  refine ⟨exact_run oracle input ordinal h s fits cursor framed,qcursor,finalSaved,?_⟩
  · intro w wBound src scratch slots
    exact (qframe w wBound (by omega) slots).trans (wordFrame w wBound src scratch)

end TwoPermutationPrototype.Packed.RecordLeaf
