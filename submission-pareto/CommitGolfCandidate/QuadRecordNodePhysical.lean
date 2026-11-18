import CommitGolfCandidate.QuadRecordNodeData

namespace TwoPermutationPrototype.Quad.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Checker
open TwoPermutationPrototype.Checker (beginRecord honestIndex check_recorded_bind check_recorded_map)
open TwoPermutationPrototype.Packed.Checker (RecordBlock RecordSaved)
open TwoPermutationPrototype.Packed (copy_field_execute)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute readBuffer checkEvaluation leafToQuad quadReply quadWorkspace quadNode recordRows

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
  let mid := leafToQuad raw.1
  have ready := node_entry_facts oracle input ordinal h s fits cursor framed
  have entryPC := cursor.pc.trans (ite_eq_right (by omega))
  have card := checker_positions_bound input
  have access : accessValid (s.getReg .x8) 8 = true := by
    rw [cursor.index]; apply aligned_access; unfold checkIndexWord; omega
  have counted : (checkEvaluation oracle (recordRows query)).2=2 := by
    dsimp only [query]; rw [checker_leaf_rows]
  have pc : raw.1.pc=4328 := (raw_view oracle input ordinal h s fits cursor framed).1
  change checkEvaluation oracle (recordRows (execute packedImage (182+fuel) s false)) = _
  rw [show 182+fuel=6+(16+(14+(2+(144+fuel)))) by omega,execute_record_setup s entryPC _ access]
  simp only [bind_pure_comp,check_recorded_map]
  rw [nonce_stage_run input ordinal h s fits cursor]
  simp only [bind_pure_comp,check_recorded_map]
  rw [execute_checker_leaf (leaf_ready input ordinal h s fits cursor framed),check_recorded_bind]
  simp only [bind_pure_comp,check_recorded_map]
  erw [leaf_to_quad_hop raw.1 pc]
  simp only [bind_pure_comp,check_recorded_map]
  erw [execute_quad_node mid _ _ fuel ready.pc ready.ready.pair ready.ready.digest ready.ready.opened
    ready.ready.source ready.ready.room ready.ready.even ready.selector ready.size ready.primitive]
  rw [check_recorded_bind]
  rw [quad_node_observation oracle mid _ _ ready.ready]
  simp only [bind_pure_comp,check_recorded_map]
  rw [counted]
  simp only [block,Execution.charge,←Nat.add_assoc,Nat.reduceAdd,Nat.zero_add,Nat.add_zero,List.append_assoc] <;> rfl

private theorem saved_ordinary (r : Reg) (keep : RecordSaved r) :
    r≠.x6 ∧ r≠.x28 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x21 ∧ r≠.x29 ∧ r≠.x30 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem shift_word (word : Nat) (bound : word < 2^64) :
    BitVec.ofNat 64 word >>> 2=BitVec.ofNat 64 (word/4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt (by omega : word/4 < 2^64),Nat.shiftRight_eq_div_pow]

theorem leaf_block_refines : LeafBlockRefines block := by
  intro oracle input ordinal h s fits cursor framed
  let idx := (honestIndex input.positions ordinal h).val
  let raw := (rawLeaf oracle ordinal idx s).1
  let mid := leafToQuad raw
  let answer := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))
  have ready := node_entry_facts oracle input ordinal h s fits cursor framed
  obtain ⟨pc,position,rawKept,wordFrame⟩ := raw_view oracle input ordinal h s fits cursor framed
  have params := quad_reply_post mid _ _ ready.ready answer
  have finalSaved : LowerSaved s (quadReply mid answer) := by
    intro r safe
    obtain ⟨h6,h28,h10,h11,h13,h12,h31,h21,h29,h30⟩ := saved_ordinary r safe
    exact (quad_reply_saved mid _ _ ready.ready answer r h6 h10 h11 h12 h13 h21 h28 h29 h30 h31).trans
      ((leaf_to_quad_saved raw r h21 h6).trans (rawKept r h6 h28 h10 h11 h13 h12 h31))
  refine ⟨by change 182 ≤ 182; omega,exact_run oracle input ordinal h s fits cursor framed,?_,finalSaved,?_,
    block_trace oracle input ordinal h s fits cursor framed,block_honest oracle input ordinal h s fits cursor framed⟩
  · change LowerCursor ordinal idx 0 (quadReply mid answer)
    refine ⟨params.1,?_,?_,params.2.2.2.2.2,(finalSaved .x23 (by decide)).trans cursor.digest,
      (finalSaved .x24 (by decide)).trans cursor.pair,(finalSaved .x5 (by decide)).trans cursor.selector,
      params.2.2.2.1,params.2.2.2.2.1⟩
    · have midNode : mid.getReg .x6=BitVec.ofNat 64 (LENGTH+idx.val) := ready.node
      rw [params.2.1,midNode,shift_word _ (by have b : idx.val < 16777216 := idx.isLt; change 16777216+idx.val < 2^64; omega)]
      rfl
    · exact params.2.2.1
  · intro w wb src scratch
    have nodeFrame := quad_reply_frame mid _ _ ready.ready answer w wb (by omega) (by omega)
    have mem := (leaf_to_quad_post raw pc).2.2.2
    exact nodeFrame.trans ((congrFun mem (wordAddress w)).trans (wordFrame w wb src (by omega)))

theorem actual_record_refines : RecordRefines (joinedRecord block (adaptLowerStep levelResult)) :=
  joined_record_refines block (adaptLowerStep levelResult) leaf_block_refines actual_lower_step

end TwoPermutationPrototype.Quad.RecordLeaf
