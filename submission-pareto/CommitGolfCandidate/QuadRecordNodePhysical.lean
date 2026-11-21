import CommitGolfCandidate.QuadRecordNodeData

namespace TwoPermutationPrototype.Quad.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Checker
open TwoPermutationPrototype.Checker (beginRecord honestIndex check_recorded_bind check_recorded_map)
open TwoPermutationPrototype.Packed.Checker (RecordBlock RecordSaved)
open TwoPermutationPrototype.Packed (copy_field_execute)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute readBuffer checkEvaluation leafToQuad quadReply quadWorkspace quadNode recordRows quadExit

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
      ((tail.1.1.charge out.cycles 5,out.rows++tail.1.2),5+tail.2) := by
  let idx := (honestIndex input.positions ordinal h).val
  let query := leafQueries (staged s) (checkSourceWord ordinal) idx
  let raw := rawLeaf oracle ordinal idx s
  let mid := leafToQuad raw.1
  let answer := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))
  let mid2 := quadReply mid answer
  let answer2 := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid2)))
  let mid3 := quadReply mid2 answer2
  let answer3 := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid3)))
  have ready := node_entry_facts oracle input ordinal h s fits cursor framed
  have ready2 := second_entry_facts oracle input ordinal h s fits cursor framed
  have ready3 := third_entry_facts oracle input ordinal h s fits cursor framed
  have entryPC := cursor.pc.trans (ite_eq_right (by omega))
  have card := checker_positions_bound input
  have access : accessValid (s.getReg .x8) 8 = true := by
    rw [cursor.index]; apply aligned_access; unfold checkIndexWord; omega
  have counted : (checkEvaluation oracle (recordRows query)).2=2 := by
    dsimp only [query]; rw [checker_leaf_rows]
  have pc : raw.1.pc=4328 := (raw_view oracle input ordinal h s fits cursor framed).1
  have indexBound : idx.val<16777216 := idx.isLt
  have finalPC : (quadReply mid3 answer3).pc=5824 := by
    have post := quad_reply_post mid3 _ _ ready3.ready answer3 ((LENGTH+idx.val)/16) ready3.node
      (by change (16777216+idx.val)/16<2^64; omega)
    rw [post.1,if_pos (by change (16777216+idx.val)/16/4/524288=0; omega)]
  change checkEvaluation oracle (recordRows (execute packedImage (466+fuel) s false)) = _
  rw [show 466+fuel=6+(16+(14+(2+(142+(141+(141+(4+fuel))))))) by omega,execute_record_setup s entryPC _ access]
  simp only [bind_pure_comp,check_recorded_map]
  rw [nonce_stage_run input ordinal h s fits cursor]
  simp only [bind_pure_comp,check_recorded_map]
  rw [execute_checker_leaf (leaf_ready input ordinal h s fits cursor framed),check_recorded_bind]
  simp only [bind_pure_comp,check_recorded_map]
  erw [leaf_to_quad_hop raw.1 pc]
  simp only [bind_pure_comp,check_recorded_map]
  erw [execute_quad_node mid _ _ _ ready.pc ready.ready.pair ready.ready.digest ready.ready.opened
    ready.ready.source ready.ready.room ready.ready.even ready.selector ready.size ready.primitive]
  rw [check_recorded_bind]
  rw [quad_node_observation oracle mid _ _ ready.ready]
  simp only [bind_pure_comp,check_recorded_map]
  erw [execute_quad_body mid2 _ _ _ ready2.pc ready2.ready.pair ready2.ready.digest ready2.ready.opened
    ready2.ready.source ready2.ready.room ready2.ready.even ready2.selector ready2.size ready2.primitive]
  rw [check_recorded_bind]
  rw [quad_node_observation oracle mid2 _ _ ready2.ready]
  simp only [bind_pure_comp,check_recorded_map]
  erw [execute_quad_body mid3 _ _ _ ready3.pc ready3.ready.pair ready3.ready.digest ready3.ready.opened
    ready3.ready.source ready3.ready.room ready3.ready.even ready3.selector ready3.size ready3.primitive]
  rw [check_recorded_bind]
  rw [quad_node_observation oracle mid3 _ _ ready3.ready]
  simp only [bind_pure_comp,check_recorded_map]
  erw [quad_exit_hop _ finalPC]
  simp only [bind_pure_comp,check_recorded_map]
  rw [counted]
  simp only [block,Execution.charge,←Nat.add_assoc,Nat.reduceAdd,Nat.zero_add,Nat.add_zero,List.append_assoc] <;> rfl

private theorem saved_ordinary (r : Reg) (keep : RecordSaved r) :
    r≠.x6 ∧ r≠.x28 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x21 ∧ r≠.x29 ∧ r≠.x30 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem leaf_block_refines : LeafBlockRefines block := by
  intro oracle input ordinal h s fits cursor framed
  let idx := (honestIndex input.positions ordinal h).val
  let raw := (rawLeaf oracle ordinal idx s).1
  let mid := leafToQuad raw
  let answer := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))
  let mid2 := quadReply mid answer
  let answer2 := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid2)))
  let mid3 := quadReply mid2 answer2
  let answer3 := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid3)))
  let final := quadReply mid3 answer3
  have ready := node_entry_facts oracle input ordinal h s fits cursor framed
  have ready2 := second_entry_facts oracle input ordinal h s fits cursor framed
  have ready3 := third_entry_facts oracle input ordinal h s fits cursor framed
  obtain ⟨pc,position,rawKept,wordFrame⟩ := raw_view oracle input ordinal h s fits cursor framed
  have indexBound : idx.val<16777216 := idx.isLt
  have params := quad_reply_post mid3 _ _ ready3.ready answer3 ((LENGTH+idx.val)/16) ready3.node
    (by change (16777216+idx.val)/16<2^64; omega)
  have finalPC : final.pc=5824 := by
    rw [params.1,if_pos (by change (16777216+idx.val)/16/4/524288=0; omega)]
  have exitPost := quad_exit_post final finalPC
  have finalSaved : LowerSaved s (quadExit final 4) := by
    intro r safe
    obtain ⟨h6,h28,h10,h11,h13,h12,h31,h21,h29,h30⟩ := saved_ordinary r safe
    exact (quad_exit_register final r h11 h13 h29).trans
      ((quad_reply_saved mid3 _ _ ready3.ready answer3 r h6 h10 h12 h21 h28 h29 h30 h31).trans
      ((quad_reply_saved mid2 _ _ ready2.ready answer2 r h6 h10 h12 h21 h28 h29 h30 h31).trans
      ((quad_reply_saved mid _ _ ready.ready answer r h6 h10 h12 h21 h28 h29 h30 h31).trans
      ((leaf_to_quad_saved raw r h21 h6).trans (rawKept r h6 h28 h10 h11 h13 h12 h31)))))
  refine ⟨by change 466 ≤ 466; omega,exact_run oracle input ordinal h s fits cursor framed,?_,finalSaved,?_,
    block_trace oracle input ordinal h s fits cursor framed,block_honest oracle input ordinal h s fits cursor framed⟩
  · change LowerCursor ordinal idx 0 (quadExit final 4)
    refine ⟨exitPost.1,?_,?_,exitPost.2.2.2.1,(finalSaved .x23 (by decide)).trans cursor.digest,
      (finalSaved .x24 (by decide)).trans cursor.pair,(finalSaved .x5 (by decide)).trans cursor.selector,
      exitPost.2.1,exitPost.2.2.1⟩
    · rw [quad_exit_register final .x6 (by decide) (by decide) (by decide),params.2.1]
      change BitVec.ofNat 64 ((16777216+idx.val)/16/4)=BitVec.ofNat 64 ((16777216+idx.val)/2^(0+6))
      congr 1
      omega
    · rw [quad_exit_register final .x21 (by decide) (by decide) (by decide),params.2.2.1]
      simp only [lowerProofByte,ite_true,Nat.add_assoc,Nat.reduceAdd]
  · intro w wb src scratch
    have mem := (leaf_to_quad_post raw pc).2.2.2
    have exitMem := quad_exit_memory final
    have frame3 := quad_reply_frame mid3 _ _ ready3.ready answer3 w wb (by omega) (by omega)
    have frame2 := quad_reply_frame mid2 _ _ ready2.ready answer2 w wb (by omega) (by omega)
    have frame1 := quad_reply_frame mid _ _ ready.ready answer w wb (by omega) (by omega)
    exact (congrFun exitMem (wordAddress w)).trans (frame3.trans (frame2.trans (frame1.trans
      ((congrFun mem (wordAddress w)).trans (wordFrame w wb src (by omega))))))

theorem actual_record_refines : RecordRefines (joinedRecord block (adaptLowerStep levelResult)) :=
  joined_record_refines block (adaptLowerStep levelResult) leaf_block_refines actual_lower_step

end TwoPermutationPrototype.Quad.RecordLeaf
