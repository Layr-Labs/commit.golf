import CommitGolfCandidate.CapOpenMarkedFinal

/-! Occupancy propagation and traversal initialization preserve the completed
high proof prefix and all high ABI inputs. Equality is relative to the completed
record state, whose low marks intentionally changed. The original proof base
in x15 is retained for the final reported length. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordsFinal capMarkMachinePass

theorem cap_open_marked_final_high
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapHighBytes (capOpenMarkedFinal trapdoor positions)
      (capOpenRecordsFinal trapdoor positions) := by
  have ready := cap_open_records_final_ready trapdoor positions positive
  have memory := cap_mark_pass_memory .x22 .x29 _ 4364 128 _
    (Or.inr rfl) (by decide) (by decide) (cap_tree_marks_parent _)
    (by simpa using ready.pc) ready.marks
    (cap_open_records_final_leaves trapdoor positions)
    (cap_open_records_marks_ready trapdoor positions positive)
  exact cap_high_bytes_memory _ _ _ memory
    (cap_mark_pass_frame _ _ 128 127 (by decide) (by decide) (cap_high_bytes_refl _))

theorem cap_open_traversal_initial_high
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapHighBytes (capOpenTraversalInitial trapdoor positions)
      (capOpenRecordsFinal trapdoor positions) :=
  cap_high_bytes_memory _ _ _ (cap_open_walk_initial_memory _)
    (cap_open_marked_final_high trapdoor positions positive)

theorem cap_open_traversal_initial_proof_base
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenTraversalInitial trapdoor positions).getReg .x15 =
      BitVec.ofNat 64 capProgram.layout.proof := by
  have base : (capProgram.initialState .opening (trapdoor, positions)).getReg .x15 =
      BitVec.ofNat 64 capProgram.layout.proof :=
    (cap_open_setup_registers _).2.2.1.symm.trans
      (cap_open_initial_proof_pointer trapdoor positions)
  have records : (capOpenRecordsFinal trapdoor positions).getReg .x15 =
      BitVec.ofNat 64 capProgram.layout.proof := by
    simpa only [capOpenRecordsFinal] using
      (cap_open_records_register positions.card
        (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions)))
        .x15 (by decide)).trans
        ((cap_open_setup_registers
          (capProgram.initialState .opening (trapdoor, positions))).2.2.2.2.2.2.2.2.2.1.trans base)
  exact (cap_open_walk_initial_register _ .x15 (by decide)).trans
    ((cap_open_marked_final_register trapdoor positions .x15 (by decide)).trans records)

end CommitGolfCandidate
