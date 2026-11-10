import CommitGolfCandidate.CapCheckRecordsReady

/-! Actual record loads are admitted by the minimum-length gate and the
natural ordinal invariant. The sibling window includes all 68 words,
without flooring any trailing proof bytes or weakening the input bounds. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

private theorem sibling_access (address : Nat) (aligned : address%8=0)
    (bounded : address+8≤MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8=true := by
  have small : address<2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    bounded,aligned,decide_true,Bool.true_and]

theorem cap_check_records_ready_admission (input : CheckInput) (ordinal remaining : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal remaining state)
    (positive : 0<remaining)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    accessValid (state.getReg .x24) 8=true ∧
    (∀ word : Fin 4,
      accessValid (state.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true) ∧
    (∀ word < 32,
      accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8=true) ∧
    (∀ word < 68,
      accessValid (state.getReg .x25+32+BitVec.ofNat 64 (8*word)) 8=true) := by
  have present : ordinal < input.positions.card := by have := ready.partition; omega
  have access := cap_check_record_access input ordinal present admitted enough
    state ready.indices ready.values ready.proof
  have bounds := cap_check_record_bounds input ordinal present admitted enough
  refine ⟨access.1,access.2.1,access.2.2,?_⟩
  intro word inside
  have aligned : (capProgram.layout.proof+576*ordinal+32+8*word)%8=0 := by
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
    omega
  have addressBound : capProgram.layout.proof+576*ordinal+32+8*word+8≤MEMORY_BYTES := by
    omega
  rw [ready.proof,show (32 : Word)=BitVec.ofNat 64 32 by rfl,
    ← BitVec.ofNat_add,← BitVec.ofNat_add]
  exact sibling_access _ aligned addressBound

end CommitGolfCandidate
