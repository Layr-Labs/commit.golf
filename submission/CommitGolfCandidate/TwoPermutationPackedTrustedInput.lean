import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.K1Manifest
import CommitGolf.Artifact
import CommitGolfCandidate.TwoPermutationCheckLoader

namespace TwoPermutationPrototype.PackedChecker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

/-- The K1 submission: its check image is `packedImage` (567 words). -/
abbrev submission : Submission := K1Artifact.submission

private theorem initial_congr (a b : Submission) (layout : a.layout = b.layout) (sizes : a.sizes = b.sizes)
    (data : (a.image .check).data = (b.image .check).data) (input : CheckInput) :
    a.initialState .check input = b.initialState .check input := by
  cases a with | mk sz l im st =>
    cases b with | mk sz' l' im' st' =>
      change sz = sz' at sizes
      change l = l' at layout
      subst sz'
      subst l'
      change (im .check).data = (im' .check).data at data
      simp only [Submission.initialState, Submission.inputBuffers, Riscv.dataBase, data]
      rfl

/-- The trusted loader writes buffer data and registers from the ABI. The K1 and record check
submissions share the layout, the sizes and the (empty) check data, so their loaded states agree. -/
theorem initial_state (input : CheckInput) :
    submission.initialState .check input = QAssembly.submission.initialState .check input :=
  initial_congr K1Artifact.submission QuartetArtifact.submission rfl rfl (by
    show ArtifactEncoding.decode 8 K1Artifact.checkData = ArtifactEncoding.decode 8 QuartetArtifact.checkData
    rfl) input

private theorem admitted_reference (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) :
    input.proof.length ≤ QAssembly.submission.sizes.proof := by
  change input.proof.length ≤ 8959041024 at valid
  change input.proof.length ≤ 8959041024
  omega

theorem check_initial_registers (input : CheckInput) :
    let state := submission.initialState .check input
    state.pc = 4096 ∧
    state.getReg .x11 = 4294971392 ∧
    state.getReg .x13 = 9395245088 ∧
    state.getReg .x14 = 9529462880 ∧
    state.getReg .x15 = 13824430176 ∧
    state.getReg .x16 = BitVec.ofNat 64 input.positions.card ∧
    state.getReg .x17 = BitVec.ofNat 64 input.proof.length := by
  rw [initial_state]
  exact Checker.check_initial_registers input

theorem check_run_admitted (input : CheckInput)
    (admitted : input.proof.length ≤ submission.sizes.proof) :
    submission.run .check input =
      execute (submission.image .check) 34359803904 (submission.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem check_run_oversized (input : CheckInput)
    (oversized : submission.sizes.proof < input.proof.length) :
    submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
  have rejected := Nat.not_le.mpr oversized
  simp only [Submission.run,rejected,decide_false,Bool.false_eq_true,ite_false]

theorem check_scratch_word_zero (input : CheckInput) (address : Nat) (below : address+8 ≤ 4294971392) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 address) = 0 := by
  rw [initial_state]
  exact Checker.check_scratch_word_zero input address below

theorem check_input_commitment (input : CheckInput) :
    readBuffer (submission.initialState .check input) submission.layout.commitment 32 = input.commitment := by
  rw [initial_state]
  exact Checker.check_input_commitment input

theorem check_input_proof_byte (input : CheckInput) (valid : input.proof.length ≤ submission.sizes.proof)
    (offset : Nat) (inside : offset < input.proof.length) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 (submission.layout.proof+offset)) =
      input.proof[offset] := by
  rw [initial_state]
  exact Checker.check_input_proof_byte input (admitted_reference input valid) offset inside

theorem check_input_value (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card) :
    readBuffer (submission.initialState .check input) (submission.layout.values + 256*ordinal) 256 =
      input.values ((input.positions.attach.sort (· ≤ ·))[ordinal]'(by simpa using present)) := by
  rw [initial_state]
  exact Checker.check_input_value input ordinal present

theorem check_input_position (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 (submission.layout.indices+8*ordinal)) =
      BitVec.ofNat 64 ((input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)).val := by
  rw [initial_state]
  exact Checker.check_input_position input ordinal present

end TwoPermutationPrototype.PackedChecker
