import CommitGolfCandidate.CheckSound
import CommitGolfCandidate.InputOrder

/-! Soundness for arbitrary accepted inputs through the actual submitted checker ABI. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Index at a proof-record ordinal, using the same ordering as the input loader. -/
def recordIndex (input : CheckInput) (ordinal : Nat) : Index :=
  ⟨openingIndex input.positions ordinal, opening_index_bound input.positions ordinal⟩

/-- Value at a proof-record ordinal. Out-of-range ordinals are irrelevant to acceptance. -/
def recordValue (input : CheckInput) (ordinal : Nat) : Entry :=
  if present : ordinal < input.positions.card then
    input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present))
  else 0

/-- Salt parsed from the same proof bytes loaded by the checker. -/
def recordSalt (input : CheckInput) (ordinal : Nat) : Digest :=
  readBuffer (submission.initialState .check input) (submission.layout.proof+800*ordinal) 32

/-- Sibling parsed from the same proof bytes loaded by the checker. -/
def recordSibling (input : CheckInput) (ordinal level : Nat) : Digest :=
  readBuffer (submission.initialState .check input) (submission.layout.proof+800*ordinal+32+32*level) 32

private theorem initial_registers (program : Submission) (input : CheckInput) :
    (program.initialState .check input).getReg .x11 = BitVec.ofNat 64 program.layout.commitment ∧
    (program.initialState .check input).getReg .x13 = BitVec.ofNat 64 program.layout.indices ∧
    (program.initialState .check input).getReg .x14 = BitVec.ofNat 64 program.layout.values ∧
    (program.initialState .check input).getReg .x15 = BitVec.ofNat 64 program.layout.proof := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ready_memory (state : MachineState) :
    (checkReadyState (checkLengthState state)).mem = state.mem := rfl

attribute [local irreducible] checkReadyState checkLengthState

/-- Every record of an accepted machine proof authenticates its supplied value to
the supplied commitment. No honest-generation hypothesis is used. -/
theorem check_input_sound (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true) :
    ∀ ordinal < input.positions.card,
      recordRoot oracle.compression (recordValue input ordinal) (recordSalt input ordinal)
        (recordIndex input ordinal) (recordSibling input ordinal) = input.commitment := by
  let initial := submission.initialState .check input
  let ready := checkReadyState (checkLengthState initial)
  have cardinal : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card ≤ 16777216 := cardinal
  have registers := check_ready_registers initial
  have loaded := initial_registers submission input
  have rootPointer : ready.getReg .x26 = BitVec.ofNat 64 4294971392 := registers.2.2.2.2.1.trans loaded.1
  have valuePointer : ready.getReg .x8 = BitVec.ofNat 64 6576672800 := registers.2.2.1.trans loaded.2.2.1
  have proofPointer : ready.getReg .x25 = BitVec.ofNat 64 10871640096 := registers.2.2.2.1.trans loaded.2.2.2
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 6442455072 := registers.2.1.trans loaded.2.1
  have memory : ready.mem = initial.mem := ready_memory initial
  have rootData : readBuffer ready 4294971392 32 = input.commitment := by
    rw [read_buffer_memory_congr _ _ memory]
    exact check_input_commitment input
  have indexData (ordinal : Nat) (present : ordinal < input.positions.card) :
      ready.getMem (BitVec.ofNat 64 (6442455072+8*ordinal)) = BitVec.ofNat 64 (recordIndex input ordinal).val := by
    rw [show ready.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
    exact check_input_position input ordinal present
  have valueData (ordinal : Nat) (present : ordinal < input.positions.card) (block : Nat) (inside : block < 4) :
      readBuffer ready (6576672800+256*ordinal+64*block) 64 =
        (recordValue input ordinal).extractLsb' (512*block) 512 := by
    rw [read_buffer_memory_congr _ _ memory]
    simpa only [recordValue, dif_pos present, initial,
      show submission.layout.values = 6576672800 from rfl] using check_input_value_block input ordinal block present inside
  have saltData (ordinal : Nat) (_present : ordinal < input.positions.card) :
      readBuffer ready (10871640096+800*ordinal) 32 = recordSalt input ordinal := by
    rw [read_buffer_memory_congr _ _ memory]
    rfl
  have pathData (ordinal : Nat) (_present : ordinal < input.positions.card) (level : Nat) (_inside : level < 24) :
      readBuffer ready (10871640096+800*ordinal+32+32*level) 32 = recordSibling input ordinal level := by
    rw [read_buffer_memory_congr _ _ memory]
    rfl
  exact check_loop_sound oracle ready input.commitment (recordValue input) (recordSalt input)
    (recordIndex input) (recordSibling input) 4294971392 6576672800 10871640096 6442455072 input.positions.card
    registers.1 rootPointer valuePointer proofPointer indexPointer
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by omega) (by omega) rootData indexData valueData saltData pathData
    ((scheme_check_acceptance oracle input).mp accepted).2

/-- Every position in the input occurs at an in-range ordinal, with its exact
provided value. This relates conflicting claims to the machine's serialized records. -/
theorem record_for_position (input : CheckInput) (index : Index) (member : index ∈ input.positions) :
    ∃ ordinal, ordinal < input.positions.card ∧ recordIndex input ordinal = index ∧
      recordValue input ordinal = input.values ⟨index, member⟩ := by
  have inList : (⟨index, member⟩ : {i // i ∈ input.positions}) ∈
      input.positions.attach.sort (fun i j => i.val ≤ j.val) := by simp
  obtain ⟨ordinal, bound, same⟩ := List.mem_iff_getElem.mp inList
  have present : ordinal < input.positions.card := by simpa using bound
  have indexSame : recordIndex input ordinal = index := by
    apply Fin.ext
    have order := sorted_value_index input.positions ordinal present
    rw [same] at order
    exact order.symm
  refine ⟨ordinal, present, indexSame, ?_⟩
  simp only [recordValue, dif_pos present, same]

end CommitGolfCandidate
