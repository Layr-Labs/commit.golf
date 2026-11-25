import CommitGolfCandidate.CheckSound

/-! Soundness and completeness for arbitrary inputs through the actual submitted checker ABI.
A nonempty opening is accepted exactly when the supplied cap chains to the commitment and
every supplied record climbs to the cap node selected by its index. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 8192

/-- Index at a proof-record ordinal, using the same ordering as the input loader. -/
def recordIndex (input : CheckInput) (ordinal : Nat) : Index :=
  ⟨openingIndex input.positions ordinal, opening_index_bound input.positions ordinal⟩

/-- Value at a proof-record ordinal. Out-of-range ordinals are irrelevant to acceptance. -/
def recordValue (input : CheckInput) (ordinal : Nat) : Entry :=
  if present : ordinal < input.positions.card then
    input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present))
  else 0

/-- Cap node parsed from the first 4096 proof bytes loaded by the checker. -/
def recordCap (input : CheckInput) (node : Nat) : Digest :=
  readBuffer (submission.initialState .check input) (submission.layout.proof+32*node) 32

/-- Salt parsed from the same proof bytes loaded by the checker. -/
def recordSalt (input : CheckInput) (ordinal : Nat) : Digest :=
  readBuffer (submission.initialState .check input) (submission.layout.proof+4096+576*ordinal) 32

/-- Sibling parsed from the same proof bytes loaded by the checker. -/
def recordSibling (input : CheckInput) (ordinal level : Nat) : Digest :=
  readBuffer (submission.initialState .check input)
    (submission.layout.proof+4096+576*ordinal+32+32*level) 32

attribute [local irreducible] checkReadyState checkLengthState checkEvaluation

set_option maxHeartbeats 1000000 in
/-- For a nonempty, correctly sized opening, the checker's acceptance condition after the
length gate is exactly: the supplied cap chains to the commitment, and every record
climbs to its cap node. -/
theorem check_input_accepts_iff (oracle : Oracle) (input : CheckInput)
    (positive : 0 < input.positions.card) :
    checkReadyAccepts oracle input.positions.card
        (checkReadyState (checkLengthState (submission.initialState .check input))) = true ↔
      capRoot oracle.compression (recordCap input) = input.commitment ∧
      ∀ ordinal < input.positions.card,
        recordRoot oracle.compression (recordValue input ordinal) (recordSalt input ordinal)
          (recordIndex input ordinal) (recordSibling input ordinal) =
            recordCap input ((recordIndex input ordinal).val / 2^PATH_LEVELS) := by
  let initial := submission.initialState .check input
  let ready := checkReadyState (checkLengthState initial)
  have cardinal : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card ≤ 16777216 := cardinal
  have registers := check_ready_registers initial
  have memory : ready.mem = initial.mem := check_ready_memory initial
  have readyScratch : ready.getReg .x21 = 256 := registers.1
  have readyProof : ready.getReg .x25 = BitVec.ofNat 64 10871640096 := registers.2.2.2.1
  have readyRoot : ready.getReg .x26 = BitVec.ofNat 64 4294971392 := registers.2.2.2.2.1
  have readyPC : ready.pc = 4164 := by
    rw [check_ready_pc]
    exact if_neg (by
      change BitVec.ofNat 64 input.positions.card ≠ 0
      intro zero
      have numeric : (BitVec.ofNat 64 input.positions.card).toNat = 0 := by rw [zero]; rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at numeric
      omega)
  let capped := capPhaseState oracle ready
  have cappedRegs := cap_phase_registers oracle ready readyPC
  have cappedOutside (address : Nat) (aligned : address % 8 = 0) (above : 352 ≤ address)
      (bounded : address + 32 < 2^64) :
      readBuffer capped address 32 = readBuffer initial address 32 :=
    (cap_phase_digest_outside oracle ready address readyScratch aligned above bounded).trans
      (read_buffer_memory_congr _ _ memory _ _)
  have capDigest : readBuffer capped 256 32 = capRoot oracle.compression (recordCap input) := by
    apply cap_phase_digest oracle ready 10871640096 (recordCap input) readyScratch readyProof
      (by decide) (by decide) (by decide)
    intro node inside
    rw [read_buffer_memory_congr _ _ memory]
    rfl
  have capMatch : rootWordsMatch true capped = true ↔
      capRoot oracle.compression (recordCap input) = input.commitment := by
    rw [root_words_match_iff, check_compare_digest true capped 4294971392
      ((cappedRegs.2.2.2 .x21 (by simp)).trans readyScratch)
      ((cappedRegs.2.2.2 .x26 (by simp)).trans readyRoot) (by decide),
      capDigest, cappedOutside 4294971392 (by decide) (by decide) (by decide)]
    rw [show readBuffer initial 4294971392 32 = input.commitment from check_input_commitment input]
  let compared := checkRootWordsState true capped 4
  have keep (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :=
    (check_root_words_preserves true capped 4 reg not6 not7).1
  have comparedMemory : compared.mem = capped.mem :=
    (check_root_words_preserves true capped 4 .x21 (by decide) (by decide)).2
  have comparedOutside (address : Nat) (aligned : address % 8 = 0) (above : 352 ≤ address)
      (bounded : address + 32 < 2^64) :
      readBuffer compared address 32 = readBuffer initial address 32 :=
    (read_buffer_memory_congr _ _ comparedMemory _ _).trans (cappedOutside address aligned above bounded)
  have comparedWord (address : Nat) (above : 352 ≤ address) (bounded : address < 2^64) :
      compared.getMem (BitVec.ofNat 64 address) = initial.getMem (BitVec.ofNat 64 address) := by
    have same : compared.getMem = capped.getMem := congrArg (fun mem address => mem address) comparedMemory
    rw [same, cap_phase_outside oracle ready _ readyScratch]
    · simp only [MachineState.getMem, memory]
    · intro i hi equal
      have natural := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
        Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
      omega
  have loopIff := check_loop_accepts_iff oracle compared (recordCap input) (recordValue input)
    (recordSalt input) (recordIndex input) (recordSibling input)
    10871640096 6576672800 10871644192 6442455072 input.positions.card
    ((keep .x21 (by decide) (by decide)).trans ((cappedRegs.2.2.2 .x21 (by simp)).trans readyScratch))
    ((keep .x30 (by decide) (by decide)).trans (cappedRegs.2.2.1.trans readyProof))
    ((keep .x8 (by decide) (by decide)).trans ((cappedRegs.2.2.2 .x8 (by simp)).trans registers.2.2.1))
    (by rw [keep .x25 (by decide) (by decide), cappedRegs.2.1, readyProof]; decide)
    ((keep .x24 (by decide) (by decide)).trans ((cappedRegs.2.2.2 .x24 (by simp)).trans registers.2.1))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by omega) (by omega)
    (fun node inside => by
      rw [comparedOutside _ (by omega) (by omega) (by omega)]
      rfl)
    (fun ordinal present => by
      rw [comparedWord _ (by omega) (by omega)]
      exact check_input_position input ordinal present)
    (fun ordinal present block inside => by
      rw [read_compression_halves _ _ (by omega),
        comparedOutside _ (by omega) (by omega) (by omega),
        comparedOutside _ (by omega) (by omega) (by omega),
        ← read_compression_halves _ _ (by omega)]
      simpa only [recordValue, dif_pos present, initial,
        show submission.layout.values = 6576672800 from rfl] using
          check_input_value_block input ordinal block present inside)
    (fun ordinal present => by
      rw [comparedOutside _ (by omega) (by omega) (by omega)]
      rfl)
    (fun ordinal present level inside => by
      rw [comparedOutside _ (by omega) (by omega) (by omega)]
      rfl)
  have nonempty : (input.positions.card == 0) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  unfold checkReadyAccepts
  rw [nonempty, Bool.false_or, Bool.and_eq_true]
  change rootWordsMatch true capped = true ∧ checkLoopAccepts oracle input.positions.card compared = true ↔ _
  rw [capMatch, loopIff]

/-- Every record of an accepted machine proof authenticates its supplied value to the
supplied cap node, and the supplied cap chains to the commitment. No honest-generation
hypothesis is used. -/
theorem check_input_sound (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (submission.scheme.check input.commitment input.positions
      input.values input.proof)).1 = true) :
    ∀ ordinal < input.positions.card,
      recordRoot oracle.compression (recordValue input ordinal) (recordSalt input ordinal)
          (recordIndex input ordinal) (recordSibling input ordinal) =
        recordCap input ((recordIndex input ordinal).val / 2^PATH_LEVELS) ∧
      capRoot oracle.compression (recordCap input) = input.commitment := by
  intro ordinal present
  have parts := ((check_input_accepts_iff oracle input (by omega)).mp
    ((scheme_check_acceptance oracle input).mp accepted).2)
  exact ⟨parts.2 ordinal present, parts.1⟩

/-- Completeness at the record level: a correctly sized proof whose cap chains to the
commitment and whose records climb to their cap nodes is accepted. -/
theorem check_input_complete (oracle : Oracle) (input : CheckInput)
    (length : input.proof.length = 4096 + 576 * input.positions.card)
    (cap : 0 < input.positions.card → capRoot oracle.compression (recordCap input) = input.commitment)
    (records : ∀ ordinal < input.positions.card,
      recordRoot oracle.compression (recordValue input ordinal) (recordSalt input ordinal)
          (recordIndex input ordinal) (recordSibling input ordinal) =
        recordCap input ((recordIndex input ordinal).val / 2^PATH_LEVELS)) :
    (oracle.eval (submission.scheme.check input.commitment input.positions
      input.values input.proof)).1 = true := by
  apply (scheme_check_acceptance oracle input).mpr
  refine ⟨length, ?_⟩
  by_cases empty : input.positions.card = 0
  · unfold checkReadyAccepts
    simp [empty]
  · exact (check_input_accepts_iff oracle input (by omega)).mpr ⟨cap (by omega), records⟩

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
