import CommitGolfCandidate.CheckSound
import CommitGolfCandidate.InputOrder

/-! Soundness for arbitrary accepted inputs through the actual submitted checker ABI,
covering both normal openings (`k ≠ 128`) and level-7 cap-table openings (`k = 128`). -/
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

/-- 16-byte salt parsed from the same proof bytes loaded by the checker (`560`-byte stride in cap mode,
`784`-byte stride in normal mode). -/
def recordSalt (input : CheckInput) (ordinal : Nat) : Salt :=
  let stride := if input.positions.card = BATCH then 560 else 784
  readBuffer (submission.initialState .check input) (submission.layout.proof + stride * ordinal) 16

/-- Level-7 cap digest `slot ∈ 0..127` parsed from a cap-mode proof buffer. -/
def recordCap (input : CheckInput) (slot : Nat) : Digest :=
  capTableOf (submission.initialState .check input) slot

/-- Full 24-level sibling digest for record `ordinal`. In normal mode all 24 siblings come
from the proof buffer; in cap mode levels `0..16` come from the proof buffer and levels
`17..23` come deterministically from the 128-leaf level-7 cap tree under `compress`. -/
def recordSibling (compress : Compression) (input : CheckInput) (ordinal level : Nat) : Digest :=
  if input.positions.card = BATCH then
    if level < 17 then
      readBuffer (submission.initialState .check input)
        (submission.layout.proof + 560 * ordinal + 16 + 32 * level) 32
    else
      referenceHeap compress 128 (recordCap input)
        (((128 + (recordIndex input ordinal).val / 2 ^ 17) / 2 ^ (level - 17)) ^^^ 1)
  else
    readBuffer (submission.initialState .check input)
      (submission.layout.proof + 784 * ordinal + 16 + 32 * level) 32

private theorem range_24_split :
    List.range 24 = List.range 17 ++ (List.range 7).map (· + 17) := by
  decide

private theorem record_root_of_cap (compress : Compression) (value : Entry) (salt : Salt)
    (index : Index) (cap : Nat → Digest) (siblings : Nat → Digest) (commitment : Digest)
    (upper : ∀ k < 7, siblings (k + 17) =
      referenceHeap compress 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ k) ^^^ 1))
    (hLow : recordAncestor compress 17 value salt index siblings = cap (index.val / 2 ^ 17))
    (hTop : referenceHeap compress 128 cap 1 = commitment) :
    recordRoot compress value salt index siblings = commitment := by
  let q := index.val / 2 ^ 17
  have hq : q < 128 := by
    have hlt : index.val < 2 ^ 24 := index.isLt
    change index.val / 2 ^ 17 < 128; omega
  let upperPath := (List.range 7).map fun k => (index.val.testBit (k + 17), siblings (k + 17))
  have pathSplit : recordPath index siblings = recordPathPrefix 17 index siblings ++ upperPath := by
    simp only [recordPath, recordPathPrefix, upperPath, range_24_split, List.map_append, List.map_map,
      Function.comp_def]
  have upperEq : upperPath = heapPath (referenceHeap compress 128 cap) (128 + q) 7 := by
    apply List.ext_getElem
    · simp only [upperPath, List.length_map, List.length_range, heap_path_length]
    · intro k hk1 hk2
      have hk : k < 7 := by simp only [upperPath, List.length_map, List.length_range] at hk1; exact hk1
      rw [heap_path_get _ (128 + q) 7 k hk]
      simp only [upperPath, List.getElem_map, List.getElem_range]
      refine Prod.ext ?_ (upper k hk)
      have hdir := heap_leaf_direction 7 q k hq hk
      change index.val.testBit (k + 17) = (2 ^ 7 + q).testBit k
      rw [hdir]
      dsimp only [q]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm 17 k]
  unfold recordRoot
  rw [pathSplit, climb, List.foldl_append]
  change climb compress (recordAncestor compress 17 value salt index siblings) upperPath = commitment
  rw [hLow, upperEq]
  have leafEq : cap q = referenceHeap compress 128 cap (2 ^ 7 + q) :=
    (reference_heap_leaf compress 128 cap q hq).symm
  rw [show (128 : Nat) = 2 ^ 7 by decide, leafEq]
  exact (reconstruct_heap_root compress (referenceHeap compress 128 cap) 7 q hq (fun p pos hi =>
    reference_heap_parent compress 128 cap p pos hi)).trans hTop

private theorem initial_registers (program : Submission) (input : CheckInput) :
    (program.initialState .check input).getReg .x11 = BitVec.ofNat 64 program.layout.commitment ∧
    (program.initialState .check input).getReg .x13 = BitVec.ofNat 64 program.layout.indices ∧
    (program.initialState .check input).getReg .x14 = BitVec.ofNat 64 program.layout.values ∧
    (program.initialState .check input).getReg .x15 = BitVec.ofNat 64 program.layout.proof := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ready_memory (state : MachineState) :
    (checkReadyState (checkLengthState state)).mem = state.mem := rfl

attribute [local irreducible] checkReadyState checkLengthState checkCapHash checkEvaluation
  checkRootWordsState

set_option maxHeartbeats 600000 in
/-- Every record of an accepted machine proof authenticates its supplied value to
the supplied commitment, for both normal and cap-table openings. -/
theorem check_input_sound (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true) :
    ∀ ordinal < input.positions.card,
      recordRoot oracle.compression (recordValue input ordinal) (recordSalt input ordinal)
        (recordIndex input ordinal) (recordSibling oracle.compression input ordinal) = input.commitment := by
  have acc := (scheme_check_acceptance oracle input).mp accepted
  let initial := submission.initialState .check input
  by_cases batch : input.positions.card = BATCH
  · rw [if_pos batch] at acc
    obtain ⟨lenOk, capMatch, loopAcc⟩ := acc
    let hashed := (checkEvaluation oracle (checkCapHash initial)).1
    let compared := checkRootWordsState hashed 138 4
    let entered := checkCapEnterLoopState compared
    have is128 : initial.getReg .x16 = 128 := by
      change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
    have isLen : initial.getReg .x17 = 75776 := by
      change BitVec.ofNat 64 input.proof.length = 75776; rw [lenOk]; rfl
    have reached : hashed ∈ support (checkCapHash initial) := check_evaluation_support oracle _
    have hRegs := check_cap_hash_registers initial hashed is128 isLen reached
    have cKeep (reg : Reg) (n6 : reg ≠ .x6) (n7 : reg ≠ .x7) : compared.getReg reg = hashed.getReg reg :=
      (check_root_words_preserves hashed 138 4 reg n6 n7).1
    have eMem : entered.mem = hashed.mem :=
      (check_root_words_preserves hashed 138 4 .x21 (by decide) (by decide)).2
    have eAbove (addr : Nat) (hi : 8704 ≤ addr) (lt64 : addr < 2 ^ 64) :
        entered.getMem (BitVec.ofNat 64 addr) = initial.getMem (BitVec.ofNat 64 addr) := by
      change entered.mem _ = _
      rw [eMem]
      exact check_cap_hash_support_outside initial hashed isLen reached (BitVec.ofNat 64 addr)
        (Or.inr (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt64]; exact hi))
    have eDigest (addr : Nat) (aligned : addr % 8 = 0) (hi : 8704 ≤ addr) (lt64 : addr + 32 < 2 ^ 64) :
        readBuffer entered addr 32 = readBuffer initial addr 32 := by
      apply read_digest_congr _ _ _ aligned
      intro w hw
      exact eAbove (addr + 8 * w) (by omega) (by omega)
    have eSalt (addr : Nat) (aligned : addr % 8 = 0) (hi : 8704 ≤ addr) (lt64 : addr + 16 < 2 ^ 64) :
        readBuffer entered addr 16 = readBuffer initial addr 16 := by
      apply read_salt_congr _ _ _ aligned
      intro w hw
      exact eAbove (addr + 8 * w) (by omega) (by omega)
    have enterKeep (reg : Reg) (n21 : reg ≠ .x21) (n26 : reg ≠ .x26) (n30 : reg ≠ .x30) :
        entered.getReg reg = compared.getReg reg := by
      simp only [entered, checkCapEnterLoopState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n30),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n26)]
    have targetPtr : entered.getReg .x26 = BitVec.ofNat 64 (10871640096 + 71680) := by
      simp only [entered, checkCapEnterLoopState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x26),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x26),
        MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
        cKeep .x19 (by decide) (by decide), hRegs.2.2.2.1]; rfl
    have valuePtr : entered.getReg .x8 = BitVec.ofNat 64 6576672800 := by
      rw [enterKeep .x8 (by decide) (by decide) (by decide), cKeep .x8 (by decide) (by decide),
        hRegs.2.2.2.2.1]; rfl
    have proofPtr : entered.getReg .x25 = BitVec.ofNat 64 10871640096 := by
      rw [enterKeep .x25 (by decide) (by decide) (by decide), cKeep .x25 (by decide) (by decide),
        hRegs.2.2.2.2.2.2.1]; rfl
    have indexPtr : entered.getReg .x24 = BitVec.ofNat 64 6442455072 := by
      rw [enterKeep .x24 (by decide) (by decide) (by decide), cKeep .x24 (by decide) (by decide),
        hRegs.2.2.2.2.2.1]; rfl
    have targetData (slot : Nat) (hs : slot < 2 ^ (24 - 17)) :
        readBuffer entered (10871640096 + 71680 + 32 * slot) 32 = recordCap input slot := by
      rw [eDigest _ (by omega) (by omega) (by change _ + 32 * slot + 32 < 2 ^ 64; change slot < 128 at hs; omega)]
      rfl
    have indexData (ordinal : Nat) (present : ordinal < BATCH) :
        entered.getMem (BitVec.ofNat 64 (6442455072 + 8 * ordinal)) =
          BitVec.ofNat 64 (recordIndex input ordinal).val := by
      rw [eAbove _ (by omega) (by change ordinal < 128 at present; omega)]
      exact check_input_position input ordinal (by rw [batch]; exact present)
    have valueData (ordinal : Nat) (present : ordinal < BATCH) (block : Nat) (inside : block < 4) :
        readBuffer entered (6576672800 + 256 * ordinal + 64 * block) 64 =
          (recordValue input ordinal).extractLsb' (512 * block) 512 := by
      have ordLt : ordinal < input.positions.card := by rw [batch]; exact present
      rw [read_compression_halves _ _ (by omega),
        eDigest (6576672800 + 256 * ordinal + 64 * block + 32) (by omega) (by omega) (by change ordinal < 128 at present; omega),
        eDigest (6576672800 + 256 * ordinal + 64 * block) (by omega) (by omega) (by change ordinal < 128 at present; omega),
        ← read_compression_halves _ _ (by omega)]
      simpa only [recordValue, dif_pos ordLt, initial,
        show submission.layout.values = 6576672800 from rfl] using
        check_input_value_block input ordinal block ordLt inside
    have saltData (ordinal : Nat) (present : ordinal < BATCH) :
        readBuffer entered (10871640096 + (16 + 32 * 17) * ordinal) 16 = recordSalt input ordinal := by
      rw [eSalt _ (by omega) (by omega) (by change ordinal < 128 at present; omega)]
      simp only [recordSalt, if_pos batch, initial]; rfl
    have pathData (ordinal : Nat) (present : ordinal < BATCH) (level : Nat) (inside : level < 17) :
        readBuffer entered (10871640096 + (16 + 32 * 17) * ordinal + 16 + 32 * level) 32 =
          recordSibling oracle.compression input ordinal level := by
      rw [eDigest _ (by omega) (by omega) (by change ordinal < 128 at present; omega)]
      simp only [recordSibling, if_pos batch, if_pos inside, initial]; rfl
    have hLowAll := check_loop_sound oracle entered (recordCap input) (recordValue input)
      (recordSalt input) (recordIndex input) (recordSibling oracle.compression input)
      17 (10871640096 + 71680) 6576672800 10871640096 6442455072 BATCH
      (by decide) (by decide) rfl rfl targetPtr valuePtr proofPtr indexPtr
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      targetData indexData valueData saltData pathData loopAcc
    have hTop : referenceHeap oracle.compression 128 (recordCap input) 1 = input.commitment :=
      (check_cap_comparison oracle input batch lenOk).mp ((root_words_match_iff hashed).mp capMatch)
    intro ordinal present
    have ordB : ordinal < BATCH := by rw [← batch]; exact present
    apply record_root_of_cap oracle.compression _ _ _ (recordCap input) _ input.commitment _ (hLowAll ordinal ordB) hTop
    intro k hk
    simp only [recordSibling, if_pos batch, if_neg (show ¬ (k + 17 < 17) by omega), Nat.add_sub_cancel]
  · rw [if_neg batch] at acc
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
    have rootData (slot : Nat) (hs : slot < 2 ^ (24 - 24)) :
        readBuffer ready (4294971392 + 32 * slot) 32 = input.commitment := by
      have sz : slot = 0 := by change slot < 1 at hs; omega
      subst sz
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [read_buffer_memory_congr _ _ memory]
      exact check_input_commitment input
    have indexData (ordinal : Nat) (present : ordinal < input.positions.card) :
        ready.getMem (BitVec.ofNat 64 (6442455072 + 8 * ordinal)) =
          BitVec.ofNat 64 (recordIndex input ordinal).val := by
      rw [show ready.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
      exact check_input_position input ordinal present
    have valueData (ordinal : Nat) (present : ordinal < input.positions.card) (block : Nat) (inside : block < 4) :
        readBuffer ready (6576672800 + 256 * ordinal + 64 * block) 64 =
          (recordValue input ordinal).extractLsb' (512 * block) 512 := by
      rw [read_buffer_memory_congr _ _ memory]
      simpa only [recordValue, dif_pos present, initial,
        show submission.layout.values = 6576672800 from rfl] using
        check_input_value_block input ordinal block present inside
    have saltData (ordinal : Nat) (_present : ordinal < input.positions.card) :
        readBuffer ready (10871640096 + (16 + 32 * 24) * ordinal) 16 = recordSalt input ordinal := by
      rw [read_buffer_memory_congr _ _ memory]
      simp only [recordSalt, if_neg batch, initial]; rfl
    have pathData (ordinal : Nat) (_present : ordinal < input.positions.card) (level : Nat) (_inside : level < 24) :
        readBuffer ready (10871640096 + (16 + 32 * 24) * ordinal + 16 + 32 * level) 32 =
          recordSibling oracle.compression input ordinal level := by
      rw [read_buffer_memory_congr _ _ memory]
      simp only [recordSibling, if_neg batch, initial]; rfl
    exact check_loop_sound oracle ready (fun _ => input.commitment) (recordValue input)
      (recordSalt input) (recordIndex input) (recordSibling oracle.compression input)
      24 4294971392 6576672800 10871640096 6442455072 input.positions.card
      (by decide) (by decide) registers.2.2.2.2.2.2 registers.1
      rootPointer valuePointer proofPointer indexPointer
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega) rootData indexData valueData saltData pathData
      acc.2

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
