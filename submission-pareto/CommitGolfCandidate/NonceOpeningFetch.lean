import CommitGolfCandidate.NonceCompactFetch


/-! The delivered opening image agrees with the cap-level opener on every word below 192 except
word 110, where the cap-level HALT becomes a jump to the compaction at word 192. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def nonceOldOpeningImage : Image := (capExperimental LOG_LENGTH).image .opening

theorem nonce_old_opening_length : nonceOldOpeningImage.code.length = 192 := by decide

theorem nonce_old_opening_halt_word : nonceOldOpeningImage.code[110]? = some 0x73 := by decide

theorem nonce_opening_head_same :
    s6OpeningImage.code.take 110 = nonceOldOpeningImage.code.take 110 := by decide

theorem nonce_opening_tail_same :
    (s6OpeningImage.code.drop 111).take 81 = nonceOldOpeningImage.code.drop 111 := by decide

theorem nonce_opening_word_same (index : Nat) (inside : index < 192) (other : index ≠ 110) :
    s6OpeningImage.code[index]? = nonceOldOpeningImage.code[index]? := by
  by_cases low : index < 110
  · have equal := congrArg (fun words : List (BitVec 32) => words[index]?) nonce_opening_head_same
    simpa only [List.getElem?_take, if_pos low] using equal
  · have equal := congrArg (fun words : List (BitVec 32) => words[index - 111]?) nonce_opening_tail_same
    have bounded : index - 111 < 81 := by omega
    simp only [List.getElem?_take, if_pos bounded, List.getElem?_drop] at equal
    have offset : 111 + (index - 111) = index := by omega
    simpa only [offset] using equal

theorem nonce_fetch_index (image : Image) (state : MachineState) (instruction : Instruction)
    (fetched : fetch image state = some instruction) :
    ∃ index, index < image.code.length ∧ state.pc = BitVec.ofNat 64 (4096 + 4 * index) ∧
      (image.code[index]?).bind decodeInstruction = some instruction := by
  have enabled : 4096 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0 := by
    by_contra invalid
    simp only [fetch, if_neg invalid] at fetched
    contradiction
  let index := (state.pc.toNat - 4096) / 4
  have decoded : (image.code[index]?).bind decodeInstruction = some instruction := by
    have equality := fetched
    simp only [fetch, if_pos enabled] at equality
    change (match image.code[index]? with | some word => decodeInstruction word | none => none) =
      some instruction at equality
    cases item : image.code[index]? <;> simpa only [item, Option.bind] using equality
  have bounded : index < image.code.length := by
    by_contra outside
    have absent : image.code[index]? = none := List.getElem?_eq_none (by omega)
    simp only [absent, Option.bind_none] at decoded
    contradiction
  refine ⟨index, bounded, ?_, decoded⟩
  have numeric : state.pc.toNat = 4096 + 4 * index := by dsimp only [index]; omega
  calc
    state.pc = BitVec.ofNat 64 state.pc.toNat := by simp
    _ = _ := by rw [numeric]

/-- Every instruction other than ECALL that the cap-level opener fetches is fetched unchanged. -/
theorem nonce_opening_ordinary_fetch (state : MachineState) (instruction : Instruction)
    (fetched : fetch nonceOldOpeningImage state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) :
    fetch s6OpeningImage state = some instruction := by
  obtain ⟨index, bounded, pc, decoded⟩ := nonce_fetch_index nonceOldOpeningImage state instruction fetched
  rw [nonce_old_opening_length] at bounded
  have notHalt : index ≠ 110 := by
    intro equal
    subst index
    rw [nonce_old_opening_halt_word] at decoded
    exact ordinary (Option.some.inj decoded).symm
  cases word : nonceOldOpeningImage.code[index]? with
  | none => rw [word] at decoded; contradiction
  | some value =>
    rw [word, Option.bind_some] at decoded
    rw [s6_image_fetch s6OpeningImage state index value (by omega) pc
      ((nonce_opening_word_same index bounded notHalt).trans word), decoded]

/-- Word 110: the jump into the compaction. -/
theorem nonce_opening_halt_replacement (state : MachineState) (pc : state.pc = 4536) :
    NonceRuns s6OpeningImage 1 state (state.setPC 4864) := by
  have fetched : fetch s6OpeningImage state = some (.base (.JAL .x0 328)) := by
    rw [s6_image_fetch s6OpeningImage state 110 343933039 (by omega) (by rw [pc]; rfl)
      s6_opening_word_jump]
    rfl
  apply nonce_runs_step fetched _ rfl
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, signExtend21, MachineState.setReg]

end CommitGolfCandidate
