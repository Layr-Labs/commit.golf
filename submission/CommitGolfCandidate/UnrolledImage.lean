import CommitGolfCandidate.UnrolledBlock
import CommitGolfCandidate.Group341Encoding

/-! Every instruction of the unrolled leaf block is linked to the delivered image:
four segments of 64 leaves and two rebase words, then the heap-end branch, the exit
jump to the parent setup and the loop jump. The block starts at word 251827. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def unrolledExitOffset : BitVec 21 := 1058332
def unrolledLoopOffset : BitVec 21 := 2065368

theorem unrolled_exit_jump :
    (1011404 : Word) + 31780 + signExtend21 unrolledExitOffset = 4364 := by decide

theorem unrolled_loop_jump :
    (1011404 : Word) + 31784 + signExtend21 unrolledLoopOffset = 1011404 := by decide

theorem unrolled_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 7947) (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * index))
    (decoded : decodeInstruction (unrolledBlockWord index) = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply commit_fetch state (251827 + index) instruction (by omega)
  · rw [pc]
    congr 1
    omega
  · change (group341ImageWords[251827 + index]?).bind decodeInstruction = _
    rw [unrolled_block_word_at index bounded]
    exact decoded

theorem unrolled_leaf_index (segment slot k : Nat) (hseg : segment < 4) (hslot : slot < 64)
    (hk : k < 31) :
    unrolledBlockWord (1986 * segment + 31 * slot + k) = unrolledLeafWord slot k := by
  unfold unrolledBlockWord unrolledSegmentWord
  rw [if_pos (by omega), show (1986 * segment + 31 * slot + k) % 1986 = 31 * slot + k by omega,
    if_pos (by omega), show (31 * slot + k) / 31 = slot by omega,
    show (31 * slot + k) % 31 = k by omega]

theorem unrolled_pc_sum (base first second : Nat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 first + BitVec.ofNat 64 second =
      BitVec.ofNat 64 (base + first + second) := by
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]

theorem unrolled_decode_carried (slot block : Nat) (hblock : block < 7) :
    decodeInstruction (unrolledLeafWord slot (7 + 3 * block)) = some (.base (.ADDI .x12 .x10 32)) := by
  interval_cases block <;> simp only [unrolledLeafWord] <;> rfl

theorem unrolled_decode_heap (slot : Nat) (hslot : slot < 64) :
    decodeInstruction (unrolledLeafWord slot 28) =
      some (.base (.ADDI .x12 .x23 (BitVec.ofNat 12 (32 * slot)))) := by
  interval_cases slot <;> rfl

theorem unrolled_decode_call (slot block : Nat) (hblock : block < 8) :
    decodeInstruction (unrolledLeafWord slot (8 + 3 * block)) = some (.base .ECALL) := by
  interval_cases block <;> simp only [unrolledLeafWord] <;> rfl

theorem unrolled_decode_advance (slot block : Nat) (hblock : block < 8) :
    decodeInstruction (unrolledLeafWord slot (9 + 3 * block)) = some (.base (.ADDI .x10 .x10 32)) := by
  interval_cases block <;> simp only [unrolledLeafWord] <;> rfl

theorem unrolled_decode_salt (slot i : Nat) (hslot : slot < 64) (hi : i < 7) :
    decodeInstruction (unrolledLeafWord slot i) =
      some (.base (((unrolledSaltInstructions slot)[i]?).getD .EBREAK)) := by
  interval_cases i
  · interval_cases slot <;> rfl
  · simp only [unrolledLeafWord, unrolledSaltInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rfl
  · interval_cases slot <;> rfl
  · simp only [unrolledLeafWord, unrolledSaltInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rfl
  · interval_cases slot <;> rfl
  · simp only [unrolledLeafWord, unrolledSaltInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rfl
  · simp only [unrolledLeafWord, unrolledSaltInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rfl

theorem unrolled_image_salt (segment slot : Nat) (hseg : segment < 4) (hslot : slot < 64) :
    UnrolledSaltFetched (submission.image .commit) slot
      ((1011404 : Word) + BitVec.ofNat 64 (7944 * segment) + BitVec.ofNat 64 (124 * slot)) := by
  intro state i hi pc
  apply unrolled_fetch state (1986 * segment + 31 * slot + i) _ (by omega)
  · rw [pc, show (1011404 : Word) = BitVec.ofNat 64 1011404 from rfl, unrolled_pc_sum,
      ← BitVec.ofNat_add]
    congr 1
    omega
  · rw [unrolled_leaf_index segment slot i hseg hslot (by omega)]
    exact unrolled_decode_salt slot i hslot hi

theorem unrolled_image_blocks (segment slot : Nat) (hseg : segment < 4) (hslot : slot < 64) :
    UnrolledBlocksFetched (submission.image .commit) slot
      ((1011404 : Word) + BitVec.ofNat 64 (7944 * segment) + BitVec.ofNat 64 (124 * slot) + 28) := by
  intro state block hblock
  have address (extra : Nat) (pc : state.pc = (1011404 : Word) + BitVec.ofNat 64 (7944 * segment) +
      BitVec.ofNat 64 (124 * slot) + 28 + BitVec.ofNat 64 (12 * block + extra)) :
      state.pc = BitVec.ofNat 64 (1011404 + 4 * (1986 * segment + 31 * slot + (7 + 3 * block)) + extra) := by
    rw [pc, show (1011404 : Word) = BitVec.ofNat 64 1011404 from rfl,
      show (28 : Word) = BitVec.ofNat 64 28 from rfl, unrolled_pc_sum, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
    congr 1
    omega
  refine ⟨fun pc => ?_, fun pc => ?_, fun pc => ?_⟩
  · apply unrolled_fetch state (1986 * segment + 31 * slot + (7 + 3 * block)) _ (by omega)
    · rw [address 0 (by simpa using pc)]
      rfl
    · rw [unrolled_leaf_index segment slot (7 + 3 * block) hseg hslot (by omega)]
      by_cases last : block = 7
      · subst last
        exact unrolled_decode_heap slot hslot
      · have notLast : decide (block = 7) = false := by simp [last]
        rw [notLast]
        exact unrolled_decode_carried slot block (by omega)
  · apply unrolled_fetch state (1986 * segment + 31 * slot + (8 + 3 * block)) _ (by omega)
    · rw [address 4 pc]
      congr 1
      omega
    · rw [unrolled_leaf_index segment slot (8 + 3 * block) hseg hslot (by omega)]
      exact unrolled_decode_call slot block hblock
  · apply unrolled_fetch state (1986 * segment + 31 * slot + (9 + 3 * block)) _ (by omega)
    · rw [address 8 pc]
      congr 1
      omega
    · rw [unrolled_leaf_index segment slot (9 + 3 * block) hseg hslot (by omega)]
      exact unrolled_decode_advance slot block hblock

theorem unrolled_image_segment (segment : Nat) (hseg : segment < 4) :
    UnrolledSegmentFetched (submission.image .commit)
      ((1011404 : Word) + BitVec.ofNat 64 (7944 * segment)) := by
  refine ⟨fun slot hslot => ⟨unrolled_image_salt segment slot hseg hslot,
    unrolled_image_blocks segment slot hseg hslot⟩, fun state pc => ?_, fun state pc => ?_⟩
  · apply unrolled_fetch state (1986 * segment + 1984) _ (by omega)
    · rw [pc, show (1011404 : Word) = BitVec.ofNat 64 1011404 from rfl,
        show (7936 : Word) = BitVec.ofNat 64 7936 from rfl, unrolled_pc_sum]
      congr 1
      omega
    · unfold unrolledBlockWord unrolledSegmentWord
      rw [if_pos (by omega), show (1986 * segment + 1984) % 1986 = 1984 by omega]
      rfl
  · apply unrolled_fetch state (1986 * segment + 1985) _ (by omega)
    · rw [pc, show (1011404 : Word) = BitVec.ofNat 64 1011404 from rfl,
        show (7940 : Word) = BitVec.ofNat 64 7940 from rfl, unrolled_pc_sum]
      congr 1
      omega
    · unfold unrolledBlockWord unrolledSegmentWord
      rw [if_pos (by omega), show (1986 * segment + 1985) % 1986 = 1985 by omega]
      rfl

/-- The delivered image contains the complete unrolled leaf block. -/
theorem unrolled_image_fetched :
    UnrolledBlockFetched (submission.image .commit) 1011404 unrolledExitOffset unrolledLoopOffset := by
  refine ⟨unrolled_image_segment, fun state pc => ?_, fun state pc => ?_, fun state pc => ?_⟩
  · apply unrolled_fetch state 7944 _ (by decide)
    · rw [pc]; rfl
    · rfl
  · apply unrolled_fetch state 7945 _ (by decide)
    · rw [pc]; rfl
    · rfl
  · apply unrolled_fetch state 7946 _ (by decide)
    · rw [pc]; rfl
    · rfl

end CommitGolfCandidate
