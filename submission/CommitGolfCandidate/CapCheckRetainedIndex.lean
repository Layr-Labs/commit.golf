import CommitGolfCandidate.CapCheckIndexBytes
import CommitGolfCandidate.CapMemoryFrame

/-! Checker input identities survive every established high-byte frame.
The aligned-word extraction uses a 32-byte read only in the proof; the
actual index instruction remains a single eight-byte load. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_high_bytes_read (state reference : MachineState) (address count : Nat)
    (high : 22528 ≤ address) (bounded : address + count ≤ 2^64)
    (frame : CapHighBytes state reference) :
    readBuffer state address count = readBuffer reference address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset member
  have inside : offset < count := Finset.mem_range.mp member
  rw [frame (address + offset) (by omega) (by omega)]

theorem cap_check_retained_index (input : CheckInput) (state : MachineState)
    (ordinal : Nat) (bounded : ordinal < input.positions.card)
    (frame : CapHighBytes state (capProgram.initialState .check input)) :
    state.getMem (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) =
      BitVec.ofNat 64
        ((input.positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have high : 22528 ≤ capProgram.layout.indices + 8*ordinal := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have inside : capProgram.layout.indices + 8*ordinal + 32 ≤ 2^64 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  have aligned : (capProgram.layout.indices + 8*ordinal) % 8 = 0 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
  have same := cap_high_bytes_read state (capProgram.initialState .check input)
    (capProgram.layout.indices + 8*ordinal) 32 high inside frame
  have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) same
  have words : state.getMem (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) =
      (capProgram.initialState .check input).getMem
        (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) := by
    simpa only [read_digest_word _ _ 0 aligned (by decide),
      Nat.mul_zero, Nat.add_zero] using word
  exact words.trans (cap_check_input_index input ordinal bounded)

end CommitGolfCandidate
