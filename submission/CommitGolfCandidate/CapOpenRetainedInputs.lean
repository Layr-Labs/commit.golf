import CommitGolfCandidate.CapCopyFrame
import CommitGolfCandidate.CapOpenInputFrame

/-! The opening record pass intentionally changes low occupancy words and high
proof-output bytes. Its retained-input frame therefore covers only the bounded
high interval below the initial output floor. This includes admitted trapdoor,
salt and index inputs without claiming equality for marks or output bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapOpenRetainedInputs (floor : Nat) (reference state : MachineState) : Prop :=
  ∀ address, 32768 ≤ address → address < floor →
    state.getByte (BitVec.ofNat 64 address) = reference.getByte (BitVec.ofNat 64 address)

theorem cap_open_retained_refl (floor : Nat) (state : MachineState) :
    CapOpenRetainedInputs floor state state := fun _ _ _ => rfl

theorem cap_open_retained_memory (floor : Nat) (state next reference : MachineState)
    (same : next.mem = state.mem) (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference next := by
  intro address high below
  have bytes : next.getByte = state.getByte := by
    funext pointer
    simp only [MachineState.getByte, MachineState.getMem, same]
  rw [bytes]
  exact frame address high below

theorem cap_open_retained_store (floor : Nat) (state reference : MachineState)
    (destination : Nat) (value : Word) (floorBound : floor ≤ 2^64)
    (low : destination < 32768) (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference
      (state.setMem (BitVec.ofNat 64 destination) value) := by
  have stored := cap_high_bytes_store state state destination value low
    (cap_high_bytes_refl state)
  intro address high below
  exact (stored address high (by omega)).trans (frame address high below)

theorem cap_open_retained_copy (floor cursor : Nat) (state reference : MachineState)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (cursorBound : cursor+32 ≤ 2^64)
    (before : floor ≤ cursor) (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference (capDigestCopyPrefix false state 8) := by
  intro address high below
  rw [cap_copy_byte_outside false state cursor address pointer aligned cursorBound
    (by omega) (Or.inl (by omega))]
  exact frame address high below

theorem cap_open_retained_read (floor : Nat) (reference state : MachineState)
    (address count : Nat) (high : 32768 ≤ address) (inside : address+count ≤ floor)
    (frame : CapOpenRetainedInputs floor reference state) :
    readBuffer state address count = readBuffer reference address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset member
  have bounded : offset < count := Finset.mem_range.mp member
  rw [frame (address+offset) (by omega) (by omega)]

end CommitGolfCandidate
