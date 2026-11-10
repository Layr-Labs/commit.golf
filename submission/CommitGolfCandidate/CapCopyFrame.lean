import CommitGolfCandidate.CapCopyMemory
import CommitGolfCandidate.CapMarkInvariant

/-! Frames for cap boundary copies. Checker copies target the low root heap;
opening copies target proof output. The common outside-interval theorem
preserves only bytes outside that destination, rather than asserting that
opening leaves its high output unchanged. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_copy_byte_outside (checking : Bool) (state : MachineState)
    (destination address : Nat)
    (pointer : state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (aligned : destination % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (addressBound : address < 2^64)
    (outside : address < destination ∨ destination + 32 ≤ address) :
    (capDigestCopyPrefix checking state 8).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have decomposition : 8 * (address / 8) + address % 8 = address := by omega
  have memory :
      (capDigestCopyPrefix checking state 8).getMem
          (BitVec.ofNat 64 (8 * (address / 8))) =
        state.getMem (BitVec.ofNat 64 (8 * (address / 8))) := by
    apply cap_copy_memory_outside
    intro word equal
    rw [pointer, ← BitVec.ofNat_add] at equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : destination + 8 * word.val < 2^64)] at numeric
    omega
  conv_lhs => rw [← decomposition]
  conv_rhs => rw [← decomposition]
  rw [aligned_byte _ (address / 8) (address % 8) (by omega),
    aligned_byte _ (address / 8) (address % 8) (by omega)]
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), memory]

/-- Low destination copies preserve the full high ABI byte frame. -/
theorem cap_copy_high_bytes (checking : Bool) (state reference : MachineState)
    (destination : Nat)
    (pointer : state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (aligned : destination % 8 = 0) (low : destination + 32 ≤ 22528)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capDigestCopyPrefix checking state 8) reference := by
  intro address lower upper
  rw [cap_copy_byte_outside checking state destination address pointer aligned
    (by omega) upper (Or.inr (by omega))]
  exact frame address lower upper

/-- Copies disjoint from the mark region preserve every finalized mark word. -/
theorem cap_copy_marks (checking : Bool) (state : MachineState) (destination node : Nat)
    (pointer : state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (destinationBound : destination + 32 ≤ 2^64)
    (bounded : node < 256)
    (separate : destination + 32 ≤ 20480 ∨ 22528 ≤ destination) :
    (capDigestCopyPrefix checking state 8).getMem (capMarkAddress node) =
      state.getMem (capMarkAddress node) := by
  apply cap_copy_memory_outside
  intro word equal
  rw [pointer, ← BitVec.ofNat_add] at equal
  have numeric := congrArg BitVec.toNat equal
  simp only [capMarkAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 20480 + 8 * node < 2^64),
    Nat.mod_eq_of_lt (by omega : destination + 8 * word.val < 2^64)] at numeric
  omega

theorem cap_copy_marks_ready (checking : Bool) (state : MachineState) (destination : Nat)
    (marked : Nat → Bool)
    (pointer : state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (destinationBound : destination + 32 ≤ 2^64)
    (separate : destination + 32 ≤ 20480 ∨ 22528 ≤ destination)
    (ready : CapMarksReady state 128 0 marked) :
    CapMarksReady (capDigestCopyPrefix checking state 8) 128 0 marked := by
  intro node positive bounded
  rw [cap_copy_marks checking state destination node pointer destinationBound bounded separate]
  exact ready node positive bounded

end CommitGolfCandidate
