import CommitGolfCandidate.CapBoundaryPrepare
import CommitGolfCandidate.CapCopyFrame
import CommitGolfCandidate.CapAdvanceGuard

/-! A boundary root address, four-word copy and proof-cursor increment form an
eleven-instruction macro. Runtime admission includes the real cursor and root
access bounds. The checker's earlier proof-end guard is a separate boundary. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capBoundaryCopied (checking : Bool) (state : MachineState) : MachineState :=
  capDigestCopyPrefix checking (capBoundaryPrefix checking state 2) 8
def capBoundaryState (checking : Bool) (state : MachineState) : MachineState :=
  execInstrBr (capBoundaryCopied checking state) (.ADDI .x25 .x25 32)

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_boundary_copy_access (checking : Bool) (state : MachineState)
    (node rootBase cursor : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (rootBound : rootBase + 32 * node + 32 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (aligned : cursor % 8 = 0) :
    (∀ word : Fin 4,
      accessValid ((capBoundaryPrefix checking state 2).getReg (capCopySource checking) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true) ∧
    (∀ word : Fin 4,
      accessValid ((capBoundaryPrefix checking state 2).getReg (capCopyDestination checking) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true) := by
  have root := cap_boundary_address checking state node rootBase base index
  have proofPointer : (capBoundaryPrefix checking state 2).getReg .x25 =
      BitVec.ofNat 64 cursor :=
    (cap_boundary_prefix_register checking state 2 (by decide) .x25 (by decide)).trans proof
  have rootAccess : ∀ word : Fin 4,
      accessValid (BitVec.ofNat 64 (rootBase + 32 * node) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    have small : rootBase + 32 * node < 2^64 := by
      simp only [MEMORY_BYTES] at rootBound
      omega
    apply opening_digest_access_valid
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using rootBound
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      omega
  have proofAccess : ∀ word : Fin 4,
      accessValid (BitVec.ofNat 64 cursor + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    apply opening_digest_access_valid
    · have small : cursor < 2^64 := by simp only [MEMORY_BYTES] at cursorBound; omega
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using cursorBound
    · have small : cursor < 2^64 := by simp only [MEMORY_BYTES] at cursorBound; omega
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using aligned
  cases checking <;> simp only [capCopySource, capCopyDestination, ↓reduceIte,
    Bool.false_eq_true, root, proofPointer]
  · exact ⟨rootAccess, proofAccess⟩
  · exact ⟨proofAccess, rootAccess⟩

theorem cap_boundary_copy_execute (checking : Bool) (state : MachineState)
    (node rootBase cursor : Nat) (pc : state.pc = capBoundaryEntry checking)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (rootBound : rootBase + 32 * node + 32 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (aligned : cursor % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (11 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capBoundaryState checking state) allowCoins
          return result.charge 11 0) := by
  have accesses := cap_boundary_copy_access checking state node rootBase cursor base index
    rootBound rootAligned proof cursorBound aligned
  have copyPC : (capBoundaryPrefix checking state 2).pc =
      if checking then 4652 else 4460 := by
    rw [cap_boundary_prefix_pc checking state 2 (by decide), pc]
    cases checking <;> rfl
  have fetched : CapDigestCopyFetched (capWalkImage checking) checking
      (if checking then 4652 else 4460) := by
    cases checking
    · exact cap_open_boundary_copy_fetched
    · exact cap_check_boundary_copy_fetched
  have increment : fetch (capWalkImage checking) (capBoundaryCopied checking state) =
      some (.base (.ADDI .x25 .x25 32)) := by
    cases checking
    · apply cap_image_fetch _ _ 99 _ (by decide)
      · rw [capBoundaryCopied, cap_copy_prefix_pc false _ 8 (by decide), copyPC]
        rfl
      · rfl
    · apply cap_image_fetch _ _ 147 _ (by decide)
      · rw [capBoundaryCopied, cap_copy_prefix_pc true _ 8 (by decide), copyPC]
        rfl
      · rfl
  have tail : execute (capWalkImage checking) (1 + fuel) (capBoundaryCopied checking state)
        allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capBoundaryState checking state) allowCoins
          return result.charge 1 0) := by
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ increment (by rfl)]
    rfl
  unfold capBoundaryCopied at tail
  rw [show 11 + fuel = 2 + (8 + (1 + fuel)) by omega,
    cap_boundary_prepare_execute checking state pc,
    cap_digest_copy_execute _ _ _ fetched _ copyPC accesses.1 accesses.2,
    tail]
  simp only [bind_assoc, pure_bind, charge_pair]

/-- The checker uses the reserved low root heap. Opening instead supplies its
admitted trapdoor base to the generic theorem above. -/
theorem cap_check_boundary_copy_execute (state : MachineState)
    (node cursor : Nat) (pc : state.pc = capBoundaryEntry true)
    (base : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 256)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (aligned : cursor % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (11 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage true) fuel
            (capBoundaryState true state) allowCoins
          return result.charge 11 0) := by
  apply cap_boundary_copy_execute true state node 12288 cursor pc base index
  · simp only [MEMORY_BYTES]
    omega
  · decide
  · exact proof
  · exact cursorBound
  · exact aligned

theorem cap_boundary_state_pc (checking : Bool) (state : MachineState)
    (pc : state.pc = capBoundaryEntry checking) :
    (capBoundaryState checking state).pc = capAdvanceEntry checking := by
  change (capBoundaryCopied checking state).pc + 4 = _
  rw [capBoundaryCopied, cap_copy_prefix_pc checking _ 8 (by decide),
    cap_boundary_prefix_pc checking state 2 (by decide), pc]
  cases checking <;> rfl

theorem cap_boundary_state_cursor (checking : Bool) (state : MachineState) (cursor : Nat)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor) :
    (capBoundaryState checking state).getReg .x25 = BitVec.ofNat 64 (cursor + 32) := by
  simp (disch := decide) only [capBoundaryState, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]
  rw [capBoundaryCopied, cap_copy_prefix_register checking _ 8 (by decide) .x25 (by decide),
    cap_boundary_prefix_register checking state 2 (by decide) .x25 (by decide), proof]
  exact (BitVec.ofNat_add cursor 32).symm

theorem cap_boundary_state_register (checking : Bool) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x25) :
    (capBoundaryState checking state).getReg reg = state.getReg reg := by
  simp only [capBoundaryState, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2)]
  rw [capBoundaryCopied, cap_copy_prefix_register checking _ 8 (by decide) reg outside.1]
  exact cap_boundary_prefix_register checking state 2 (by decide) reg
    ⟨outside.2.1, outside.2.2.1⟩

end CommitGolfCandidate
