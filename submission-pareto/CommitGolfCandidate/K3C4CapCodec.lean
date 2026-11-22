import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.K3T238PackDecode

/-! # The packed cap frontier (T238)

Every cap frontier node is 238 bits. The frontier is read in depth-first order; each full group of eight
consecutive nodes takes 238 bytes: slots `j = 0..6` are 30 bytes holding node `j` in bits `0..237` and bits
`2j, 2j+1` of node 7's top 14 bits in bits `238, 239`; node 7's low 224 bits follow in 28 bytes. A trailing partial
group is plain 30-byte slots. Frontier node `k` therefore starts `capPackedBytes k` bytes into the frontier. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

/-- Bytes taken by the first `k` frontier nodes. -/
def capPackedBytes (k : Nat) : Nat := 238*(k/8) + 30*(k%8)

/-- Frontier node `k` of the packed frontier starting at byte `start`. -/
def capFrontierValue (state : MachineState) (start k : Nat) : Digest :=
  packedNodeAt state (start+238*(k/8)) (k%8)

/-- Bytes the checker reads for frontier node `k`: 28 for the last node of a group, else 30. -/
def capSlotBytes (k : Nat) : Nat := if k%8 = 7 then 28 else 30

theorem cap_packed_bytes_succ (k : Nat) : capPackedBytes (k+1) = capPackedBytes k + capSlotBytes k := by
  unfold capPackedBytes capSlotBytes
  split <;> omega

theorem cap_packed_bytes_zero : capPackedBytes 0 = 0 := rfl

theorem cap_packed_bytes_mono {a b : Nat} (order : a ≤ b) : capPackedBytes a ≤ capPackedBytes b := by
  unfold capPackedBytes
  omega

theorem cap_packed_bytes_even (k : Nat) : capPackedBytes k % 2 = 0 := by
  unfold capPackedBytes
  omega

theorem cap_packed_bytes_closed (k : Nat) : capPackedBytes k = 30*k - 2*(k/8) := by
  unfold capPackedBytes
  omega

theorem cap_packed_bytes_le (k : Nat) : capPackedBytes k ≤ 30*k := by
  unfold capPackedBytes
  omega

theorem cap_slot_bytes_le (k : Nat) : capSlotBytes k ≤ 30 := by
  unfold capSlotBytes
  split <;> omega

/-- The position of node `k` inside its block. -/
theorem cap_packed_bytes_block (k : Nat) : capPackedBytes k = 238*(k/8) + 30*(k%8) := rfl

private theorem read_above (before after : MachineState) (address count : Nat)
    (above : 32768 ≤ address) (fits : address+count ≤ 2^64)
    (frame : ∀ q, 4096 ≤ q → q < 2^61 → memoryView after q = memoryView before q) :
    readBuffer after address count = readBuffer before address count :=
  read_buffer_above before after address count 4096 (by omega) fits frame

/-- A frontier node depends only on memory. -/
theorem cap_frontier_value_mem {before after : MachineState} (same : after.mem = before.mem) (start k : Nat) :
    capFrontierValue after start k = capFrontierValue before start k := by
  have reads (a n : Nat) : readBuffer after a n = readBuffer before a n := by
    unfold readBuffer
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [MachineState.getByte, MachineState.getMem, same]
  unfold capFrontierValue packedNodeAt packedSpareAt
  rw [reads, reads, reads, reads, reads, reads, reads, reads, reads]

/-- A packed node depends only on memory above word 4096. -/
theorem cap_node_frame (before after : MachineState) (base k : Nat) (small : k < 8)
    (above : 32768 ≤ base) (fits : base+238 ≤ 2^64)
    (frame : ∀ q, 4096 ≤ q → q < 2^61 → memoryView after q = memoryView before q) :
    packedNodeAt after base k = packedNodeAt before base k := by
  have spare (j : Nat) (small : 30*j+30 ≤ 238) : packedSpareAt after (base+30*j) = packedSpareAt before (base+30*j) := by
    unfold packedSpareAt
    rw [read_above before after _ 30 (by omega) (by omega) frame]
  unfold packedNodeAt
  split
  · have s0 := spare 0 (by decide)
    have s1 := spare 1 (by decide)
    have s2 := spare 2 (by decide)
    have s3 := spare 3 (by decide)
    have s4 := spare 4 (by decide)
    have s5 := spare 5 (by decide)
    have s6 := spare 6 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at s0 s1 s2 s3 s4 s5 s6
    rw [s0, s1, s2, s3, s4, s5, s6, read_above before after _ 28 (by omega) (by omega) frame]
  · rw [read_above before after _ 30 (by omega) (by omega) frame]

/-- A frontier node depends only on memory above word 4096. -/
theorem cap_frontier_value_frame (before after : MachineState) (start k : Nat)
    (above : 32768 ≤ start) (fits : start+capPackedBytes k+238 ≤ 2^64)
    (frame : ∀ q, 4096 ≤ q → q < 2^61 → memoryView after q = memoryView before q) :
    capFrontierValue after start k = capFrontierValue before start k := by
  unfold capFrontierValue
  apply cap_node_frame before after _ _ (Nat.mod_lt _ (by decide)) (by omega) _ frame
  unfold capPackedBytes at fits
  omega

end TwoPermutationPrototype.Packed.Checker
