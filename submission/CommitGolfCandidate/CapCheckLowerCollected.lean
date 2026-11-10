import CommitGolfCandidate.CapCheckLowerRecordFrame
import CommitGolfCandidate.CapCheckCollected

/-! The 25 paid lower-record queries cannot alter any collected cap leaf or
occupancy entry. This invariant holds on every supported reply continuation,
including replies inconsistent with the fixed-oracle digest semantics. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem word_outside_scratch (address : Nat) (above : 320 ≤ address)
    (small : address < 2^64) :
    ∀ i < 8, BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (256+8*i) := by
  intro i inside equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : 256+8*i<2^64)] at numeric
  omega

theorem cap_check_lower_record_collected (state finished : MachineState)
    (scratch : state.getReg .x21=256)
    (reachable : finished ∈ support (capCheckLowerRecord state))
    (roots : CapRootMap) (ready : CapCheckCollected state roots) :
    CapCheckCollected finished roots := by
  constructor
  · intro group bounded
    have same := cap_check_lower_record_word_frame state finished scratch reachable
      (capMarkAddress (128+group))
      (word_outside_scratch _ (by omega) (by omega))
    exact same.trans (ready.marks group bounded)
  · intro group bounded value known
    apply (read_digest_congr finished state (capCheckRootAddress group)
      (by unfold capCheckRootAddress; omega) _).trans (ready.roots group bounded value known)
    intro word inside
    apply cap_check_lower_record_word_frame state finished scratch reachable
    exact word_outside_scratch _ (by unfold capCheckRootAddress; omega)
      (by unfold capCheckRootAddress; omega)

end CommitGolfCandidate
