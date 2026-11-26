import CommitGolfCandidate.PairWriteStep
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4000
set_option maxHeartbeats 60000
attribute [local irreducible] headState Nat.iterate overrideState openingCopyState submission
theorem lowIndex (k : Nat) (h : k < 128) :
    (BitVec.ofNat 64 (indexBase+8*k)).toNat < outBase := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [indexBase]; omega : indexBase+8*k < 2^64)]
  dsimp [indexBase,outBase]; omega

theorem loadNext (idx : Nat → Nat) (bounds : ∀ k, idx k < 2^24) (s : MachineState)
    (n : Nat) (bn : n < 128) (f : Frame s (n+1))
    (loaded : ∀ k < n+1, s.getMem (BitVec.ofNat 64 (indexBase+8*k)) = BitVec.ofNat 64 (idx k))
    (k : Nat) (bk : k<n) :
    (overrideState s).getMem (BitVec.ofNat 64 (indexBase+8*k)) = BitVec.ofNat 64 (idx k) :=
  (belowWord s f (bounds n) (loaded n (Nat.lt_succ_self n))
    (BitVec.ofNat 64 (indexBase+8*k)) (lowIndex k (Nat.lt_trans bk bn))).trans
    (loaded k (Nat.lt_succ_of_lt bk))

theorem sweepBelow (idx : Nat → Nat) (bounds : ∀ k, idx k < 2^24) (n : Nat) (bn : n ≤ 128)
    (s : MachineState) (f : Frame s n)
    (loaded : ∀ k < n, s.getMem (BitVec.ofNat 64 (indexBase+8*k)) = BitVec.ofNat 64 (idx k))
    (addr : Word) (below : addr.toNat < outBase) :
    (overrideState^[n] s).getMem addr = s.getMem addr := by
  induction n generalizing s with
  | zero => simp only [Function.iterate_zero,id_eq,overrideSlot]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (by omega) (overrideState s) (oneFrame s f)
      (loadNext idx bounds s n (by omega) f loaded)).trans
      (belowWord s f (bounds n) (loaded n (Nat.lt_succ_self n)) addr below)


end CommitGolfCandidate.PairCap
