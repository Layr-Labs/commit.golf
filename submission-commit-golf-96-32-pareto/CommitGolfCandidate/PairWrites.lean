import CommitGolfCandidate.PairBelow
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4000
set_option maxHeartbeats 120000
attribute [local irreducible] Nat.iterate overrideState readBuffer childAddress

private theorem slotIteration {α β : Type} (step : α → α) (view : α → β) (inv : Nat → α → Prop)
    (bucket : Nat → Nat) (value : Nat → β) (p : Nat)
    (pres : ∀ n s, inv (n+1) s → inv n (step s))
    (update : ∀ n s, inv (n+1) s → view (step s) = if bucket n = p then value n else view s)
    (n : Nat) (s : α) (ok : inv n s) :
    view (step^[n] s) = overrideSlot bucket value p n (view s) := by
  induction n generalizing s with
  | zero => simp only [Function.iterate_zero,id_eq,overrideSlot]
  | succ k ih =>
    rw [Function.iterate_succ_apply,ih (step s) (pres k s ok), update k s ok]
    rfl

private abbrev hashAt (s : MachineState) (a : Nat) := readBuffer s a 32

private structure Seen (indices : Nat → Nat) (children : Nat → Digest) (n : Nat) (s : MachineState) : Prop where
  bound : n ≤ 128
  frame : Frame s n
  idx : ∀ k < n, s.getMem (BitVec.ofNat 64 (indexBase+8*k)) = BitVec.ofNat 64 (indices k)
  child : ∀ k, hashAt s (childAddress (indices k/65536)) = children k

private theorem copyLow (s : MachineState) {n i : Nat} (f : Frame s (n+1)) (bi : i<2^24)
    (load : s.getMem (BitVec.ofNat 64 (indexBase+8*n)) = BitVec.ofNat 64 i)
    (a : Nat) (align : a%8=0) (low : a+32 ≤ outBase) :
    hashAt (overrideState s) a = hashAt s a := by
  apply read_digest_congr _ _ a align
  intro j h
  have small : a+8*j < 2^64 := by change a+32 ≤ 10871707680 at low; omega
  apply belowWord s f bi load (BitVec.ofNat 64 (a+8*j))
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  omega

private theorem seenNext (idx : Nat → Nat) (bounds : ∀ k, idx k < 2^24) (child : Nat → Digest)
    (n : Nat) (s : MachineState) (seen : Seen idx child (n+1) s) :
    Seen idx child n (overrideState s) := by
  have b := seen.bound
  refine ⟨by omega, oneFrame s seen.frame, loadNext idx bounds s n (by omega) seen.frame seen.idx, ?_⟩
  intro k
  have size := bounds k
  have c : childAddress (idx k/65536) % 8 = 0 ∧ childAddress (idx k/65536)+32 ≤ outBase :=
    childBounds ⟨idx k/65536,by omega⟩
  exact (copyLow s seen.frame (bounds n) (seen.idx n (Nat.lt_succ_self n)) _ c.1 c.2).trans (seen.child k)

theorem sweepSlot (idx : Nat → Nat) (bounds : ∀ k, idx k < 2^24) (n : Nat) (bn : n ≤ 128)
    (s : MachineState) (f : Frame s n)
    (loaded : ∀ k < n, s.getMem (BitVec.ofNat 64 (indexBase+8*k)) = BitVec.ofNat 64 (idx k))
    (p : Nat) (bp : p < 128) :
    readBuffer (overrideState^[n] s) (outBase+32*p) 32 =
      overrideSlot (fun k => idx k/131072) (fun k => readBuffer s (childAddress (idx k/65536)) 32)
        p n (readBuffer s (outBase+32*p) 32) := by
  let child := fun k => hashAt s (childAddress (idx k/65536))
  let view := fun st => hashAt st (outBase+32*p)
  apply slotIteration overrideState view (Seen idx child) (fun k => idx k/131072) child p (seenNext idx bounds child)
  · intro k st good
    have w := oneSlot st good.frame (bounds k) (good.idx k (Nat.lt_succ_self k)) p bp
    change hashAt (overrideState st) (outBase+32*p) = if idx k/131072 = p then child k else hashAt st (outBase+32*p)
    exact w.trans (congrArg (fun d => if idx k/131072 = p then d else hashAt st (outBase+32*p)) (good.child k))
  · exact ⟨bn,f,loaded,fun _ => rfl⟩

theorem setupMem (s : MachineState) : (setupState (jumpState s)).mem = s.mem := rfl
theorem finishMem (s : MachineState) : (finishState s).mem = s.mem := rfl
end CommitGolfCandidate.PairCap
