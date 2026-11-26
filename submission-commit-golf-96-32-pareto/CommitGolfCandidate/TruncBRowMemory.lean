import CommitGolfCandidate.TruncBCopiedWord
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 90000
attribute [local irreducible] readBuffer copyAt storedAt nextEdge storeState

theorem copyHigh (s : MachineState) (pc : s.pc=5120) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val)
    (w : Word) (high : 32768≤w.toNat) : (copied s).getMem w=s.getMem w := by
  apply copiedWord s pc u idx
  · have b : ∀ u : Fin 256, (alignToDword (BitVec.ofNat 64 (flag u.val))).toNat < 32768 := by decide
    intro e;rw [e] at high;exact (Nat.not_lt_of_ge high) (b u)
  · intro j e
    have b : ∀ u : Fin 256, cell u.val+32≤32768 := by decide
    have c:=b u;have hj:=j.isLt
    rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at high;omega

theorem copyGap (s : MachineState) (pc : s.pc=5120) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val) (p : Fin 128) :
    readBuffer (copied s) (16384+96*p.val+64) 32=readBuffer s (16384+96*p.val+64) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro j hj;apply copiedWord s pc u idx
  · have b : ∀ u : Fin 256, (alignToDword (BitVec.ofNat 64 (flag u.val))).toNat < 16384 := by decide
    intro e;have h := congrArg BitVec.toNat e;have hp:=p.isLt;have hh:=b u
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h;omega
  · intro k e
    have h := congrArg BitVec.toNat e; have hu:=u.isLt;have hp:=p.isLt;have hk:=k.isLt
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 16384+96*p.val+64+8*j<2^64),
      Nat.mod_eq_of_lt (by unfold cell heapOffset;omega : cell u.val+8*k.val<2^64)] at h
    unfold cell heapOffset at h
    by_cases c : u.val/2=p.val
    · omega
    · rcases Nat.lt_or_gt_of_ne c with lo|hi <;> omega
end CommitGolfCandidate.Trunc.Batch
