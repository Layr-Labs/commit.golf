import CommitGolfCandidate.PairRecordTail
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 300000

def storedAt (s : MachineState) (u : Fin 256) : Option Digest :=
  if s.getByte (BitVec.ofNat 64 (flag u.val)) = 0 then none else some (readBuffer s (cell u.val) 32)

private theorem cellBounds : ∀ u : Fin 256, 16384 ≤ cell u.val ∧ cell u.val+32≤32768 ∧ cell u.val%8=0 := by decide
private theorem flagBounds : ∀ u : Fin 256, (alignToDword (BitVec.ofNat 64 (flag u.val))).toNat <16384 := by decide

private theorem flagDisjoint (u v : Fin 256) (j : Fin 4) :
    alignToDword (BitVec.ofNat 64 (flag u.val)) ≠ BitVec.ofNat 64 (cell v.val) + BitVec.ofNat 64 (8*j.val) := by
  have b := cellBounds v; have low := flagBounds u
  rw [← BitVec.ofNat_add]
  intro eqn; have h := congrArg BitVec.toNat eqn
  have hj := j.isLt
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem cellSeparated (u v : Fin 256) (different : v ≠ u) :
    cell u.val+32 ≤ cell v.val ∨ cell v.val+32 ≤ cell u.val := by
  have ne : v.val ≠ u.val := fun h => different (Fin.ext h)
  unfold cell heapOffset
  omega

private theorem copyExcludesFlag (s : MachineState) (src : Word) (u v : Fin 256) :
    (copyAt s src (BitVec.ofNat 64 (cell u.val))).getByte (BitVec.ofNat 64 (flag v.val)) =
      s.getByte (BitVec.ofNat 64 (flag v.val)) := by
  apply congrArg (fun w => extractByte w (byteOffset (BitVec.ofNat 64 (flag v.val))))
  exact opening_copy_memory_outside _ _ (flagDisjoint v u)

private theorem byteWriteDisjoint (s : MachineState) (u v : Fin 256) :
    readBuffer (s.setByte (BitVec.ofNat 64 (flag u.val)) 1) (cell v.val) 32 =
      readBuffer s (cell v.val) 32 := by
  apply read_digest_congr _ _ _ (cellBounds v).2.2
  intro j hj
  have d := flagDisjoint u v ⟨j,hj⟩
  rw [← BitVec.ofNat_add] at d
  exact MachineState.getMem_setMem_ne (Ne.symm d)

theorem writeMap (s : MachineState) (u v : Fin 256)
    (sf : s.getReg .x22 = BitVec.ofNat 64 (flag u.val))
    (sn : s.getReg .x23 = BitVec.ofNat 64 (cell u.val)) (scratch : s.getReg .x21=256) :
    storedAt (storeState s) v =
      if v=u then some (readBuffer s 256 32) else storedAt s v := by
  let marked := s.setByte (BitVec.ofNat 64 (flag u.val)) 1
  have mem : (storeState s).mem=(copyAt marked 256 (BitVec.ofNat 64 (cell u.val))).mem := by
    rw [storeMemory,sf,sn,scratch]
  have flagged : (storeState s).getByte (BitVec.ofNat 64 (flag v.val)) =
      if v=u then 1 else s.getByte (BitVec.ofNat 64 (flag v.val)) := by
    have eqn : (storeState s).getByte (BitVec.ofNat 64 (flag v.val)) =
        (copyAt marked 256 (BitVec.ofNat 64 (cell u.val))).getByte (BitVec.ofNat 64 (flag v.val)) :=
      congrArg (fun (m : Word → Word) => extractByte (m (alignToDword (BitVec.ofNat 64 (flag v.val)))) (byteOffset (BitVec.ofNat 64 (flag v.val)))) mem
    rw [eqn,copyExcludesFlag,set_byte_read]
    congr 1
    apply propext
    constructor
    · intro e; apply Fin.ext
      have hn := congrArg BitVec.toNat e
      have bv := v.isLt; have bu := u.isLt
      simp only [BitVec.toNat_ofNat,flag,Nat.mod_eq_of_lt (by omega : 12288+v.val<2^64),
        Nat.mod_eq_of_lt (by omega : 12288+u.val<2^64)] at hn; omega
    · rintro rfl; rfl
  by_cases same : v=u
  · subst v
    rw [storedAt,flagged]
    simp [storedNode s u sf sn scratch]
  · have vv := cellBounds v; have uu := cellBounds u
    have kept : readBuffer (storeState s) (cell v.val) 32 = readBuffer s (cell v.val) 32 := by
      rw [read_buffer_memory_congr _ _ mem]
      apply (opening_copy_preserves_digest _ (cell u.val) (cell v.val) rfl vv.2.2 (by omega) (by omega)
        ((cellSeparated u v same).symm)).trans
      exact byteWriteDisjoint s u v
    simp only [storedAt,flagged,if_neg same,kept]

end CommitGolfCandidate.PairCap.Batch
