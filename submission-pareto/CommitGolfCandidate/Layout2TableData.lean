import CommitGolfCandidate.Layout2Invariant
import CommitGolfCandidate.Layout2TableBytes
import CommitGolfCandidate.TwoPermutationCheckLoader

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2Helpers (pget pget_get halfword_bytes half_ext)
set_option maxRecDepth 32000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
attribute [local irreducible] ArtifactEncoding.decode K1Artifact.checkData

theorem check_data_eq : (candidate.image .check).data=ArtifactEncoding.decode 8 K1Artifact.checkData := rfl

private theorem base_of_tree {n : Nat} (I : Image) (p : ArtifactEncoding.Packed n)
    (h : I.data=ArtifactEncoding.decode 8 p) : dataBase I = 16*((MEMORY_BYTES-n)/16) :=
  congrArg (fun l : Nat => 16*((MEMORY_BYTES-l)/16))
    ((congrArg List.length h).trans (ArtifactEncoding.length_decode 8 p))

theorem data_base : dataBase (candidate.image .check)=tableBase :=
  base_of_tree (candidate.image .check) K1Artifact.checkData check_data_eq

private theorem raw_get {n : Nat} (packed : ArtifactEncoding.Packed n) (data : List Byte)
    (eq : data=ArtifactEncoding.decode 8 packed) (k : Nat) (hk : k<n) :
    data[k]?.getD 0=BitVec.ofNat 8 (pget packed k) := by
  rw [eq,←List.getD_eq_getElem?_getD,ArtifactEncoding.getD_decode 8 packed k hk]
  apply BitVec.eq_of_toNat_eq
  rw [pget_get,BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by rw [←pget_get packed ⟨k,hk⟩];exact BitVec.isLt _)).symm

theorem raw_data_read (k : Nat) (hk : k<337472) :
    (candidate.image .check).data[k]?.getD 0=BitVec.ofNat 8 (pget K1Artifact.checkData k) :=
  raw_get K1Artifact.checkData _ check_data_eq k hk

theorem data_read {τ} (physical : ∀ k, k<85440 → pget K1Artifact.checkData k=tableByte τ k)
    (k : Nat) (inside : k<85440) :
    (candidate.image .check).data[k]?.getD 0=BitVec.ofNat 8 (tableByte τ k) :=
  (raw_data_read k (by omega)).trans (congrArg (BitVec.ofNat 8) (physical k inside))
end CommitGolfCandidate.Layout2
