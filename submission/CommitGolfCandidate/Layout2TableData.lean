import CommitGolfCandidate.Layout2Invariant
import CommitGolfCandidate.Layout2TableBytes
import CommitGolfCandidate.TwoPermutationCheckLoader

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (pget pget_get halfword_bytes half_ext)
set_option maxRecDepth 32000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
private theorem check_data_eq : (candidate.image .check).data=ArtifactEncoding.decode 8 K1Artifact.checkData := by
  dsimp only [candidate,K1Artifact.submission]

theorem data_base : dataBase (candidate.image .check)=tableBase := by
  unfold dataBase;rw [check_data_eq,ArtifactEncoding.length_decode];decide

theorem data_read {τ} (physical : ∀ k, k<85440 → pget K1Artifact.checkData k=tableByte τ k)
    (k : Nat) (inside : k<85440) :
    (candidate.image .check).data[k]?.getD 0=BitVec.ofNat 8 (tableByte τ k) := by
  rw [←List.getD_eq_getElem?_getD,check_data_eq,ArtifactEncoding.getD_decode 8 _ k inside]
  apply BitVec.eq_of_toNat_eq
  rw [pget_get,physical k inside,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  unfold tableByte
  split <;> exact Nat.mod_lt _ (by decide)

end CommitGolfCandidate.Layout2
