import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.LateCalls

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem packed_lookup {count : Nat} (a : ArtifactEncoding.Packed count) (n : Nat) (h : n < count) :
    (ArtifactEncoding.decode 32 a)[n]? = some (a.get 32 ⟨n,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]

attribute [local irreducible] ArtifactEncoding.decode Artifact.commitCode

theorem commit_packed_word (n : Nat) (small : n < 3796) :
    commitImage.code[n]? = some (Artifact.commitCode.get 32 ⟨n,small⟩) := by
  rw [←commit_image_matches]
  exact packed_lookup Artifact.commitCode n small

def packedWord (n : Nat) : BitVec 32 :=
  if h : n < 3796 then Artifact.commitCode.get 32 ⟨n,h⟩ else 0

theorem decoded_word (n : Nat) (small : n < 3796) (op : Instr)
    (ok : decodeInstruction (packedWord n) = some (.base op)) : AtWord n op := by
  intro s pc
  have eq : commitImage.code[n]? = some (packedWord n) := by simp only [packedWord,dif_pos small,commit_packed_word n small]
  exact (fetch_word pc (by omega) eq).trans ok

end CommitGolfCandidate.Late
