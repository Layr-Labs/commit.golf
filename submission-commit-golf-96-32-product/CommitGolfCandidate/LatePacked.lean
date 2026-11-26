import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.LateCalls

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem packed_lookup {count : Nat} (a : ArtifactEncoding.Packed count) (n : Nat) (h : n < count) :
    (ArtifactEncoding.decode 32 a)[n]? = some (a.get 32 ⟨n,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]

attribute [local irreducible] ArtifactEncoding.decode Artifact.commitCode

theorem commit_packed_word (n : Nat) (small : n < 3262) :
    commitImage.code[n]? = some (Artifact.commitCode.get 32 ⟨n,small⟩) := by
  rw [←commit_image_matches]
  exact packed_lookup Artifact.commitCode n small

def packedWord (n : Nat) : BitVec 32 :=
  if h : n < 3262 then Artifact.commitCode.get 32 ⟨n,h⟩ else 0

private theorem fetchCommitWord {s : MachineState} {i : Nat} (ip : s.pc = pcAt i)
    (small : i < 4096) {w : BitVec 32} (atWord : commitImage.code[i]? = some w) :
    fetch commitImage s = decodeInstruction w := by
  have bound : 4096 + 4*i < 2^64 := by omega
  simp only [fetch, ip, pcAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rw [if_pos (by constructor <;> omega)]
  simpa only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by decide : 0 < 4), atWord]

theorem decoded_word (n : Nat) (small : n < 3262) (op : Instr)
    (ok : decodeInstruction (packedWord n) = some (.base op)) : AtWord n op := by
  intro s pc
  have eq : commitImage.code[n]? = some (packedWord n) := by simp only [packedWord,dif_pos small,commit_packed_word n small]
  exact (fetchCommitWord pc (by omega) eq).trans ok

end CommitGolfCandidate.Late
