import CommitGolf.ArtifactEncoding
import CommitGolf.Riscv

namespace CommitGolfCandidate.Reconstruction
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Fetch through the verifier's balanced image tree without reducing a materialized code list. -/
theorem fetch_packed {n : Nat} (image : Image) (packed : ArtifactEncoding.Packed n)
    (code : image.code = ArtifactEncoding.decode 32 packed) (i : Nat) (inside : i < n)
    (fits : 4096 + 4*i < 2^64) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096 + 4*i)) :
    fetch image s = decodeInstruction (packed.get 32 ⟨i, inside⟩) := by
  have hn : s.pc.toNat = 4096+4*i := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  have len : i < (ArtifactEncoding.decode 32 packed).length := by
    rwa [ArtifactEncoding.length_decode]
  have word := ArtifactEncoding.getD_decode 32 packed i inside
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem len] at word
  rw [fetch, hn, ite_eq_left (by omega), show (4096+4*i-4096)/4=i by omega, code,
    List.getElem?_eq_getElem len]
  exact congrArg decodeInstruction word

end CommitGolfCandidate.Reconstruction
