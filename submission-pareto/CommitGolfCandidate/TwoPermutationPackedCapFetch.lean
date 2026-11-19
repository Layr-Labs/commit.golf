import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.TwoPermutationCheckerCompression

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

/-- Fetch from the checker image at any word position used by the cap (the T238 blocks sit at 628..704). -/
theorem cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 1024) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch packedImage state = some (.base instruction) :=
  wide_image_fetch packedImage state index instruction (by omega) pc decoded

end TwoPermutationPrototype.Packed.Checker
