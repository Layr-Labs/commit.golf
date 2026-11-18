-- Pair-heads copy of TwoPermutationPackedCapFetch (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckImage
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.TwoPermutationCheckerCompression

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

theorem cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 512) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (pairImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch pairImage state = some (.base instruction) :=
by
  have numeric : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases entry : pairImage.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

end TwoPermutationPrototype.PairCk.Packed.Checker
