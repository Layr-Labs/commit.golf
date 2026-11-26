import CommitGolfCandidate.BatchUtilities
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

theorem patchedFetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 384) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (Late.Check.Normal.checkerImage.code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch Late.Check.Normal.checkerImage state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : Late.Check.Normal.checkerImage.code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded
end CommitGolfCandidate.PairCap
