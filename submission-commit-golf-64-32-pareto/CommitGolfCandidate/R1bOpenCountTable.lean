import CommitGolfCandidate.R1bOpenCountSites
import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves
namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate R1b.Machine
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local irreducible] ArtifactEncoding.decode
private theorem keepsAll (s : MachineState) : keepsCount (fetch openingImage s) := by
  rw [←delivered_opening_image]
  let i:=(s.pc.toNat-4096)/4
  by_cases valid : 4096≤s.pc.toNat ∧ s.pc.toNat%4=0
  · by_cases bound : i<12626
    · have pc : s.pc=R1bPC.pcAt i := by
        rw [←BitVec.toNat_inj];unfold R1bPC.pcAt
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096+4*i<2^64 by omega)]
        dsimp only [i];omega
      rw [show fetch (Artifact.submission.image .opening) s=_ from fetched .opening i bound s pc]
      exact countAt _ bound
    · have size : (Artifact.submission.image .opening).code.length=12626 := by
        change (ArtifactEncoding.decode 32 Artifact.openingCode).length=12626
        exact ArtifactEncoding.length_decode 32 Artifact.openingCode
      have miss : (Artifact.submission.image .opening).code[(s.pc.toNat-4096)/4]?=none :=
        List.getElem?_eq_none (show (Artifact.submission.image .opening).code.length ≤ i by omega)
      rw [fetch,if_pos valid,miss] <;> rfl
  · simp [fetch,valid,keepsCount]

theorem RunsOpeningBlock.count {s t : MachineState} {n : Nat} (run : RunsOpeningBlock s t n) :
    t.getReg .x16=s.getReg .x16 := by
  have ev:=run 0 false
  have hit : (⟨.unfinished,t,n,0⟩ : Execution) ∈ support (execute openingImage n s false) := by
    simpa only [Nat.add_zero,execute,pure_bind,Execution.charge,Nat.zero_add] using
      (show (⟨.unfinished,t,n,0⟩ : Execution) ∈ support (execute openingImage (n+0) s false) by
        rw [ev];simp [execute,Execution.charge])
  exact countRun openingImage keepsAll n s hit
end TwoPermutationPrototype.PackedOpening
