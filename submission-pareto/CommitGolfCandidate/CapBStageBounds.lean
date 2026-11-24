import CommitGolfCandidate.CapBResult
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening.CapB (handlers flushPrice)
open TwoPermutationPrototype.Sampling
theorem bill_127 {gs : List Nat} (f : (capFrontierNodes gs 1 8).length=127) : bill gs 128≤3366 := by
  have h:=TwoPermutationPrototype.GroupedOpening.CapB.control_bound gs 1 5
  change TwoPermutationPrototype.GroupedOpening.CapB.control gs 1 5≤850+2*(capFrontierNodes gs 1 8).length at h
  rw [f] at h
  have bound:=TwoPermutationPrototype.GroupedOpening.CapB.last_two.1
  unfold bill TwoPermutationPrototype.GroupedOpening.CapB.price
  rw [f];dsimp only;rw [if_pos (by decide : 128%4=0)]
  omega
end CommitGolfCandidate.CapB
