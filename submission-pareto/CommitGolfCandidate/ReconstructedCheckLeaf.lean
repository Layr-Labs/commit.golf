import CommitGolfCandidate.ReconstructedCheckLeafWords

namespace CommitGolfCandidate.Reconstruction.CheckLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded CheckLeafPlan CheckLeafCall CheckLeafWords
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 23000
set_option maxHeartbeats 1300000
set_option exponentiation.threshold 2048
attribute [local irreducible] CheckLeafPlan.start CheckLeafPlan.first CheckLeafPlan.second CheckLeafPlan.third

private theorem get_state {α} (x : Option α) (default : α) (h : x.isSome=true) : x=some (x.getD default) := by
  cases x <;> simp_all

def rows (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32) :=
  [row o (request o idx n msg 0),row o (request o idx n msg 1)]

/-- At the first path-loop instruction the checker holds the low three doublewords
and the low 48 bits of the fourth doubleword of the second permutation answer. -/
theorem positive (o : Oracle) (env : Env) (layout : Layout env table) (idx : Index) (n : Words 2) (msg : Words 32)
    (params : Params o env idx n msg) (s : MachineState) (initial : Matches env start s) :
    ∃ t, Segment o 196 s t (rows o idx n msg) ∧ t.pc=CommitBlocks.addr 238 ∧ Matches env third.state t ∧
      Safe table third.state.writes ∧
      let leaf := leafDigestW 240 (o.permutation (request o idx n msg 1))
      t.getReg .x12=leaf.extractLsb' 0 64 ∧ t.getReg .x13=leaf.extractLsb' 64 64 ∧
      t.getReg .x14=leaf.extractLsb' 128 64 ∧ t.getReg .x11=leaf.extractLsb' 192 64 := by
  have run := CheckProgram.sound o env table layout CheckLeafImage.lookup CheckLeafImage.decoded
  have safe0 : Safe table start.writes := by unfold start;intro a h;cases h
  obtain ⟨a,one,ma,sa,pc₁⟩ := run (CommitBlocks.addr 213) 185 start s initial safe0 first
    (by unfold first;exact get_state firstRun ⟨0,start⟩ firstReceipt.1)
  obtain ⟨b,two,mb,sb⟩ := call_step o env layout idx n msg params 0 (by decide) 4 first.state a ma sa pc₁ firstReceipt.2.2
  obtain ⟨c,three,mc,sc,pc₂⟩ := run (CommitBlocks.addr 231) 23 (modelCall 0 first.state) b mb sb second
    (by unfold second;exact get_state secondRun ⟨0,start⟩ secondReceipt.1)
  obtain ⟨u,four,mu,su⟩ := call_step o env layout idx n msg params 1 (by decide) 5 second.state c mc sc pc₂ secondReceipt.2.2
  obtain ⟨t,five,mt,st,last⟩ := run (CommitBlocks.addr 238) 10 (modelCall 1 second.state) u mu su third
    (by unfold third;exact get_state thirdRun ⟨0,start⟩ thirdReceipt.1)
  have all := compose (compose (compose (compose one two) three) four) five
  rw [firstReceipt.2.1,secondReceipt.2.1,thirdReceipt.2.1] at all
  refine ⟨t,all,last,mt,st,?_⟩
  obtain ⟨lo,mid,hi,top,_⟩:=thirdReceipt.2.2
  rw [mt.regs .x12,mt.regs .x13,mt.regs .x14,mt.regs .x11,lo,mid,hi,top]
  exact ⟨digest o env idx n msg params.answers 0,digest o env idx n msg params.answers 1,
    digest o env idx n msg params.answers 2,digest o env idx n msg params.answers 3⟩

end CommitGolfCandidate.Reconstruction.CheckLeaf
