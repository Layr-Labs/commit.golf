import CommitGolfCandidate.TwoPermutationPackedLeafFetch

namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def wideOps : List Instr := [.ECALL,.SH .x12 .x0 30,.ADDI .x10 .x10 4032,.ADDI .x12 .x12 4064]
def narrowOps : List Instr := [.ECALL,.LHU .x7 .x12 28,.AND .x7 .x7 .x6,.SW .x12 .x7 28,
  .ADDI .x10 .x10 4032,.ADDI .x12 .x12 4064]

def blockOK (n : Nat) (narrow : Bool) : Prop :=
  let ops := if narrow then narrowOps else wideOps
  let start := if narrow then 4125 else 26
  ∀ j : Fin 64, ∀ k : Fin ops.length,
    Manifest.decodeBase (packed_wideCodeWord (start+ops.length*(64*n+j.val)+k.val))=some ops[k.val]

private theorem blockfalse0 : blockOK 0 false := by unfold blockOK; decide +kernel
private theorem blockfalse1 : blockOK 1 false := by unfold blockOK; decide +kernel
private theorem blockfalse2 : blockOK 2 false := by unfold blockOK; decide +kernel
private theorem blockfalse3 : blockOK 3 false := by unfold blockOK; decide +kernel
private theorem blockfalse4 : blockOK 4 false := by unfold blockOK; decide +kernel
private theorem blockfalse5 : blockOK 5 false := by unfold blockOK; decide +kernel
private theorem blockfalse6 : blockOK 6 false := by unfold blockOK; decide +kernel
private theorem blockfalse7 : blockOK 7 false := by unfold blockOK; decide +kernel
private theorem blockfalse8 : blockOK 8 false := by unfold blockOK; decide +kernel
private theorem blockfalse9 : blockOK 9 false := by unfold blockOK; decide +kernel
private theorem blockfalse10 : blockOK 10 false := by unfold blockOK; decide +kernel
private theorem blockfalse11 : blockOK 11 false := by unfold blockOK; decide +kernel
private theorem blockfalse12 : blockOK 12 false := by unfold blockOK; decide +kernel
private theorem blockfalse13 : blockOK 13 false := by unfold blockOK; decide +kernel
private theorem blockfalse14 : blockOK 14 false := by unfold blockOK; decide +kernel
private theorem blockfalse15 : blockOK 15 false := by unfold blockOK; decide +kernel
private theorem blocktrue0 : blockOK 0 true := by unfold blockOK; decide +kernel
private theorem blocktrue1 : blockOK 1 true := by unfold blockOK; decide +kernel
private theorem blocktrue2 : blockOK 2 true := by unfold blockOK; decide +kernel
private theorem blocktrue3 : blockOK 3 true := by unfold blockOK; decide +kernel
private theorem blocktrue4 : blockOK 4 true := by unfold blockOK; decide +kernel
private theorem blocktrue5 : blockOK 5 true := by unfold blockOK; decide +kernel
private theorem blocktrue6 : blockOK 6 true := by unfold blockOK; decide +kernel
private theorem blocktrue7 : blockOK 7 true := by unfold blockOK; decide +kernel
private theorem blocktrue8 : blockOK 8 true := by unfold blockOK; decide +kernel
private theorem blocktrue9 : blockOK 9 true := by unfold blockOK; decide +kernel
private theorem blocktrue10 : blockOK 10 true := by unfold blockOK; decide +kernel
private theorem blocktrue11 : blockOK 11 true := by unfold blockOK; decide +kernel
private theorem blocktrue12 : blockOK 12 true := by unfold blockOK; decide +kernel
private theorem blocktrue13 : blockOK 13 true := by unfold blockOK; decide +kernel
private theorem blocktrue14 : blockOK 14 true := by unfold blockOK; decide +kernel
private theorem blocktrue15 : blockOK 15 true := by unfold blockOK; decide +kernel

theorem decodedBlock (n : Nat) (h : n<16) (narrow : Bool) : blockOK n narrow := by
  cases narrow <;> interval_cases n
  · exact blockfalse0
  · exact blockfalse1
  · exact blockfalse2
  · exact blockfalse3
  · exact blockfalse4
  · exact blockfalse5
  · exact blockfalse6
  · exact blockfalse7
  · exact blockfalse8
  · exact blockfalse9
  · exact blockfalse10
  · exact blockfalse11
  · exact blockfalse12
  · exact blockfalse13
  · exact blockfalse14
  · exact blockfalse15
  · exact blocktrue0
  · exact blocktrue1
  · exact blocktrue2
  · exact blocktrue3
  · exact blocktrue4
  · exact blocktrue5
  · exact blocktrue6
  · exact blocktrue7
  · exact blocktrue8
  · exact blocktrue9
  · exact blocktrue10
  · exact blocktrue11
  · exact blocktrue12
  · exact blocktrue13
  · exact blocktrue14
  · exact blocktrue15

end TwoPermutationPrototype.RV64.R1bParents
