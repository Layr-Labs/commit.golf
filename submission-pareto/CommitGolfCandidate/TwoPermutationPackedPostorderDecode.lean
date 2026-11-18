import CommitGolfCandidate.TwoPermutationPackedPostorderProgram

namespace TwoPermutationPrototype.Opening.Postorder
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

/-- Check each machine word once in image order. The recursive proof uses this
table through CodeAt, without interpreting a different opening program. -/
private theorem table :
    ((TwoPermutationPrototype.PackedOpening.openingImage.code.drop 674).take 766).map decodeBase = (words 1 8 0).map some := by decide

theorem code_at_root : CodeAt 674 (words 1 8 0) := by
  intro j
  have size : cost 8 = 766 := rfl
  have bounded : j.val < 766 := by simpa only [words_length,size] using j.isLt
  have atWord := congrArg (fun xs : List (Option Instr) => xs[j.val]?) table
  simp only [List.getElem?_map, List.getElem?_take, bounded, ite_true,
    List.getElem?_drop, List.getElem?_eq_getElem j.isLt, Option.map_some] at atWord
  cases hw : TwoPermutationPrototype.PackedOpening.openingImage.code[674+j.val]? with
  | none => simp [hw] at atWord
  | some w =>
    simp only [hw, Option.map_some, Option.some.injEq] at atWord
    cases hi : decodeInstruction w with
    | none => simp [decodeBase, hi] at atWord
    | some op =>
      cases op <;> simp [decodeBase, hi] at atWord <;> simp [hi, atWord]

end TwoPermutationPrototype.Opening.Postorder
