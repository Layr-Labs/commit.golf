import CommitGolfCandidate.QuadCheckImage
import CommitGolfCandidate.PentaWrapRunC
import CommitGolfCandidate.QOpeningImage

/-! The checker image carries the cap wrapper: the entry jump at word 0 and the wrapper code at
words 460-774. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

private theorem base_of_decode (w : BitVec 32) (instr : Instr) (h : QOpening.decodeBase w = some instr) :
    decodeInstruction w = some (.base instr) := by
  unfold QOpening.decodeBase at h
  cases hd : decodeInstruction w with
  | none => simp [hd] at h
  | some r =>
    cases r with
    | base b =>
      simp only [hd, Option.bind_some, Option.some.injEq] at h
      rw [h]
    | word op rd rs₁ rs₂ => simp [hd] at h
    | sraiw rd rs sh => simp [hd] at h

set_option maxRecDepth 100000 in
private theorem entry_decoded :
    (quadCheckImage.code[0]?).bind QOpening.decodeBase = some (.JAL .x0 1840) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem wrap_decoded :
    ∀ i < 315, (quadCheckImage.code[460+i]?).bind QOpening.decodeBase = PentaWrap.wrapCode[i]? := by
  decide +kernel

theorem quad_wrap_image : PentaWrap.WrapImage quadCheckImage where
  entry := by
    have h := entry_decoded
    cases hc : quadCheckImage.code[0]? with
    | none => rw [hc] at h; cases h
    | some w =>
      rw [hc, Option.bind_some] at h
      rw [Option.bind_some]
      exact base_of_decode w _ h
  words := by
    intro i hi
    have h := wrap_decoded i hi
    have hw : PentaWrap.wrapCode[i]? = some (PentaWrap.wrapCode[i]'(by rw [PentaWrap.wrap_code_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    rw [hw] at h ⊢
    cases hc : quadCheckImage.code[460+i]? with
    | none => rw [hc] at h; cases h
    | some w =>
      rw [hc, Option.bind_some] at h
      rw [Option.bind_some, Option.map_some]
      exact base_of_decode w _ h

end TwoPermutationPrototype.Quad.Checker
