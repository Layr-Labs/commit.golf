import CommitGolfCandidate.ChainedCheckerControllerCode
import CommitGolfCandidate.ChainedInverseFooterCode

/-! Exact chained checking image and the reused generic hashing components. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem chained_checker_decode_at (index : Fin 3012) :
    (chainedCheckerWords[index.val]?).bind decodeInstruction=
      some (.base (chainedCheckerOps.getD index.val .EBREAK)) := by
  have projected := congrArg (fun xs => xs[index.val]?) chained_checker_decode
  simp only [List.getElem?_map] at projected
  have op : chainedCheckerOps[index.val]?=some (chainedCheckerOps.getD index.val .EBREAK) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [chained_checker_ops_length]; exact index.isLt)]
    rfl
  rw [op] at projected
  cases word : chainedCheckerWords[index.val]? with
  | none => simp [word] at projected
  | some value =>
    simp only [word,Option.map_some,Option.some.injEq] at projected
    simp only [word,Option.bind_some]
    cases decoded : decodeInstruction value with
    | none => simp [inverseDecodeBase,decoded] at projected
    | some instruction =>
      cases instruction <;> simp [inverseDecodeBase,decoded] at projected <;> simp [projected]

theorem chained_checker_ops_at : OpsAt chainedCheckerImage 4096 chainedCheckerOps := by
  intro index inside s pc
  have bound : index<3012 := by rwa [chained_checker_ops_length] at inside
  apply inverse_image_fetch chainedCheckerImage s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact chained_checker_decode_at ⟨index,bound⟩

theorem chained_checker_slice_at (start count : Nat) (ops : List Instr)
    (inside : start≤chainedCheckerOps.length) (part : (chainedCheckerOps.drop start).take count=ops) :
    OpsAt chainedCheckerImage (4096+BitVec.ofNat 64 (4*start)) ops := by
  have whole := chained_checker_ops_at
  rw [←List.take_append_drop start chainedCheckerOps] at whole
  have tail := ops_at_right chainedCheckerImage 4096 (chainedCheckerOps.take start) (chainedCheckerOps.drop start) whole
  rw [List.length_take,Nat.min_eq_left inside] at tail
  rw [←List.take_append_drop count (chainedCheckerOps.drop start)] at tail
  have front := ops_at_left chainedCheckerImage (4096+BitVec.ofNat 64 (4*start))
    ((chainedCheckerOps.drop start).take count) ((chainedCheckerOps.drop start).drop count) tail
  rwa [part] at front

theorem chained_checker_record_widths_at :
    OpsAt chainedCheckerImage (4096+4*58) (widthTableOps recordWidths) := by
  exact chained_checker_slice_at 58 51 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem chained_checker_record_parse_at : TailParseAt chainedCheckerImage (4096+4*115) := by
  have code := chained_checker_slice_at 115 21 tailParseOps
    (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

theorem chained_checker_record_inverse_at :
    OpsAt chainedCheckerImage (4096+4*142) inverseRecordPlanOps := by
  exact chained_checker_slice_at 142 2018 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem chained_checker_footer_width_at :
    OpsAt chainedCheckerImage (4096+4*2175) footerWidthsOps := by
  exact chained_checker_slice_at 2175 6 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem chained_checker_footer_parse_at : TailParseAt chainedCheckerImage (4096+4*2202) := by
  have code := chained_checker_slice_at 2202 21 tailParseOps
    (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

theorem chained_checker_footer_inverse_at :
    OpsAt chainedCheckerImage (4096+4*2229) inverseFooterOps := by
  exact chained_checker_slice_at 2229 123 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem chained_checker_first_pack_at : FirstPackAt chainedCheckerImage (4096+4*2959) := by
  have code := chained_checker_slice_at 2959 31 firstPackOps
    (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

theorem chained_checker_continuation_at : ContinuationAt chainedCheckerImage (4096+4*2990) := by
  have code := chained_checker_slice_at 2990 19 continuationOps
    (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

end CommitGolfCandidate.Chained.Native
