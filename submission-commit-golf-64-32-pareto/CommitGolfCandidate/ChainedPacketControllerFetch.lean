import CommitGolfCandidate.ChainedPacketControllerCode
import CommitGolfCandidate.ChainedInverseFooterCode

/-! Exact standalone decoder fetches and placements of its checked components. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem packet_decoder_decode_at (index : Fin 2367) :
    (packetDecoderWords[index.val]?).bind decodeInstruction=
      some (.base (packetDecoderOps.getD index.val .EBREAK)) := by
  have projected := congrArg (fun xs => xs[index.val]?) packet_decoder_decode
  simp only [List.getElem?_map] at projected
  have op : packetDecoderOps[index.val]?=some (packetDecoderOps.getD index.val .EBREAK) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [packet_decoder_ops_length]; exact index.isLt)]
    rfl
  rw [op] at projected
  cases word : packetDecoderWords[index.val]? with
  | none => simp [word] at projected
  | some value =>
    simp only [word,Option.map_some,Option.some.injEq] at projected
    simp only [word,Option.bind_some]
    cases decoded : decodeInstruction value with
    | none => simp [inverseDecodeBase,decoded] at projected
    | some instruction =>
      cases instruction <;> simp [inverseDecodeBase,decoded] at projected <;> simp [projected]

theorem packet_decoder_ops_at : OpsAt packetDecoderImage 4096 packetDecoderOps := by
  intro index inside s pc
  have bound : index<2367 := by rwa [packet_decoder_ops_length] at inside
  apply inverse_image_fetch packetDecoderImage s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact packet_decoder_decode_at ⟨index,bound⟩

theorem packet_decoder_slice_at (start count : Nat) (ops : List Instr)
    (inside : start≤packetDecoderOps.length) (part : (packetDecoderOps.drop start).take count=ops) :
    OpsAt packetDecoderImage (4096+BitVec.ofNat 64 (4*start)) ops := by
  have whole := packet_decoder_ops_at
  rw [←List.take_append_drop start packetDecoderOps] at whole
  have tail := ops_at_right packetDecoderImage 4096 (packetDecoderOps.take start) (packetDecoderOps.drop start) whole
  rw [List.length_take,Nat.min_eq_left inside] at tail
  rw [←List.take_append_drop count (packetDecoderOps.drop start)] at tail
  have front := ops_at_left packetDecoderImage (4096+BitVec.ofNat 64 (4*start))
    ((packetDecoderOps.drop start).take count) ((packetDecoderOps.drop start).drop count) tail
  rwa [part] at front

theorem packet_decoder_record_widths_at :
    OpsAt packetDecoderImage (4096+4*58) (widthTableOps recordWidths) := by
  exact packet_decoder_slice_at 58 51 _ (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)

theorem packet_decoder_record_parse_at : TailParseAt packetDecoderImage (4096+4*115) := by
  have code := packet_decoder_slice_at 115 21 tailParseOps
    (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

theorem packet_decoder_record_inverse_at :
    OpsAt packetDecoderImage (4096+4*142) inverseRecordPlanOps := by
  exact packet_decoder_slice_at 142 2018 _ (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)

theorem packet_decoder_footer_width_at :
    OpsAt packetDecoderImage (4096+4*2175) footerWidthsOps := by
  exact packet_decoder_slice_at 2175 6 _ (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)

theorem packet_decoder_footer_parse_at : TailParseAt packetDecoderImage (4096+4*2202) := by
  have code := packet_decoder_slice_at 2202 21 tailParseOps
    (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)
  intro index s pc
  exact code index.val index.isLt s pc

theorem packet_decoder_footer_inverse_at :
    OpsAt packetDecoderImage (4096+4*2229) inverseFooterOps := by
  exact packet_decoder_slice_at 2229 123 _ (by rw [packet_decoder_ops_length]; decide) (by decide +kernel)

end CommitGolfCandidate.Chained.Native
