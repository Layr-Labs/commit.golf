import CommitGolfCandidate.ChainedInverseRecordCode

/-! A fixed image reconstructs any number of 30-byte footer rows from parsed descriptors. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

def inverseFooterOps : List Instr :=
  [.BEQ .x22 .x0 492]++inverseFieldOps 29++[.ADDI .x22 .x22 4095,.BNE .x22 .x0 7708]
def inverseFooterWords : List (BitVec 32) :=
  [0x1e0b0663]++inverseFieldWords 29++[0xfffb0b13,0xe00b1ee3]
def inverseFooterImage : Image := ⟨inverseFooterWords,[]⟩

theorem inverse_footer_words_length : inverseFooterWords.length=123 := by decide +kernel
theorem inverse_footer_ops_length : inverseFooterOps.length=123 := by decide +kernel
theorem inverse_footer_decode :
    inverseFooterWords.map inverseDecodeBase=inverseFooterOps.map some := by decide +kernel

theorem inverse_footer_decode_at (i : Fin 123) :
    (inverseFooterWords[i.val]?).bind decodeInstruction=some (.base (inverseFooterOps.getD i.val .EBREAK)) := by
  have projected := congrArg (fun xs => xs[i.val]?) inverse_footer_decode
  simp only [List.getElem?_map] at projected
  have op : inverseFooterOps[i.val]?=some (inverseFooterOps.getD i.val .EBREAK) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [inverse_footer_ops_length]; exact i.isLt)]
    rfl
  rw [op] at projected
  cases word : inverseFooterWords[i.val]? with
  | none => simp [word] at projected
  | some value =>
    simp only [word,Option.map_some,Option.some.injEq] at projected
    simp only [word,Option.bind_some]
    cases decoded : decodeInstruction value with
    | none => simp [inverseDecodeBase,decoded] at projected
    | some instruction =>
      cases instruction <;> simp [inverseDecodeBase,decoded] at projected <;> simp [projected]

theorem inverse_footer_ops_at : OpsAt inverseFooterImage 4096 inverseFooterOps := by
  intro index inside s pc
  have bound : index<123 := by simpa only [inverse_footer_ops_length] using inside
  apply cap_image_fetch inverseFooterImage s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact inverse_footer_decode_at ⟨index,bound⟩

theorem inverse_footer_body_at (image : Image) (base : Word) (code : OpsAt image base inverseFooterOps) :
    LowCopyAt image (base+4) 29 ∧ InverseFieldTailAt image ((base+4)+464) := by
  have start := ops_at_right image base [.BEQ .x22 .x0 492] _ code
  have body := ops_at_left image (base+4) (inverseFieldOps 29) _ start
  constructor
  · intro index inside i s pc
    have bound : 4*index+i.val<4*29 := by have := i.isLt; omega
    have location : s.pc=(base+4)+BitVec.ofNat 64 (4*(4*index+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*index+i.val) (by simp only [inverseFieldOps,List.length_ofFn]; omega) s location
    have same : inverseFieldOp 29 (4*index+i.val)=byteCopyOp i.val := by
      have remainder : (4*index+i.val)%4=i.val := by have := i.isLt; omega
      simp only [inverseFieldOp,ite_eq_left bound,remainder]
    simpa only [inverse_field_ops_get 29 (4*index+i.val) (by omega),same] using result
  · intro i s pc
    have location : s.pc=(base+4)+BitVec.ofNat 64 (4*(4*29+i.val)) := by
      change s.pc=((base+4)+BitVec.ofNat 64 464)+BitVec.ofNat 64 (4*i.val) at pc
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*29+i.val)
      (by simp only [inverseFieldOps,List.length_ofFn]; have := i.isLt; omega) s location
    have same : inverseFieldOp 29 (4*29+i.val)=inverseFieldTailOp i.val := by simp [inverseFieldOp]
    simpa only [inverse_field_ops_get 29 (4*29+i.val) (by have := i.isLt; omega),same] using result

end CommitGolfCandidate.Chained.Native
