import CommitGolfCandidate.HeadStreamExec

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStream
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem emit_word_0 (m : Nat) (hm : m<7) : instrAt (174+7*m)=.LBU .x24 .x28 (BitVec.ofNat 12 (m+1)) := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val)=.LBU .x24 .x28 (BitVec.ofNat 12 (m.val+1)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_1 (m : Nat) (hm : m<7) : instrAt (174+7*m+1)=.ANDI .x24 .x24 127 := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+1)=.ANDI .x24 .x24 127 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_2 (m : Nat) (hm : m<7) : instrAt (174+7*m+2)=.SRLI .x29 .x23 (BitVec.ofNat 6 m) := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+2)=.SRLI .x29 .x23 (BitVec.ofNat 6 m.val) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_3 (m : Nat) (hm : m<7) : instrAt (174+7*m+3)=.SLLI .x30 .x24 (BitVec.ofNat 6 (7-m)) := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+3)=.SLLI .x30 .x24 (BitVec.ofNat 6 (7-m.val)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_4 (m : Nat) (hm : m<7) : instrAt (174+7*m+4)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+4)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_5 (m : Nat) (hm : m<7) : instrAt (174+7*m+5)=.SB .x26 .x29 (BitVec.ofNat 12 m) := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+5)=.SB .x26 .x29 (BitVec.ofNat 12 m.val) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_6 (m : Nat) (hm : m<7) : instrAt (174+7*m+6)=.ADDI .x23 .x24 0 := by
  exact (show ∀ m : Fin 7, instrAt (174+7*m.val+6)=.ADDI .x23 .x24 0 by decide) ⟨m,hm⟩


theorem byte_and127 (x : Byte) : x.setWidth 64 &&& 127#64=BitVec.ofNat 64 (x.toNat%128) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [show (127 : Nat)=2^7-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem combine_words (a b m : Nat) (ha : a<128) (hb : b<128) (hm : m<7) :
    BitVec.ofNat 64 (a/2^m) ||| BitVec.ofNat 64 (b*2^(7-m))=
      BitVec.ofNat 64 (a/2^m+b*2^(7-m)) := by
  have low : a/2^m<2^(7-m) := by interval_cases m <;> norm_num at * <;> omega
  have pow : 2^(7-m)≤128 := by interval_cases m <;> norm_num
  have prod : b*2^(7-m)≤127*128 := Nat.mul_le_mul (by omega) pow
  exact w_or_mul (a/2^m) b (2^(7-m)) (7-m) rfl low
    (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by omega) (by omega)

def emitPath (m : Nat) : List Nat :=
  [174+7*m,174+7*m+1,174+7*m+2,174+7*m+3,174+7*m+4,174+7*m+5,174+7*m+6]

theorem emit_keeps (m : Nat) (hm : m<7) :
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m) r)=true := by
  exact (show ∀ m : Fin 7,
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m.val) r)=true by decide) ⟨m,hm⟩

set_option maxHeartbeats 1000000 in
theorem emit_one (m a b I O : Nat) (hm : m<7) (ha : a<128) (hb : b<128)
    (s : MachineState) (pc : s.pc=pcOf (174+7*m))
    (x28 : s.getReg .x28=BitVec.ofNat 64 I) (x26 : s.getReg .x26=BitVec.ofNat 64 O)
    (x23 : s.getReg .x23=BitVec.ofNat 64 a)
    (input : I+m+2≤2^36) (output : O+m+1≤2^36)
    (load : (s.getByte (BitVec.ofNat 64 (I+(m+1)))).toNat%128=b) :
    PathOK s (emitPath m) ∧ (run s (emitPath m)).pc=pcOf (174+7*(m+1)) ∧
      (run s (emitPath m)).getReg .x23=BitVec.ofNat 64 b ∧
      (∀ q, (run s (emitPath m)).getByte q=
        if q=BitVec.ofNat 64 (O+m) then BitVec.ofNat 8 (a/2^m+b*2^(7-m)) else s.getByte q) ∧
      Runs s (run s (emitPath m)) 7 7 := by
  have imm : (signExtend12 (BitVec.ofNat 12 m)).toNat=m ∧
      signExtend12 (BitVec.ofNat 12 (m+1))=BitVec.ofNat 64 (m+1) ∧
      signExtend12 (BitVec.ofNat 12 m)=BitVec.ofNat 64 m := by
    interval_cases m <;> decide
  have ok : PathOK s (emitPath m) := by
    simp (disch := omega) [PathOK,emitPath,emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,
      emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,execInstrBr,
      pc,x28,x26,ordinaryInstr,memoryArgumentsValid,memAccess,imm.2.1,imm.2.2,w_add]
    refine ⟨by omega,?_,by omega,by omega,by omega,by omega,by omega,?_,by omega⟩ <;>
      apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  refine ⟨ok,?_,?_,?_,(runs_path _ s ok).cast ?_ ?_⟩
  · simp (disch := omega) [run,emitPath,emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,
      emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,execInstrBr,pc]
    congr 1 <;> omega
  · simp (disch := omega) [run,emitPath,emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,
      emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,execInstrBr,x28,
      imm.2.1,w_add,byte_and127,load]
  · intro q
    simp (disch := omega) [run,emitPath,emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,
      emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,execInstrBr,
      x28,x26,x23,imm.2.1,imm.2.2,w_add,byte_and127,load,w_shl,w_shr,
      combine_words a b m ha hb hm,truncate_w,Nat.mod_eq_of_lt (show m<64 by omega),
      Nat.mod_eq_of_lt (show 7-m<64 by omega)]
  · rfl
  · exact (show ∀ m : Fin 7, pathCycles (emitPath m.val)=7 by decide) ⟨m,hm⟩

end TwoPermutationPrototype.PackedOpening.HeadStream
