import CommitGolfCandidate.HeadStreamExec

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamFour
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[simp] theorem emit_word_0 (m : Nat) (hm : m<4) : instrAt (174+12*m)=.LBU .x23 .x28 (BitVec.ofNat 12 (8*m/4)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val)=.LBU .x23 .x28 (BitVec.ofNat 12 (8*m.val/4)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_1 (m : Nat) (hm : m<4) : instrAt (174+12*m+1)=.ANDI .x23 .x23 15 := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+1)=.ANDI .x23 .x23 15 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_2 (m : Nat) (hm : m<4) : instrAt (174+12*m+2)=.LBU .x24 .x28 (BitVec.ofNat 12 (8*m/4+1)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+2)=.LBU .x24 .x28 (BitVec.ofNat 12 (8*m.val/4+1)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_3 (m : Nat) (hm : m<4) : instrAt (174+12*m+3)=.ANDI .x24 .x24 15 := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+3)=.ANDI .x24 .x24 15 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_4 (m : Nat) (hm : m<4) : instrAt (174+12*m+4)=.LBU .x31 .x28 (BitVec.ofNat 12 (8*m/4+2)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+4)=.LBU .x31 .x28 (BitVec.ofNat 12 (8*m.val/4+2)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_5 (m : Nat) (hm : m<4) : instrAt (174+12*m+5)=.ANDI .x31 .x31 15 := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+5)=.ANDI .x31 .x31 15 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_6 (m : Nat) (hm : m<4) : instrAt (174+12*m+6)=.SRLI .x29 .x23 (BitVec.ofNat 6 (8*m%4)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+6)=.SRLI .x29 .x23 (BitVec.ofNat 6 (8*m.val%4)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_7 (m : Nat) (hm : m<4) : instrAt (174+12*m+7)=.SLLI .x30 .x24 (BitVec.ofNat 6 (4-8*m%4)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+7)=.SLLI .x30 .x24 (BitVec.ofNat 6 (4-8*m.val%4)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_8 (m : Nat) (hm : m<4) : instrAt (174+12*m+8)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+8)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_9 (m : Nat) (hm : m<4) : instrAt (174+12*m+9)=.SLLI .x30 .x31 (BitVec.ofNat 6 (8-8*m%4)) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+9)=.SLLI .x30 .x31 (BitVec.ofNat 6 (8-8*m.val%4)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_10 (m : Nat) (hm : m<4) : instrAt (174+12*m+10)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+10)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_11 (m : Nat) (hm : m<4) : instrAt (174+12*m+11)=.SB .x26 .x29 (BitVec.ofNat 12 m) := by
  exact (show ∀ m : Fin 4, instrAt (174+12*m.val+11)=.SB .x26 .x29 (BitVec.ofNat 12 m.val) by decide) ⟨m,hm⟩

theorem byte_and15 (x : Byte) : x.setWidth 64 &&& 15#64=BitVec.ofNat 64 (x.toNat%16) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [show (15 : Nat)=2^4-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem combine_words (a b c m : Nat) (ha : a<16) (hb : b<16) (hc : c<16) (hm : m<4) :
    (BitVec.ofNat 64 (a/2^(8*m%4)) ||| BitVec.ofNat 64 (b*2^(4-8*m%4))) |||
      BitVec.ofNat 64 (c*2^(8-8*m%4))=
      BitVec.ofNat 64 (a/2^(8*m%4)+b*2^(4-8*m%4)+c*2^(8-8*m%4)) := by
  have low : a/2^(8*m%4)<2^(4-8*m%4) := by interval_cases m <;> norm_num at * <;> omega
  have middle : a/2^(8*m%4)+b*2^(4-8*m%4)<2^(8-8*m%4) := by
    interval_cases m <;> norm_num at * <;> omega
  have small : a/2^(8*m%4)+b*2^(4-8*m%4)+c*2^(8-8*m%4)<2^64 := by
    interval_cases m <;> norm_num at * <;> omega
  have leftSmall : a/2^(8*m%4)+b*2^(4-8*m%4)<2^64 :=
    lt_of_le_of_lt (Nat.le_add_right _ _) small
  have first := w_or_mul (a/2^(8*m%4)) b (2^(4-8*m%4)) (4-8*m%4) rfl low
    (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ _) leftSmall) leftSmall
  rw [first]
  exact w_or_mul _ c (2^(8-8*m%4)) (8-8*m%4) rfl middle leftSmall
    (lt_of_le_of_lt (Nat.le_add_left _ _) small) small

def emitPath (m : Nat) : List Nat :=
  [174+12*m,174+12*m+1,174+12*m+2,174+12*m+3,174+12*m+4,174+12*m+5,
   174+12*m+6,174+12*m+7,174+12*m+8,174+12*m+9,174+12*m+10,174+12*m+11]

theorem emit_keeps (m : Nat) (hm : m<4) :
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m) r)=true := by
  exact (show ∀ m : Fin 4,
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m.val) r)=true by decide) ⟨m,hm⟩

theorem emit_one (m a b c I O : Nat) (hm : m<4) (ha : a<16) (hb : b<16) (hc : c<16)
    (s : MachineState) (pc : s.pc=pcOf (174+12*m))
    (x28 : s.getReg .x28=BitVec.ofNat 64 I) (x26 : s.getReg .x26=BitVec.ofNat 64 O)
    (input : I+8*m/4+3≤2^36) (output : O+m+1≤2^36)
    (load₀ : (s.getByte (BitVec.ofNat 64 (I+8*m/4))).toNat%16=a)
    (load₁ : (s.getByte (BitVec.ofNat 64 (I+(8*m/4+1)))).toNat%16=b)
    (load₂ : (s.getByte (BitVec.ofNat 64 (I+(8*m/4+2)))).toNat%16=c) :
    PathOK s (emitPath m) ∧ (run s (emitPath m)).pc=pcOf (174+12*(m+1)) ∧
      (∀ q, (run s (emitPath m)).getByte q=
        if q=BitVec.ofNat 64 (O+m) then
          BitVec.ofNat 8 (a/2^(8*m%4)+b*2^(4-8*m%4)+c*2^(8-8*m%4)) else s.getByte q) ∧
      Runs s (run s (emitPath m)) 12 12 := by
  have imm (n : Nat) (hn : n≤8) : signExtend12 (BitVec.ofNat 12 n)=BitVec.ofNat 64 n := by
    interval_cases n <;> decide
  have i₀ := imm (8*m/4) (by omega)
  have i₁ := imm (8*m/4+1) (by omega)
  have i₂ := imm (8*m/4+2) (by omega)
  have im := imm m (by omega)
  have ok : PathOK s (emitPath m) := by
    simp (disch := omega) [PathOK,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,
      execInstrBr,pc,x28,x26,ordinaryInstr,memoryArgumentsValid,memAccess,i₀,i₁,i₂,im,w_add]
    repeat' apply And.intro
    all_goals first | omega | (apply accessValid_of; rw [toNat_w _ (by omega)]; omega)
  refine ⟨ok,?_,?_,(runs_path _ s ok).cast rfl ?_⟩
  · simp (disch := omega) [run,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,
      execInstrBr,pc]
    congr 1 <;> omega
  · intro q
    simp (disch := omega) [run,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,
      execInstrBr,x28,x26,i₀,i₁,i₂,im,w_add,byte_and15,load₀,load₁,load₂,w_shl,w_shr,
      combine_words a b c m ha hb hc hm,truncate_w,
      Nat.mod_eq_of_lt (show 8*m%4<64 by omega),
      Nat.mod_eq_of_lt (show 4-8*m%4<64 by omega),
      Nat.mod_eq_of_lt (show 8-8*m%4<64 by omega)]
  · exact (show ∀ m : Fin 4, pathCycles (emitPath m.val)=12 by decide) ⟨m,hm⟩

end TwoPermutationPrototype.PackedOpening.HeadStream
