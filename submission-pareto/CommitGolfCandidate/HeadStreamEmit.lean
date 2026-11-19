import CommitGolfCandidate.HeadStreamExec
import CommitGolfCandidate.HeadStreamThree

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamThree
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[simp] theorem emit_word_0 (m : Nat) (hm : m<3) : instrAt (174+16*m)=.LBU .x23 .x28 (BitVec.ofNat 12 (8*m/3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val)=.LBU .x23 .x28 (BitVec.ofNat 12 (8*m.val/3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_1 (m : Nat) (hm : m<3) : instrAt (174+16*m+1)=.ANDI .x23 .x23 7 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+1)=.ANDI .x23 .x23 7 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_2 (m : Nat) (hm : m<3) : instrAt (174+16*m+2)=.LBU .x24 .x28 (BitVec.ofNat 12 (8*m/3+1)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+2)=.LBU .x24 .x28 (BitVec.ofNat 12 (8*m.val/3+1)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_3 (m : Nat) (hm : m<3) : instrAt (174+16*m+3)=.ANDI .x24 .x24 7 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+3)=.ANDI .x24 .x24 7 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_4 (m : Nat) (hm : m<3) : instrAt (174+16*m+4)=.LBU .x31 .x28 (BitVec.ofNat 12 (8*m/3+2)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+4)=.LBU .x31 .x28 (BitVec.ofNat 12 (8*m.val/3+2)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_5 (m : Nat) (hm : m<3) : instrAt (174+16*m+5)=.ANDI .x31 .x31 7 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+5)=.ANDI .x31 .x31 7 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_6 (m : Nat) (hm : m<3) : instrAt (174+16*m+6)=.SRLI .x29 .x23 (BitVec.ofNat 6 (8*m%3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+6)=.SRLI .x29 .x23 (BitVec.ofNat 6 (8*m.val%3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_7 (m : Nat) (hm : m<3) : instrAt (174+16*m+7)=.SLLI .x30 .x24 (BitVec.ofNat 6 (3-8*m%3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+7)=.SLLI .x30 .x24 (BitVec.ofNat 6 (3-8*m.val%3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_8 (m : Nat) (hm : m<3) : instrAt (174+16*m+8)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+8)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_9 (m : Nat) (hm : m<3) : instrAt (174+16*m+9)=.SLLI .x30 .x31 (BitVec.ofNat 6 (6-8*m%3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+9)=.SLLI .x30 .x31 (BitVec.ofNat 6 (6-8*m.val%3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_10 (m : Nat) (hm : m<3) : instrAt (174+16*m+10)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+10)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_11 (m : Nat) (hm : m<3) : instrAt (174+16*m+11)=.LBU .x25 .x28 (BitVec.ofNat 12 (8*m/3+3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+11)=.LBU .x25 .x28 (BitVec.ofNat 12 (8*m.val/3+3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_12 (m : Nat) (hm : m<3) : instrAt (174+16*m+12)=.ANDI .x25 .x25 7 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+12)=.ANDI .x25 .x25 7 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_13 (m : Nat) (hm : m<3) : instrAt (174+16*m+13)=.SLLI .x30 .x25 (BitVec.ofNat 6 (9-8*m%3)) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+13)=.SLLI .x30 .x25 (BitVec.ofNat 6 (9-8*m.val%3)) by decide) ⟨m,hm⟩

@[simp] theorem emit_word_14 (m : Nat) (hm : m<3) : instrAt (174+16*m+14)=.OR .x29 .x29 .x30 := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+14)=.OR .x29 .x29 .x30 by decide) ⟨m,hm⟩

@[simp] theorem emit_word_15 (m : Nat) (hm : m<3) : instrAt (174+16*m+15)=.SB .x26 .x29 (BitVec.ofNat 12 m) := by
  exact (show ∀ m : Fin 3, instrAt (174+16*m.val+15)=.SB .x26 .x29 (BitVec.ofNat 12 m.val) by decide) ⟨m,hm⟩

theorem byte_and7 (x : Byte) : x.setWidth 64 &&& 7#64=BitVec.ofNat 64 (x.toNat%8) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [show (7 : Nat)=2^3-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem combine_words (a b c d m : Nat) (ha : a<8) (hb : b<8) (hc : c<8) (hd : d<8) (hm : m<3) :
    ((BitVec.ofNat 64 (a/2^(8*m%3)) ||| BitVec.ofNat 64 (b*2^(3-8*m%3))) |||
      BitVec.ofNat 64 (c*2^(6-8*m%3))) ||| BitVec.ofNat 64 (d*2^(9-8*m%3)) =
      BitVec.ofNat 64 (a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)+d*2^(9-8*m%3)) := by
  have low : a/2^(8*m%3)<2^(3-8*m%3) := by interval_cases m <;> norm_num at * <;> omega
  have middle : a/2^(8*m%3)+b*2^(3-8*m%3)<2^(6-8*m%3) := by
    interval_cases m <;> norm_num at * <;> omega
  have upper : a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)<2^(9-8*m%3) := by
    interval_cases m <;> norm_num at * <;> omega
  have small : a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)+d*2^(9-8*m%3)<2^64 := by
    interval_cases m <;> norm_num at * <;> omega
  have leftSmall : a/2^(8*m%3)+b*2^(3-8*m%3)<2^64 := by omega
  have midSmall : a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)<2^64 := by omega
  rw [w_or_mul _ b _ (3-8*m%3) rfl low
    (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ _) leftSmall) leftSmall,
    w_or_mul _ c _ (6-8*m%3) rfl middle leftSmall
      (lt_of_le_of_lt (Nat.le_add_left _ _) midSmall) midSmall]
  exact w_or_mul _ d _ (9-8*m%3) rfl upper midSmall
    (lt_of_le_of_lt (Nat.le_add_left _ _) small) small

def emitPath (m : Nat) : List Nat :=
  [174+16*m,174+16*m+1,174+16*m+2,174+16*m+3,174+16*m+4,174+16*m+5,
   174+16*m+6,174+16*m+7,174+16*m+8,174+16*m+9,174+16*m+10,174+16*m+11,
   174+16*m+12,174+16*m+13,174+16*m+14,174+16*m+15]

theorem emit_keeps (m : Nat) (hm : m<3) :
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m) r)=true := by
  exact (show ∀ m : Fin 3,
    ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg).all
      (fun r => !writesAny (emitPath m.val) r)=true by decide) ⟨m,hm⟩

theorem emit_one (m a b c d I O : Nat) (hm : m<3) (ha : a<8) (hb : b<8) (hc : c<8) (hd : d<8)
    (s : MachineState) (pc : s.pc=pcOf (174+16*m))
    (x28 : s.getReg .x28=BitVec.ofNat 64 I) (x26 : s.getReg .x26=BitVec.ofNat 64 O)
    (input : I+8*m/3+4≤2^36) (output : O+m+1≤2^36)
    (load₀ : (s.getByte (BitVec.ofNat 64 (I+8*m/3))).toNat%8=a)
    (load₁ : (s.getByte (BitVec.ofNat 64 (I+(8*m/3+1)))).toNat%8=b)
    (load₂ : (s.getByte (BitVec.ofNat 64 (I+(8*m/3+2)))).toNat%8=c)
    (load₃ : (s.getByte (BitVec.ofNat 64 (I+(8*m/3+3)))).toNat%8=d) :
    PathOK s (emitPath m) ∧ (run s (emitPath m)).pc=pcOf (174+16*(m+1)) ∧
      (∀ q, (run s (emitPath m)).getByte q=
        if q=BitVec.ofNat 64 (O+m) then
          BitVec.ofNat 8 (a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)+d*2^(9-8*m%3)) else s.getByte q) ∧
      Runs s (run s (emitPath m)) 16 16 := by
  have imm (n : Nat) (hn : n≤8) : signExtend12 (BitVec.ofNat 12 n)=BitVec.ofNat 64 n := by
    interval_cases n <;> decide
  have i₀ := imm (8*m/3) (by omega)
  have i₁ := imm (8*m/3+1) (by omega)
  have i₂ := imm (8*m/3+2) (by omega)
  have i₃ := imm (8*m/3+3) (by omega)
  have im := imm m (by omega)
  have ok : PathOK s (emitPath m) := by
    simp (disch := omega) [PathOK,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,emit_word_12 m hm,emit_word_13 m hm,emit_word_14 m hm,emit_word_15 m hm,
      execInstrBr,pc,x28,x26,ordinaryInstr,memoryArgumentsValid,memAccess,i₀,i₁,i₂,i₃,im,w_add]
    repeat' apply And.intro
    all_goals first | omega | (apply accessValid_of; rw [toNat_w _ (by omega)]; omega)
  refine ⟨ok,?_,?_,(runs_path _ s ok).cast rfl ?_⟩
  · simp (disch := omega) [run,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,emit_word_12 m hm,emit_word_13 m hm,emit_word_14 m hm,emit_word_15 m hm,
      execInstrBr,pc]
    congr 1 <;> omega
  · intro q
    simp (disch := omega) [run,emitPath,
      emit_word_0 m hm,emit_word_1 m hm,emit_word_2 m hm,emit_word_3 m hm,emit_word_4 m hm,emit_word_5 m hm,emit_word_6 m hm,emit_word_7 m hm,emit_word_8 m hm,emit_word_9 m hm,emit_word_10 m hm,emit_word_11 m hm,emit_word_12 m hm,emit_word_13 m hm,emit_word_14 m hm,emit_word_15 m hm,
      execInstrBr,x28,x26,i₀,i₁,i₂,i₃,im,w_add,byte_and7,load₀,load₁,load₂,load₃,w_shl,w_shr,
      combine_words a b c d m ha hb hc hd hm,truncate_w,
      Nat.mod_eq_of_lt (show 8*m%3<64 by omega),
      Nat.mod_eq_of_lt (show 3-8*m%3<64 by omega),
      Nat.mod_eq_of_lt (show 6-8*m%3<64 by omega),
      Nat.mod_eq_of_lt (show 9-8*m%3<64 by omega)]
  · exact (show ∀ m : Fin 3, pathCycles (emitPath m.val)=16 by decide) ⟨m,hm⟩

end TwoPermutationPrototype.PackedOpening.HeadStream
