import CommitGolfCandidate.TwoPermutationPackedOpeningPack
import CommitGolfCandidate.HeadStreamThree

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamThree
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg set_byte_read

@[simp] theorem word_0 : instrAt 142=.SUB .x18 .x11 .x16 := rfl
@[simp] theorem word_1 : instrAt 143=.ADDI .x9 .x0 480 := rfl
@[simp] theorem word_2 : instrAt 144=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_3 : instrAt 145=.ADD .x30 .x27 .x16 := rfl
@[simp] theorem word_4 : instrAt 146=.SB .x30 .x0 0 := rfl
@[simp] theorem word_5 : instrAt 147=.SB .x30 .x0 1 := rfl
@[simp] theorem word_6 : instrAt 148=.SB .x30 .x0 2 := rfl
@[simp] theorem word_7 : instrAt 149=.SB .x30 .x0 3 := rfl
@[simp] theorem word_8 : instrAt 150=.SB .x30 .x0 4 := rfl
@[simp] theorem word_9 : instrAt 151=.SB .x30 .x0 5 := rfl
@[simp] theorem word_10 : instrAt 152=.SB .x30 .x0 6 := rfl
@[simp] theorem word_11 : instrAt 153=.ADDI .x7 .x16 7 := rfl
@[simp] theorem word_12 : instrAt 154=.SRLI .x7 .x7 3 := rfl
@[simp] theorem word_13 : instrAt 155=.ADD .x26 .x20 .x18 := rfl
@[simp] theorem word_14 : instrAt 156=.BEQ .x22 .x18 48 := rfl
@[simp] theorem word_15 : instrAt 157=.JAL .x0 4636 := rfl
@[simp] theorem word_16 : instrAt 158=.DIVU .x30 .x30 .x9 := rfl
@[simp] theorem word_17 : instrAt 159=.BLTU .x30 .x16 8 := rfl
@[simp] theorem word_18 : instrAt 160=.ADDI .x30 .x16 0 := rfl
@[simp] theorem word_19 : instrAt 161=.ADD .x30 .x22 .x30 := rfl
@[simp] theorem word_20 : instrAt 162=.ADD .x30 .x20 .x30 := rfl
@[simp] theorem word_21 : instrAt 163=.LBU .x23 .x30 0 := rfl
@[simp] theorem word_22 : instrAt 164=.ADD .x24 .x20 .x22 := rfl
@[simp] theorem word_23 : instrAt 165=.SB .x24 .x23 0 := rfl
@[simp] theorem word_24 : instrAt 166=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_25 : instrAt 167=.JAL .x0 2097108 := rfl
@[simp] theorem word_26 : instrAt 168=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_27 : instrAt 169=.ADDI .x26 .x20 44 := rfl
@[simp] theorem word_28 : instrAt 170=.BEQ .x22 .x16 268 := rfl
@[simp] theorem word_29 : instrAt 171=.ADD .x28 .x27 .x22 := rfl
@[simp] theorem word_30 : instrAt 172=.LBU .x29 .x28 0 := rfl
@[simp] theorem word_31 : instrAt 173=.ANDI .x29 .x29 3 := rfl
@[simp] theorem word_32 : instrAt 174=.SLLI .x29 .x29 6 := rfl
@[simp] theorem word_33 : instrAt 175=.LBU .x30 .x26 0 := rfl
@[simp] theorem word_34 : instrAt 176=.ANDI .x30 .x30 63 := rfl
@[simp] theorem word_35 : instrAt 177=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_36 : instrAt 178=.SB .x26 .x29 0 := rfl
@[simp] theorem word_37 : instrAt 179=.ADDI .x26 .x26 480 := rfl
@[simp] theorem word_38 : instrAt 180=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_39 : instrAt 181=.JAL .x0 2097108 := rfl
@[simp] theorem word_40 : instrAt 182=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_41 : instrAt 183=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_42 : instrAt 184=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_43 : instrAt 185=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_44 : instrAt 186=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_45 : instrAt 187=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_46 : instrAt 188=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_47 : instrAt 189=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_48 : instrAt 190=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_49 : instrAt 191=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_50 : instrAt 192=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_51 : instrAt 193=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_52 : instrAt 194=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_53 : instrAt 195=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_54 : instrAt 196=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_55 : instrAt 197=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_56 : instrAt 198=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_57 : instrAt 199=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_58 : instrAt 200=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_59 : instrAt 201=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_60 : instrAt 202=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_61 : instrAt 203=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_62 : instrAt 204=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_63 : instrAt 205=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_64 : instrAt 206=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_65 : instrAt 207=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_66 : instrAt 208=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_67 : instrAt 209=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_68 : instrAt 210=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_69 : instrAt 211=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_70 : instrAt 212=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_71 : instrAt 213=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_72 : instrAt 214=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_73 : instrAt 215=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_74 : instrAt 216=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_75 : instrAt 217=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_76 : instrAt 218=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_77 : instrAt 219=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_78 : instrAt 220=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_79 : instrAt 221=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_80 : instrAt 222=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_81 : instrAt 223=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_82 : instrAt 224=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_83 : instrAt 225=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_84 : instrAt 226=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_85 : instrAt 227=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_86 : instrAt 228=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_87 : instrAt 229=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_88 : instrAt 230=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_89 : instrAt 231=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_90 : instrAt 232=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_91 : instrAt 233=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_92 : instrAt 234=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_93 : instrAt 235=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_94 : instrAt 236=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_95 : instrAt 237=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_96 : instrAt 238=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_97 : instrAt 239=.ADDI .x0 .x0 0 := rfl
@[simp] theorem word_98 : instrAt 240=.SUB .x11 .x11 .x16 := rfl
@[simp] theorem word_99 : instrAt 241=.ADDI .x22 .x0 0 := rfl

@[simp] theorem se12_435 : signExtend12 435#12=435#64 := by decide
@[simp] theorem se12_480 : signExtend12 480#12=480#64 := by decide
@[simp] theorem se12_63 : signExtend12 63#12=63#64 := by decide
@[simp] theorem compact_branch : pcOf 156+signExtend13 48#13=pcOf 168 := by decide
@[simp] theorem source_branch : pcOf 159+signExtend13 8#13=pcOf 161 := by decide
@[simp] theorem compact_jump : pcOf 167+signExtend21 2097108#21=pcOf 156 := by decide

structure Regs (k L base H : Nat) (s : MachineState) : Prop where
  x5 : s.getReg .x5=1
  x10 : s.getReg .x10=0
  x11 : s.getReg .x11=BitVec.ofNat 64 L
  x16 : s.getReg .x16=BitVec.ofNat 64 k
  x20 : s.getReg .x20=BitVec.ofNat 64 base
  x27 : s.getReg .x27=BitVec.ofNat 64 H
  x18 : s.getReg .x18=BitVec.ofNat 64 (L-k)
  x9 : s.getReg .x9=480
  x7 : s.getReg .x7=BitVec.ofNat 64 ((k+7)/8)

theorem Regs.keep {k L base H : Nat} {s : MachineState} (regs : Regs k L base H s)
    (ts : List Nat)
    (h : ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7] : List Reg).all
      (fun r => !writesAny ts r)=true) : Regs k L base H (run s ts) := by
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨h5,h10,h11,h16,h20,h27,h18,h9,h7⟩ := h
  exact ⟨(run_keeps _ ts s h5).trans regs.x5,(run_keeps _ ts s h10).trans regs.x10,
    (run_keeps _ ts s h11).trans regs.x11,(run_keeps _ ts s h16).trans regs.x16,
    (run_keeps _ ts s h20).trans regs.x20,(run_keeps _ ts s h27).trans regs.x27,
    (run_keeps _ ts s h18).trans regs.x18,(run_keeps _ ts s h9).trans regs.x9,
    (run_keeps _ ts s h7).trans regs.x7⟩

structure Compact (k L base H : Nat) (Q : Proof) (s0 : MachineState) (p : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf 156
  x22 : s.getReg .x22=BitVec.ofNat 64 p
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k))
  bound : p≤L-k
  mem : ∀ a : Word, s.getByte a=
    if base≤a.toNat ∧ a.toNat<base+p then convertedByte k Q (a.toNat-base) else s0.getByte a

end TwoPermutationPrototype.PackedOpening.HeadStream
