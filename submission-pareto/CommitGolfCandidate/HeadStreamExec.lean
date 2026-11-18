import CommitGolfCandidate.TwoPermutationPackedOpeningPack
import CommitGolfCandidate.HeadStreamCodec

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStream
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
@[simp] theorem word_15 : instrAt 157=.ADDI .x30 .x22 435 := rfl
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
@[simp] theorem word_27 : instrAt 169=.BEQ .x22 .x7 228 := rfl
@[simp] theorem word_28 : instrAt 170=.SLLI .x28 .x22 3 := rfl
@[simp] theorem word_29 : instrAt 171=.ADD .x28 .x27 .x28 := rfl
@[simp] theorem word_30 : instrAt 172=.LBU .x23 .x28 0 := rfl
@[simp] theorem word_31 : instrAt 173=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_32 : instrAt 174=.LBU .x24 .x28 1 := rfl
@[simp] theorem word_33 : instrAt 175=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_34 : instrAt 176=.SRLI .x29 .x23 0 := rfl
@[simp] theorem word_35 : instrAt 177=.SLLI .x30 .x24 7 := rfl
@[simp] theorem word_36 : instrAt 178=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_37 : instrAt 179=.SB .x26 .x29 0 := rfl
@[simp] theorem word_38 : instrAt 180=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_39 : instrAt 181=.LBU .x24 .x28 2 := rfl
@[simp] theorem word_40 : instrAt 182=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_41 : instrAt 183=.SRLI .x29 .x23 1 := rfl
@[simp] theorem word_42 : instrAt 184=.SLLI .x30 .x24 6 := rfl
@[simp] theorem word_43 : instrAt 185=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_44 : instrAt 186=.SB .x26 .x29 1 := rfl
@[simp] theorem word_45 : instrAt 187=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_46 : instrAt 188=.LBU .x24 .x28 3 := rfl
@[simp] theorem word_47 : instrAt 189=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_48 : instrAt 190=.SRLI .x29 .x23 2 := rfl
@[simp] theorem word_49 : instrAt 191=.SLLI .x30 .x24 5 := rfl
@[simp] theorem word_50 : instrAt 192=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_51 : instrAt 193=.SB .x26 .x29 2 := rfl
@[simp] theorem word_52 : instrAt 194=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_53 : instrAt 195=.LBU .x24 .x28 4 := rfl
@[simp] theorem word_54 : instrAt 196=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_55 : instrAt 197=.SRLI .x29 .x23 3 := rfl
@[simp] theorem word_56 : instrAt 198=.SLLI .x30 .x24 4 := rfl
@[simp] theorem word_57 : instrAt 199=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_58 : instrAt 200=.SB .x26 .x29 3 := rfl
@[simp] theorem word_59 : instrAt 201=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_60 : instrAt 202=.LBU .x24 .x28 5 := rfl
@[simp] theorem word_61 : instrAt 203=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_62 : instrAt 204=.SRLI .x29 .x23 4 := rfl
@[simp] theorem word_63 : instrAt 205=.SLLI .x30 .x24 3 := rfl
@[simp] theorem word_64 : instrAt 206=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_65 : instrAt 207=.SB .x26 .x29 4 := rfl
@[simp] theorem word_66 : instrAt 208=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_67 : instrAt 209=.LBU .x24 .x28 6 := rfl
@[simp] theorem word_68 : instrAt 210=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_69 : instrAt 211=.SRLI .x29 .x23 5 := rfl
@[simp] theorem word_70 : instrAt 212=.SLLI .x30 .x24 2 := rfl
@[simp] theorem word_71 : instrAt 213=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_72 : instrAt 214=.SB .x26 .x29 5 := rfl
@[simp] theorem word_73 : instrAt 215=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_74 : instrAt 216=.LBU .x24 .x28 7 := rfl
@[simp] theorem word_75 : instrAt 217=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_76 : instrAt 218=.SRLI .x29 .x23 6 := rfl
@[simp] theorem word_77 : instrAt 219=.SLLI .x30 .x24 1 := rfl
@[simp] theorem word_78 : instrAt 220=.OR .x29 .x29 .x30 := rfl
@[simp] theorem word_79 : instrAt 221=.SB .x26 .x29 6 := rfl
@[simp] theorem word_80 : instrAt 222=.ADDI .x23 .x24 0 := rfl
@[simp] theorem word_81 : instrAt 223=.ADDI .x26 .x26 7 := rfl
@[simp] theorem word_82 : instrAt 224=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_83 : instrAt 225=.JAL .x0 2096928 := rfl
@[simp] theorem word_84 : instrAt 226=.SRLI .x7 .x16 3 := rfl
@[simp] theorem word_85 : instrAt 227=.SUB .x11 .x11 .x7 := rfl
@[simp] theorem word_86 : instrAt 228=.ECALL := rfl

@[simp] theorem se12_435 : signExtend12 435#12=435#64 := by decide
@[simp] theorem se12_480 : signExtend12 480#12=480#64 := by decide
@[simp] theorem se12_127 : signExtend12 127#12=127#64 := by decide
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

def copyLow : List Nat := [156,157,158,159,161,162,163,164,165,166,167]
def copyHigh : List Nat := [156,157,158,159,160,161,162,163,164,165,166,167]

def copySteps (k p : Nat) : Nat := if p<480*k-435 then 11 else 12
def copyCycles (k p : Nat) : Nat := if p<480*k-435 then 14 else 15

set_option maxHeartbeats 1000000 in
theorem compact_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (p : Nat)
    (inv : Compact k L base H Q s0 p s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (room : base+2^34≤2^36) (inside : p<L-k)
    (source : ∀ j<L, s0.getByte (BitVec.ofNat 64 (base+j))=Q.getD j 0) :
    ∃ s', Compact k L base H Q s0 (p+1) s' ∧ Runs s s' (copySteps k p) (copyCycles k p) := by
  have regs := inv.regs
  have bounds := compact_source_bounds k L p records inside
  have ne : BitVec.ofNat 64 p≠BitVec.ofNat 64 (L-k) := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have load : s.getByte (BitVec.ofNat 64 (base+compactSource k p))=Q.getD (compactSource k p) 0 := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    exact source _ bounds.2
  have value : (Q.getD (compactSource k p) 0)=convertedByte k Q p := by
    rw [convertedByte,len,if_pos inside]
  have finish (ts : List Nat) (ok : PathOK s ts)
      (keep : ([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7] : List Reg).all
        (fun r => !writesAny ts r)=true)
      (pc : (run s ts).pc=pcOf 156)
      (next : (run s ts).getReg .x22=BitVec.ofNat 64 (p+1))
      (out : (run s ts).getReg .x26=BitVec.ofNat 64 (base+(L-k)))
      (mem : ∀ a, (run s ts).getByte a=
        if a=BitVec.ofNat 64 (base+p) then Q.getD (compactSource k p) 0 else s.getByte a) :
      Compact k L base H Q s0 (p+1) (run s ts) :=
    ⟨regs.keep ts keep,pc,next,out,by omega,
      extend_region _ _ base p (convertedByte k Q) s0.getByte _ (by omega) inv.mem mem value⟩
  by_cases low : (p+435)/480<k
  · have src : compactSource k p=p+(p+435)/480 := by
      unfold compactSource;rw [Nat.min_eq_right (by omega)]
    have ok : PathOK s copyLow := by
      simp (disch := omega) [PathOK,copyLow,code,execInstrBr,inv.pc,inv.x22,regs.x18,regs.x16,
        regs.x9,regs.x20,ne,ordinaryInstr,memoryArgumentsValid,memAccess,w_add,w_divu,
        ult_ofNat,low]
      constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
    have pc : (run s copyLow).pc=pcOf 156 := by
      simp (disch := omega) [run,copyLow,code,execInstrBr,inv.pc,inv.x22,regs.x18,regs.x16,
        regs.x9,regs.x20,ne,w_add,w_divu,ult_ofNat,low]
    have next : (run s copyLow).getReg .x22=BitVec.ofNat 64 (p+1) := by
      simp (disch := omega) [run,copyLow,execInstrBr,inv.x22,regs.x18,regs.x16,regs.x9,ne,
        w_add,w_divu,ult_ofNat,low]
    have out : (run s copyLow).getReg .x26=BitVec.ofNat 64 (base+(L-k)) :=
      (run_keeps _ copyLow s (by decide)).trans inv.x26
    have mem : ∀ a, (run s copyLow).getByte a=
        if a=BitVec.ofNat 64 (base+p) then Q.getD (compactSource k p) 0 else s.getByte a := by
      intro a
      simpa (disch := omega) [run,copyLow,code,execInstrBr,inv.x22,regs.x9,regs.x20,
        regs.x18,regs.x16,ne,ult_ofNat,low,w_add,
        w_divu,←src,load,setWidth_byte] using
        (set_byte_read s (BitVec.ofNat 64 (base+p)) a (Q.getD (compactSource k p) 0))
    refine ⟨_,finish copyLow ok (by decide) pc next out mem,(runs_path _ s ok).cast ?_ ?_⟩
    · have threshold : p<480*k-435 := by omega
      simp only [copySteps,if_pos threshold];rfl
    · have threshold : p<480*k-435 := by omega
      simp only [copyCycles,if_pos threshold]
      decide
  · have src : compactSource k p=p+k := by
      unfold compactSource;rw [Nat.min_eq_left (by omega)]
    have ok : PathOK s copyHigh := by
      simp (disch := omega) [PathOK,copyHigh,code,execInstrBr,inv.pc,inv.x22,regs.x18,regs.x16,
        regs.x9,regs.x20,ne,ordinaryInstr,memoryArgumentsValid,memAccess,w_add,w_divu,
        ult_ofNat,low]
      constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
    have pc : (run s copyHigh).pc=pcOf 156 := by
      simp (disch := omega) [run,copyHigh,code,execInstrBr,inv.pc,inv.x22,regs.x18,regs.x16,
        regs.x9,regs.x20,ne,w_add,w_divu,ult_ofNat,low]
    have next : (run s copyHigh).getReg .x22=BitVec.ofNat 64 (p+1) := by
      simp (disch := omega) [run,copyHigh,execInstrBr,inv.x22,regs.x18,regs.x16,regs.x9,ne,
        w_add,w_divu,ult_ofNat,low]
    have out : (run s copyHigh).getReg .x26=BitVec.ofNat 64 (base+(L-k)) :=
      (run_keeps _ copyHigh s (by decide)).trans inv.x26
    have mem : ∀ a, (run s copyHigh).getByte a=
        if a=BitVec.ofNat 64 (base+p) then Q.getD (compactSource k p) 0 else s.getByte a := by
      intro a
      simpa (disch := omega) [run,copyHigh,code,execInstrBr,inv.x22,regs.x9,regs.x16,regs.x20,
        regs.x18,ne,ult_ofNat,low,w_divu,w_add,←src,load,setWidth_byte] using
        (set_byte_read s (BitVec.ofNat 64 (base+p)) a (Q.getD (compactSource k p) 0))
    refine ⟨_,finish copyHigh ok (by decide) pc next out mem,(runs_path _ s ok).cast ?_ ?_⟩
    · have threshold : ¬p<480*k-435 := by omega
      simp only [copySteps,if_neg threshold];rfl
    · have threshold : ¬p<480*k-435 := by omega
      simp only [copyCycles,if_neg threshold]
      decide

theorem copy_steps_sum (k N : Nat) :
    ∑ p ∈ Finset.range N, copySteps k p=12*N-min N (480*k-435) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold copySteps
    split_ifs <;> omega

theorem copy_cycles_sum (k N : Nat) :
    ∑ p ∈ Finset.range N, copyCycles k p=15*N-min N (480*k-435) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold copyCycles
    split_ifs <;> omega

end TwoPermutationPrototype.PackedOpening.HeadStream
