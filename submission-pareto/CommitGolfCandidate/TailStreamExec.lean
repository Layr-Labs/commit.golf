import CommitGolfCandidate.TailStreamEmit

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open ProofCodec.HeadStreamSeven
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg set_byte_read

def pcOf (t : Nat) : Word := Pack.pcOf (241+t)
def instrAt (t : Nat) : Instr := code.getD t .NOP

class CodeImage (image : Image) : Prop where
  fetched : ∀ (s : MachineState) (t : Nat), t<101 → s.pc=pcOf t →
    fetch image s=some (.base (instrAt t))

@[simp] theorem word_0 : instrAt 0=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_1 : instrAt 1=.ADDI .x26 .x20 44 := rfl
@[simp] theorem word_2 : instrAt 2=.BEQ .x22 .x16 28 := rfl
@[simp] theorem word_3 : instrAt 3=.LBU .x23 .x26 0 := rfl
@[simp] theorem word_4 : instrAt 4=.ADD .x24 .x27 .x22 := rfl
@[simp] theorem word_5 : instrAt 5=.SB .x24 .x23 0 := rfl
@[simp] theorem word_6 : instrAt 6=.ADDI .x26 .x26 480 := rfl
@[simp] theorem word_7 : instrAt 7=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_8 : instrAt 8=.JAL .x0 2097128 := rfl
@[simp] theorem word_9 : instrAt 9=.SUB .x18 .x11 .x16 := rfl
@[simp] theorem word_10 : instrAt 10=.ADDI .x9 .x0 479 := rfl
@[simp] theorem word_11 : instrAt 11=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_12 : instrAt 12=.ADD .x30 .x27 .x16 := rfl
@[simp] theorem word_13 : instrAt 13=.SB .x30 .x0 0 := rfl
@[simp] theorem word_14 : instrAt 14=.SB .x30 .x0 1 := rfl
@[simp] theorem word_15 : instrAt 15=.SB .x30 .x0 2 := rfl
@[simp] theorem word_16 : instrAt 16=.SB .x30 .x0 3 := rfl
@[simp] theorem word_17 : instrAt 17=.SB .x30 .x0 4 := rfl
@[simp] theorem word_18 : instrAt 18=.SB .x30 .x0 5 := rfl
@[simp] theorem word_19 : instrAt 19=.SB .x30 .x0 6 := rfl
@[simp] theorem word_20 : instrAt 20=.ADDI .x7 .x16 7 := rfl
@[simp] theorem word_21 : instrAt 21=.SRLI .x7 .x7 3 := rfl
@[simp] theorem word_22 : instrAt 22=.ADD .x26 .x20 .x18 := rfl
@[simp] theorem word_23 : instrAt 23=.BEQ .x22 .x18 48 := rfl
@[simp] theorem word_24 : instrAt 24=.JAL .x0 8200 := rfl
@[simp] theorem word_25 : instrAt 25=.DIVU .x30 .x30 .x9 := rfl
@[simp] theorem word_26 : instrAt 26=.BLTU .x30 .x16 8 := rfl
@[simp] theorem word_27 : instrAt 27=.ADDI .x30 .x16 0 := rfl
@[simp] theorem word_28 : instrAt 28=.ADD .x30 .x22 .x30 := rfl
@[simp] theorem word_29 : instrAt 29=.ADD .x30 .x20 .x30 := rfl
@[simp] theorem word_30 : instrAt 30=.LBU .x23 .x30 0 := rfl
@[simp] theorem word_31 : instrAt 31=.ADD .x24 .x20 .x22 := rfl
@[simp] theorem word_32 : instrAt 32=.SB .x24 .x23 0 := rfl
@[simp] theorem word_33 : instrAt 33=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_34 : instrAt 34=.JAL .x0 2097108 := rfl
@[simp] theorem word_35 : instrAt 35=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_36 : instrAt 36=.ADD .x28 .x27 .x0 := rfl
@[simp] theorem word_37 : instrAt 37=.BEQ .x22 .x7 244 := rfl
@[simp] theorem word_38 : instrAt 38=.LBU .x23 .x28 0 := rfl
@[simp] theorem word_39 : instrAt 39=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_40 : instrAt 40=.SRLI .x23 .x23 0 := rfl
@[simp] theorem word_41 : instrAt 41=.LBU .x24 .x28 1 := rfl
@[simp] theorem word_42 : instrAt 42=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_43 : instrAt 43=.SLLI .x24 .x24 7 := rfl
@[simp] theorem word_44 : instrAt 44=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_45 : instrAt 45=.SB .x26 .x23 0 := rfl
@[simp] theorem word_46 : instrAt 46=.LBU .x23 .x28 1 := rfl
@[simp] theorem word_47 : instrAt 47=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_48 : instrAt 48=.SRLI .x23 .x23 1 := rfl
@[simp] theorem word_49 : instrAt 49=.LBU .x24 .x28 2 := rfl
@[simp] theorem word_50 : instrAt 50=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_51 : instrAt 51=.SLLI .x24 .x24 6 := rfl
@[simp] theorem word_52 : instrAt 52=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_53 : instrAt 53=.SB .x26 .x23 1 := rfl
@[simp] theorem word_54 : instrAt 54=.LBU .x23 .x28 2 := rfl
@[simp] theorem word_55 : instrAt 55=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_56 : instrAt 56=.SRLI .x23 .x23 2 := rfl
@[simp] theorem word_57 : instrAt 57=.LBU .x24 .x28 3 := rfl
@[simp] theorem word_58 : instrAt 58=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_59 : instrAt 59=.SLLI .x24 .x24 5 := rfl
@[simp] theorem word_60 : instrAt 60=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_61 : instrAt 61=.SB .x26 .x23 2 := rfl
@[simp] theorem word_62 : instrAt 62=.LBU .x23 .x28 3 := rfl
@[simp] theorem word_63 : instrAt 63=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_64 : instrAt 64=.SRLI .x23 .x23 3 := rfl
@[simp] theorem word_65 : instrAt 65=.LBU .x24 .x28 4 := rfl
@[simp] theorem word_66 : instrAt 66=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_67 : instrAt 67=.SLLI .x24 .x24 4 := rfl
@[simp] theorem word_68 : instrAt 68=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_69 : instrAt 69=.SB .x26 .x23 3 := rfl
@[simp] theorem word_70 : instrAt 70=.LBU .x23 .x28 4 := rfl
@[simp] theorem word_71 : instrAt 71=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_72 : instrAt 72=.SRLI .x23 .x23 4 := rfl
@[simp] theorem word_73 : instrAt 73=.LBU .x24 .x28 5 := rfl
@[simp] theorem word_74 : instrAt 74=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_75 : instrAt 75=.SLLI .x24 .x24 3 := rfl
@[simp] theorem word_76 : instrAt 76=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_77 : instrAt 77=.SB .x26 .x23 4 := rfl
@[simp] theorem word_78 : instrAt 78=.LBU .x23 .x28 5 := rfl
@[simp] theorem word_79 : instrAt 79=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_80 : instrAt 80=.SRLI .x23 .x23 5 := rfl
@[simp] theorem word_81 : instrAt 81=.LBU .x24 .x28 6 := rfl
@[simp] theorem word_82 : instrAt 82=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_83 : instrAt 83=.SLLI .x24 .x24 2 := rfl
@[simp] theorem word_84 : instrAt 84=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_85 : instrAt 85=.SB .x26 .x23 5 := rfl
@[simp] theorem word_86 : instrAt 86=.LBU .x23 .x28 6 := rfl
@[simp] theorem word_87 : instrAt 87=.ANDI .x23 .x23 127 := rfl
@[simp] theorem word_88 : instrAt 88=.SRLI .x23 .x23 6 := rfl
@[simp] theorem word_89 : instrAt 89=.LBU .x24 .x28 7 := rfl
@[simp] theorem word_90 : instrAt 90=.ANDI .x24 .x24 127 := rfl
@[simp] theorem word_91 : instrAt 91=.SLLI .x24 .x24 1 := rfl
@[simp] theorem word_92 : instrAt 92=.OR .x23 .x23 .x24 := rfl
@[simp] theorem word_93 : instrAt 93=.SB .x26 .x23 6 := rfl
@[simp] theorem word_94 : instrAt 94=.ADDI .x28 .x28 8 := rfl
@[simp] theorem word_95 : instrAt 95=.ADDI .x26 .x26 7 := rfl
@[simp] theorem word_96 : instrAt 96=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_97 : instrAt 97=.JAL .x0 2096912 := rfl
@[simp] theorem word_98 : instrAt 98=.SRLI .x23 .x16 3 := rfl
@[simp] theorem word_99 : instrAt 99=.SUB .x11 .x11 .x23 := rfl
@[simp] theorem word_100 : instrAt 100=.ECALL := rfl

@[simp] theorem pc_succ (t : Nat) : pcOf t+4#64=pcOf (t+1) := by
  unfold pcOf Pack.pcOf
  apply BitVec.eq_of_toNat_eq
  simp
  omega

@[simp] theorem se12_479 : signExtend12 479#12=479#64 := by decide
@[simp] theorem se12_435 : signExtend12 435#12=435#64 := by decide
@[simp] theorem compact_branch : pcOf 23+signExtend13 48#13=pcOf 35 := by decide
@[simp] theorem source_branch : pcOf 26+signExtend13 8#13=pcOf 28 := by decide
@[simp] theorem compact_jump : pcOf 34+signExtend21 2097108#21=pcOf 23 := by decide

variable {image : Image}

def Runs (image : Image) (a b : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel coins, execute image (steps + fuel) a coins =
    (do let result ← execute image fuel b coins
        return result.charge cycles 0)

theorem Runs.refl (s : MachineState) : Runs image s s 0 0 := by
  intro fuel coins
  simp [Execution.charge]

theorem Runs.trans {a b c : MachineState} {s1 c1 s2 c2 : Nat}
    (first : Runs image a b s1 c1) (second : Runs image b c s2 c2) : Runs image a c (s1 + s2) (c1 + c2) := by
  intro fuel coins
  rw [Nat.add_assoc, first (s2 + fuel) coins, second fuel coins]
  simp [Execution.charge, ← Nat.add_assoc, Nat.add_comm c1 c2]

theorem Runs.cast {a b : MachineState} {s1 c1 s2 c2 : Nat} (run : Runs image a b s1 c1)
    (hs : s1 = s2) (hc : c1 = c2) : Runs image a b s2 c2 := hs ▸ hc ▸ run


def cost (t : Nat) : Nat := instructionCycles (.base (instrAt t))

variable [CodeImage image]

theorem runs_step (s : MachineState) (t : Nat) (ht : t < 101) (pc : s.pc = pcOf t)
    (ord : ordinaryInstr (instrAt t) = true) (valid : memoryArgumentsValid s (instrAt t) = true) :
    Runs image s (execInstrBr s (instrAt t)) 1 (cost t) := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step _ _ _ _ _ _ (CodeImage.fetched s t ht pc) (ordinary_step_eq s _ ord valid)

/-- Run packer words `ts` in order. -/
def run (s : MachineState) (ts : List Nat) : MachineState :=
  ts.foldl (fun state t => execInstrBr state (instrAt t)) s

def PathOK : MachineState → List Nat → Prop
  | _, [] => True
  | s, t :: ts => t < 101 ∧ s.pc = pcOf t ∧ ordinaryInstr (instrAt t) = true ∧
      memoryArgumentsValid s (instrAt t) = true ∧ PathOK (execInstrBr s (instrAt t)) ts

def pathCycles (ts : List Nat) : Nat := (ts.map cost).sum

theorem runs_path : ∀ (ts : List Nat) (s : MachineState), PathOK s ts →
    Runs image s (run s ts) ts.length (pathCycles ts)
  | [], s, _ => by simpa [run, pathCycles] using Runs.refl (image := image) s
  | t :: ts, s, ⟨ht, pc, ord, valid, rest⟩ => by
    have tail := runs_path ts _ rest
    have both := (runs_step (image := image) s t ht pc ord valid).trans tail
    simpa [run, pathCycles, Nat.add_comm] using both


def writesAny (ts : List Nat) (r : Reg) : Bool := ts.any fun t => writesReg (.base (instrAt t)) r

theorem run_keeps (r : Reg) : ∀ (ts : List Nat) (s : MachineState), writesAny ts r = false →
    (run s ts).getReg r = s.getReg r
  | [], s, _ => rfl
  | t :: ts, s, h => by
    simp only [writesAny, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [run, List.foldl_cons]
    exact (run_keeps r ts _ h.2).trans (exec_keeps s _ r h.1)

/-- No store. -/
def loadsOnly : Instr → Bool
  | .SD .. | .SW .. | .SH .. | .SB .. | .CSRS .. => false
  | _ => true

theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem exec_mem (s : MachineState) (i : Instr) (h : loadsOnly i = true) :
    (execInstrBr s i).mem = s.mem := by
  cases i <;> simp only [loadsOnly] at h <;> simp only [execInstrBr] <;> (try split) <;>
    simp [mem_setReg', MachineState.setPC] at *

theorem run_mem : ∀ (ts : List Nat) (s : MachineState), (ts.all fun t => loadsOnly (instrAt t)) = true →
    (run s ts).mem = s.mem
  | [], s, _ => rfl
  | t :: ts, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [run, List.foldl_cons]
    exact (run_mem ts _ h.2).trans (exec_mem s _ h.1)

theorem getByte_of_mem {s t : MachineState} (h : s.mem = t.mem) (a : Word) : s.getByte a = t.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem, h]


structure Regs (k L base H : Nat) (s : MachineState) : Prop where
  x5 : s.getReg .x5=1
  x10 : s.getReg .x10=0
  x11 : s.getReg .x11=BitVec.ofNat 64 L
  x16 : s.getReg .x16=BitVec.ofNat 64 k
  x20 : s.getReg .x20=BitVec.ofNat 64 base
  x27 : s.getReg .x27=BitVec.ofNat 64 H
  x18 : s.getReg .x18=BitVec.ofNat 64 (L-k)
  x9 : s.getReg .x9=479
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
  pc : s.pc=pcOf 23
  x22 : s.getReg .x22=BitVec.ofNat 64 p
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k))
  bound : p≤L-k
  mem : ∀ a : Word, s.getByte a=
    if base≤a.toNat ∧ a.toNat<base+p then convertedByte k Q (a.toNat-base) else s0.getByte a

theorem runs_loop (Inv : Nat → MachineState → Prop) (N : Nat) (st cy : Nat → Nat)
    (body : ∀ j < N, ∀ s, Inv j s → ∃ s', Inv (j + 1) s' ∧ Runs image s s' (st j) (cy j)) (d : Nat) :
    ∀ j s, j + d = N → Inv j s →
      ∃ s', Inv N s' ∧ Runs image s s' (∑ i ∈ Finset.Ico j N, st i) (∑ i ∈ Finset.Ico j N, cy i) := by
  induction d with
  | zero =>
    intro j s h inv
    subst h
    exact ⟨s, inv, by simpa using Runs.refl (image := image) s⟩
  | succ d ih =>
    intro j s h inv
    obtain ⟨s1, inv1, run1⟩ := body j (by omega) s inv
    obtain ⟨s2, inv2, run2⟩ := ih (j + 1) s1 (by omega) inv1
    refine ⟨s2, inv2, ?_⟩
    have hlt : j < N := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt st, Finset.sum_eq_sum_Ico_succ_bot hlt cy]
    exact run1.trans run2

end TwoPermutationPrototype.PackedOpening.TailStream
