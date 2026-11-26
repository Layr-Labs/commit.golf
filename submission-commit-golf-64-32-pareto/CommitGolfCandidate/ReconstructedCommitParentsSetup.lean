import CommitGolfCandidate.ReconstructedCommitParentsGroup

namespace CommitGolfCandidate.Reconstruction.CommitParents.Setup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

inductive Op where
  | lui (rd : Reg) (imm : BitVec 20)
  | addi (rd rs : Reg) (imm : BitVec 12)
  | addiw (rd rs : Reg) (imm : BitVec 12)
  | slli (rd rs : Reg) (shift : BitVec 6)

def Op.instr : Op → Instr
  | .lui r i => .LUI r i
  | .addi r s i => .ADDI r s i
  | .addiw r s i => .ADDIW r s i
  | .slli r s i => .SLLI r s i

def Op.dest : Op → Reg
  | .lui r _ | .addi r .. | .addiw r .. | .slli r .. => r

def Op.value (v : Reg → Option Word) : Op → Option Word
  | .lui _ i => some (((i.zeroExtend 32) <<< 12).signExtend 64)
  | .addi _ r i => (fun x => x + signExtend12 i) <$> v r
  | .addiw _ r i => (fun x => (x.truncate 32+(signExtend12 i).truncate 32).signExtend 64) <$> v r
  | .slli _ r i => (fun x : Word => x <<< i.toNat) <$> v r

def knownStep (v : Reg → Option Word) (a : Op) (r : Reg) : Option Word :=
  if r = .x0 then some 0 else if r=a.dest then a.value v else v r

def Agrees (s : MachineState) (v : Reg → Option Word) :=
  ∀ r w, v r=some w → s.getReg r=w

theorem transferred (a : Op) (s : MachineState) (v : Reg → Option Word) (ok : Agrees s v) :
    Agrees (execInstrBr s a.instr) (knownStep v a) := by
  intro r w eq
  unfold knownStep at eq
  by_cases zero : r=.x0
  · subst r;simp at eq;subst w;rfl
  rw [ite_eq_right zero] at eq
  by_cases touched : r=a.dest
  · rw [ite_eq_left touched] at eq
    subst r
    cases a with
    | lui rd im =>
      change rd ≠ .x0 at zero
      simp only [Op.value,Option.some.injEq] at eq
      simp [Op.instr,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq zero,←eq,Op.dest]
    | addi rd rs imm | addiw rd rs imm | slli rd rs imm =>
      change rd ≠ .x0 at zero
      cases hr : v rs with
      | none => simp [Op.value,hr] at eq
      | some val =>
        have sr := ok rs val hr
        simp [Op.value,hr] at eq
        simp [Op.instr,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq zero,sr,←eq,Op.dest]
  · rw [ite_eq_right touched] at eq
    cases a <;> simp only [Op.dest] at touched <;>
      simp [Op.instr,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm touched),ok _ _ eq]

def known (d : Nat) (r : Reg) : Option Word :=
  if r=.x0 ∨ r=.x5 then some 0 else if d<23 ∧ r=.x11 then some 64 else if d<23 ∧ r=.x13 then some 0 else none

def ops : Nat → List Op
  | 0 => [.lui .x18 8192, .addiw .x18 .x18 49, .slli .x18 .x18 7, .lui .x19 16384, .addiw .x19 .x19 97, .slli .x19 .x19 6, .addi .x20 .x0 1, .lui .x22 1]
  | 1 => [.lui .x18 32768, .addiw .x18 .x18 199, .slli .x18 .x18 5, .lui .x19 8192, .addiw .x19 .x19 49, .slli .x19 .x19 7, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 1]
  | 2 => [.lui .x18 8192, .addiw .x18 .x18 51, .slli .x18 .x18 7, .lui .x19 32768, .addiw .x19 .x19 199, .slli .x19 .x19 5, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 2]
  | 3 => [.lui .x18 32768, .addiw .x18 .x18 213, .slli .x18 .x18 5, .lui .x19 8192, .addiw .x19 .x19 51, .slli .x19 .x19 7, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 3]
  | 4 => [.lui .x18 16384, .addiw .x18 .x18 115, .slli .x18 .x18 6, .lui .x19 32768, .addiw .x19 .x19 213, .slli .x19 .x19 5, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 4]
  | 5 => [.lui .x18 32768, .addiw .x18 .x18 263, .slli .x18 .x18 5, .lui .x19 16384, .addiw .x19 .x19 115, .slli .x19 .x19 6, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 5]
  | 6 => [.lui .x18 4096, .addiw .x18 .x18 41, .slli .x18 .x18 8, .lui .x19 32768, .addiw .x19 .x19 263, .slli .x19 .x19 5, .addi .x20 .x0 1, .lui .x22 1, .addi .x17 .x0 6]
  | 7 => [.lui .x18 262145, .slli .x18 .x18 2, .addi .x18 .x18 2336, .lui .x19 4096, .addiw .x19 .x19 41, .slli .x19 .x19 8, .addi .x20 .x0 1, .lui .x22 1, .addi .x23 .x0 8, .addi .x17 .x0 7]
  | 8 => [.lui .x18 16384, .addiw .x18 .x18 357, .slli .x18 .x18 6, .lui .x19 262145, .slli .x19 .x19 2, .addi .x19 .x19 2336, .addi .x20 .x0 1, .lui .x22 1, .addi .x23 .x0 9, .addi .x21 .x0 211, .slli .x21 .x21 32]
  | 9 => [.lui .x18 32768, .addiw .x18 .x18 1227, .slli .x18 .x18 5, .lui .x19 16384, .addiw .x19 .x19 357, .slli .x19 .x19 6, .addi .x20 .x0 1, .lui .x22 1, .addi .x23 .x0 10, .addi .x21 .x0 211, .slli .x21 .x21 32]
  | 10 => [.lui .x18 8192, .addiw .x18 .x18 563, .slli .x18 .x18 7, .lui .x19 32768, .addiw .x19 .x19 1227, .slli .x19 .x19 5, .addi .x20 .x0 2, .lui .x22 1, .addi .x23 .x0 11, .addi .x21 .x0 1325, .slli .x21 .x21 29]
  | 11 => [.lui .x18 32769, .addiw .x18 .x18 205, .slli .x18 .x18 5, .lui .x19 8192, .addiw .x19 .x19 563, .slli .x19 .x19 7, .addi .x20 .x0 4, .lui .x22 1, .addi .x23 .x0 12, .addi .x21 .x0 1325, .slli .x21 .x21 29]
  | 12 => [.lui .x18 16385, .addiw .x18 .x18 103, .slli .x18 .x18 6, .lui .x19 32769, .addiw .x19 .x19 205, .slli .x19 .x19 5, .addi .x20 .x0 8, .lui .x22 1, .addi .x23 .x0 13, .addi .x21 .x0 1325, .slli .x21 .x21 29]
  | 13 => [.lui .x18 32772, .addiw .x18 .x18 207, .slli .x18 .x18 5, .lui .x19 16385, .addiw .x19 .x19 103, .slli .x19 .x19 6, .addi .x20 .x0 16, .lui .x22 1, .addi .x23 .x0 14, .addi .x21 .x0 1677, .slli .x21 .x21 29]
  | 14 => [.lui .x18 2049, .addiw .x18 .x18 2061, .slli .x18 .x18 9, .lui .x19 32772, .addiw .x19 .x19 207, .slli .x19 .x19 5, .addi .x20 .x0 32, .lui .x22 1, .addi .x23 .x0 15, .addi .x21 .x0 1677, .slli .x21 .x21 29]
  | 15 => [.lui .x18 32784, .addiw .x18 .x18 209, .slli .x18 .x18 5, .lui .x19 2049, .addiw .x19 .x19 2061, .slli .x19 .x19 9, .addi .x20 .x0 64, .lui .x22 1, .addi .x23 .x0 16, .addi .x21 .x0 137, .slli .x21 .x21 33]
  | 16 => [.lui .x18 16400, .addiw .x18 .x18 105, .slli .x18 .x18 6, .lui .x19 32784, .addiw .x19 .x19 209, .slli .x19 .x19 5, .addi .x20 .x0 128, .lui .x22 1, .addi .x23 .x0 17, .addi .x21 .x0 1491, .slli .x21 .x21 30]
  | 17 => [.lui .x18 32832, .addiw .x18 .x18 211, .slli .x18 .x18 5, .lui .x19 16400, .addiw .x19 .x19 105, .slli .x19 .x19 6, .addi .x20 .x0 256, .lui .x22 1, .addi .x23 .x0 18, .addi .x21 .x0 1491, .slli .x21 .x21 30]
  | 18 => [.lui .x18 8224, .addiw .x18 .x18 53, .slli .x18 .x18 7, .lui .x19 32832, .addiw .x19 .x19 211, .slli .x19 .x19 5, .addi .x20 .x0 512, .lui .x22 1, .addi .x23 .x0 19, .addi .x21 .x0 1677, .slli .x21 .x21 31]
  | 19 => [.lui .x18 33024, .addiw .x18 .x18 213, .slli .x18 .x18 5, .lui .x19 8224, .addiw .x19 .x19 53, .slli .x19 .x19 7, .addi .x20 .x0 1024, .lui .x22 1, .addi .x21 .x0 1491, .slli .x21 .x21 32]
  | 20 => [.lui .x18 16640, .addiw .x18 .x18 107, .slli .x18 .x18 6, .lui .x19 33024, .addiw .x19 .x19 213, .slli .x19 .x19 5, .addi .x20 .x0 1, .slli .x20 .x20 11, .lui .x22 1, .lui .x21 335]
  | 21 => [.lui .x18 33792, .addiw .x18 .x18 215, .slli .x18 .x18 5, .lui .x19 16640, .addiw .x19 .x19 107, .slli .x19 .x19 6, .lui .x20 1, .lui .x22 1, .lui .x21 348]
  | 22 => [.lui .x18 4352, .addiw .x18 .x18 27, .slli .x18 .x18 8, .lui .x19 33792, .addiw .x19 .x19 215, .slli .x19 .x19 5, .lui .x20 2, .lui .x22 1, .lui .x21 364]
  | 23 => [.addi .x11 .x0 64, .addi .x13 .x0 0, .lui .x18 36864, .addiw .x18 .x18 217, .slli .x18 .x18 5, .lui .x19 4352, .addiw .x19 .x19 27, .slli .x19 .x19 8, .lui .x20 4, .lui .x22 1, .lui .x21 380]
  | _ => []

def begin (d : Nat) := Image.levelStart d - (ops d).length

private def baseOp : Option Instruction → Option Instr
  | some (.base i) => some i
  | _ => none

private theorem code : ∀ d : Fin 24, ((ops d).zipIdx).all (fun p =>
    baseOp (decodeInstruction (Image.readAt (begin d+p.2))) == some p.1.instr) = true := by decide

def Verified (pc : Nat) (ops : List Op) :=
  ∀ j : Fin ops.length, ∀ s : MachineState, s.pc=CommitBlocks.addr (pc+j.val) →
    fetch CommitSetup.im s=some (.base ops[j.val].instr)

theorem verified (d : Fin 24) : Verified (begin d) (ops d) := by
  intro j s pc
  have member : ((ops d)[j.val],j.val) ∈ (ops d).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem j.isLt)
  have word := beq_iff_eq.1 (List.all_eq_true.1 (code d) _ member)
  have lim : ∀ e : Fin 24, begin e+(ops e).length ≤ 150132 := by decide
  have small : begin d+j.val < 150132 := by have := lim d;have := j.isLt;omega
  change baseOp (decodeInstruction (Image.readAt (begin d+j.val)))=some (ops d)[j.val].instr at word
  rw [Image.readAt,dif_pos small] at word
  apply CommitSetup.fetch_at ⟨_,small⟩ _ _ s pc
  generalize h : decodeInstruction (Artifact.commitCode.get 32 ⟨_,small⟩) = x at word ⊢
  cases x <;> simp_all [baseOp]
  rename_i instr
  cases instr <;> simp_all [baseOp]

def after (s : MachineState) (as : List Op) := as.foldl (fun t a => execInstrBr t a.instr) s

theorem run (o : Oracle) (s : MachineState) (pc : Nat) (as : List Op)
    (v : Reg→Option Word) (matchRegs : Agrees s v) (start : s.pc=CommitBlocks.addr pc) (f : Verified pc as) :
    let t := after s as
    Segment o CommitSetup.im as.length s t ∧ t.mem=s.mem ∧ t.pc=CommitBlocks.addr (pc+as.length) ∧
      Agrees t (as.foldl knownStep v) := by
  induction as generalizing s pc v with
  | nil => exact ⟨empty ..,rfl,by simpa [after] using start,matchRegs⟩
  | cons a as ih =>
    let b := execInstrBr s a.instr
    have ins := f 0 s (by simpa using start)
    have sg : Segment o CommitSetup.im 1 s b := plain o CommitSetup.im s b (.base a.instr) ins (by cases a <;> rfl)
    have eq : b.pc=CommitBlocks.addr (pc+1) := by
      rw [CommitBlocks.addr_next,←start];cases a <;> rfl
    have bm : b.mem=s.mem := by
      cases a with
      | lui r _ | addi r _ _ | addiw r _ _ | slli r _ _ => cases r <;> rfl
    have ft : Verified (pc+1) as := by
      intro j t pos
      have key := f ⟨j.val+1,by simp⟩ t (by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using pos)
      exact key
    obtain ⟨sg',mem,pos,kept⟩ := ih b (pc+1) (knownStep v a) (transferred a s v matchRegs) eq ft
    exact ⟨by simpa only [after,b,List.foldl_cons,List.length_cons,Nat.one_add,Nat.succ_eq_add_one] using compose sg sg',
      mem.trans bm,by simpa [after,b,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pos,kept⟩

def certificate (d : Fin 24) :=
  let v := (ops d).foldl knownStep (known d)
  v .x5=some 0 ∧ v .x11=some 64 ∧ v .x13=some 0 ∧
    (width d = 240 → v .x17=some (BitVec.ofNat 64 d)) ∧
    (modulus d ≠ 0 → v .x21=some (BitVec.ofNat 64 (modulus d))) ∧
    (width d < 240 → modulus d=0 → v .x21=some (BitVec.ofNat 64 (narrowMarker d))) ∧
    (modulus (d.val+1) ≠ 0 → v .x23=some (BitVec.ofNat 64 (d.val+1))) ∧
    v .x22=some 4096 ∧ v .x18=some (BitVec.ofNat 64 (srcCentre d (2^d.val) 0)) ∧
    v .x19=some (BitVec.ofNat 64 (dstCentre d (2^d.val) 0)) ∧
    v .x20=some (BitVec.ofNat 64 (2^d.val/Image.unroll d))

theorem start_level (o : Oracle) (s : MachineState) (d : Fin 24)
    (pc : s.pc=CommitBlocks.addr (begin d)) (kind : s.getReg .x5=0)
    (regular : d.val < 23 → s.getReg .x11=64 ∧ s.getReg .x13=0) :
    let t := after s (ops d)
    Segment o CommitSetup.im (ops d).length s t ∧ t.mem=s.mem ∧ Cursor d (2^d.val) 0 t ∧
    t.getReg .x20=BitVec.ofNat 64 (2^d.val/Image.unroll d) := by
  have compatible : Agrees s (known d) := by
    intro r w h
    unfold known at h
    split_ifs at h with hz ha hb
    · rcases hz with rfl|rfl <;> simp_all [MachineState.getReg]
    · obtain ⟨lt,rfl⟩ := ha;simp_all
    · obtain ⟨lt,rfl⟩ := hb;simp_all
  obtain ⟨sg,mem,p,kept⟩ := run o s (begin d) (ops d) (known d) compatible pc (verified d)
  have cert : ∀ e : Fin 24, certificate e := by unfold certificate;decide
  have finish : ∀ e : Fin 24, begin e+(ops e).length=Image.start e 0 := by decide
  obtain ⟨h5,h11,h13,h17,hm,hn,hl,h22,h18,h19,h20⟩ := cert d
  exact ⟨sg,mem,⟨p.trans (congrArg CommitBlocks.addr (finish d)),
    ⟨⟨kept _ _ h5,kept _ _ h11,kept _ _ h13⟩,⟨fun x=>kept _ _ (h17 x),fun x=>kept _ _ (hm x),fun x y=>kept _ _ (hn x y)⟩,
    fun x=>kept _ _ (hl x)⟩,kept _ _ h22,kept _ _ h18,kept _ _ h19⟩,kept _ _ h20⟩

end CommitGolfCandidate.Reconstruction.CommitParents.Setup
