import CommitGolfCandidate.GroupOpenWholeFlow

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Wide Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg get_reg_set_half
@[local simp] private theorem mem_pc (s : MachineState) (v : Word) : (s.setPC v).mem=s.mem := rfl
@[local simp] private theorem mem_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl

def tag (s : MachineState) (S l : Nat) :=
  foldValue (s.getHalfword (BitVec.ofNat 64 (S+28))) (s.getReg .x10 >>> (2*(l-6)))

def payload (s : MachineState) (i : Index) (l b : Nat) : BitVec 8 :=
  if folded l ∧ 28≤b then (tag s (siblingAddress i l) l).extractLsb' (8*(b-28)) 8
  else s.getByte (BitVec.ofNat 64 (siblingAddress i l+b))

def packRows (l : Nat) : List Instr :=
  [.LHU .x31 .x7 28] ++
  (if l=6 then [.SLLI .x29 .x10 14] else
    [.SRLI .x29 .x10 (BitVec.ofNat 6 (2*(l-6))),.SLLI .x29 .x29 14]) ++
  [.OR .x31 .x31 .x29,.SH .x21 .x31 (BitVec.ofNat 12 (siblingOffset l+28))]

def pack (l : Nat) (s : MachineState) := if folded l then execCode s (packRows l) else s
def packCost (l : Nat) := if folded l then (packRows l).length else 0
def packStart (c l : Nat) := rawStart c (4+l)+(shape c (4+l)).cycles

private theorem pack_code (c : Fin 4) (l : Fin 14) (hl : folded l) :
    Slice (packStart c l) (packRows l) := by revert l;fin_cases c <;> decide +kernel
theorem pack_fit (c : Fin 4) (l : Fin 14) : packStart c l+packCost l<6144 := by revert c l;decide

theorem half_from_words {s u : MachineState} (h : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a))
    (a : Nat) (below : a<proofBase) : u.getHalfword (BitVec.ofNat 64 a)=s.getHalfword (BitVec.ofNat 64 a) := by
  let p:=alignToDword (BitVec.ofNat 64 a)
  have lim : proofBase<2^64 := by decide
  have bound : p.toNat < proofBase := by rw [show p.toNat=_ from align_any a (by omega)];omega
  have word:=h p.toNat bound
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at word
  unfold MachineState.getHalfword
  rw [show u.getMem (alignToDword (BitVec.ofNat 64 a))=_ from word]

theorem byte_from_words {s u : MachineState} (h : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a))
    (a : Nat) (below : a<proofBase) : u.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a) := by
  let p:=alignToDword (BitVec.ofNat 64 a)
  have lim : proofBase<2^64 := by decide
  have bound : p.toNat < proofBase := by rw [show p.toNat=_ from align_any a (by omega)];omega
  have word:=h p.toNat bound
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at word
  unfold MachineState.getByte
  rw [show u.getMem (alignToDword (BitVec.ofNat 64 a))=_ from word]

theorem half_outside (s : MachineState) (t a : Nat) (v : BitVec 16) (even : t%2=0)
    (fit : t+2<2^64) (afit : a<2^64) (away : a<t ∨ t+2≤a) :
    (s.setHalfword (BitVec.ofNat 64 t) v).getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a) := by
  apply ProjectedHalfword.store_outside
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show t<2^64 by omega)];exact even
  · constructor
    · intro e; have := Opening.nat_address_injective afit (by omega) e;omega
    · rw [←word_succ];intro e;have := Opening.nat_address_injective afit (by omega) e;omega

theorem half_below (s : MachineState) (t a : Nat) (v : BitVec 16) (fit : t<2^64)
    (low : a<proofBase) (above : proofBase≤t) :
    (s.setHalfword (BitVec.ofNat 64 t) v).getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a) := by
  rw [set_half_eq,MachineState.getMem_setMem_ne]
  intro e
  have eq:=congrArg BitVec.toNat e
  rw [align_any t fit,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^64 from lt_trans low (by decide : proofBase<2^64))] at eq
  have al : proofBase%8=0 := by decide
  omega

structure PackResult (c l S T : Nat) (s u : MachineState) : Prop where
  run : RunsOpeningBlock s u (packCost l)
  pc : u.pc=pcAt (packStart c l+packCost l)
  mem : u.mem=if folded l then (s.setHalfword (BitVec.ofNat 64 (T+28)) (tag s S l)).mem else s.mem
  regs : ∀ r, r≠.x31 → r≠.x29 → u.getReg r=s.getReg r

theorem pack_result (c : Fin 4) (l : Fin 14) (s : MachineState) (S T : Nat)
    (pc : s.pc=pcAt (packStart c l)) (sr : s.getReg .x7=BitVec.ofNat 64 S) (dr : s.getReg .x21+BitVec.ofNat 64 (siblingOffset l)=BitVec.ofNat 64 T)
    (sa : S%8=0) (even : T%2=0) (sf : S+32≤MEMORY_BYTES) (room : folded l → T+30≤MEMORY_BYTES) :
    PackResult c l S T s (pack l s) := by
  by_cases fold : folded l
  · have high := l.isLt
    have short : 2*(l.val-6)<64 := by omega
    have sw : (BitVec.ofNat 6 (2*(l.val-6))).toNat=2*(l.val-6) := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt short]
    have src : s.getReg .x7+signExtend12 (28#12)=BitVec.ofNat 64 (S+28) := by
      rw [sr,show signExtend12 (28#12)=BitVec.ofNat 64 28 from rfl,←BitVec.ofNat_add]
    have dst : s.getReg .x21+signExtend12 (BitVec.ofNat 12 (siblingOffset l+28))=BitVec.ofNat 64 (T+28) := by
      rw [sign12 _ (by have := sibling_offset_le l (by omega);omega),BitVec.ofNat_add,←BitVec.add_assoc,dr,←BitVec.ofNat_add]
    have ls:=half_access (S+28) (by omega) (by omega)
    have ts:=room fold
    have st:=half_access (T+28) (by omega) (by omega)
    have ready : Ready s (packRows l) := by
      by_cases six : l.val=6 <;> (try rw [six] at dst) <;> simp [packRows,six,Ready,memoryArgumentsValid,memAccess,execInstrBr,src,dst,ls,st]
    have ran:=code_run (packRows l) (packStart c l) s (by have := pack_fit c l;simpa [packCost,fold] using this.le)
      (codeOfSlice (pack_code c l fold)) ready pc
      (by intro op m; by_cases six : l.val=6 <;> simp [packRows,six] at m <;> rcases m with rfl|rfl|rfl|rfl|rfl <;> rfl)
      (by intro t op m;by_cases six : l.val=6 <;> simp [packRows,six] at m <;> rcases m with rfl|rfl|rfl|rfl|rfl <;> rfl)
    refine ⟨by simpa [pack,packCost,fold] using ran,?_,?_,?_⟩
    · by_cases six : l.val=6
      · change (pack l s).pc=_
        simp only [pack,packCost,if_pos fold,packRows,if_pos six]
        change s.pc+4+4+4+4=_
        rw [pc];simp only [BitVec.add_assoc];exact ofNat_step _ 4
      · simp only [pack,packCost,if_pos fold,packRows,if_neg six]
        change s.pc+4+4+4+4+4=_
        rw [pc];simp only [BitVec.add_assoc];exact ofNat_step _ 5
    · simp only [pack,if_pos fold]
      by_cases six : l.val=6 <;> (try rw [six] at dst) <;>
        simp [packRows,six,execCode,execInstrBr,tag,foldValue,src,dst,sw] <;>
        apply half_mem_congr <;> simp
    · intro r a b; simp only [pack,if_pos fold]
      by_cases six : l.val=6 <;> simp [packRows,six,execCode,execInstrBr,Ne.symm a,Ne.symm b]
  · refine ⟨?_,?_,?_,?_⟩
    · simpa only [pack,packCost,if_neg fold] using run_zero s
    · simpa only [pack,packCost,if_neg fold,Nat.add_zero] using pc
    · simp only [pack,if_neg fold]
    · simp [pack,fold]

end TwoPermutationPrototype.GroupedOpening.Whole
