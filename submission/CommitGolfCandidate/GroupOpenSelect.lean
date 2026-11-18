import CommitGolfCandidate.GroupOpenStep
import CommitGolfCandidate.CounterSaltWindows

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank msgWord)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def selectRows (direct : Bool) : List Row :=
  [(747,.SLLI .x7 .x28 4),(748,.BNE .x28 .x0 8)] ++
  (if direct then [(749,.ADDI .x7 .x0 200)] else []) ++
  [(750,.ADD .x7 .x7 .x12),(751,.SLLI .x30 .x6 4),(752,.ADD .x30 .x30 .x22)]
def copyRows : List Row := [(753,.LD .x31 .x7 (-16)),(754,.SD .x30 .x31 0),
  (755,.LD .x31 .x7 (-8)),(756,.SD .x30 .x31 8)]
def nextRows (last : Bool) : List Row := [(757,.ADDI .x14 .x14 8),(758,.ADDI .x17 .x17 (-1)),(759,.BNE .x17 .x0 (-80))] ++
  (if last then [(760,.JAL .x0 8)] else [])
theorem post_parts (direct last : Bool) : postRows direct last=selectRows direct++copyRows++nextRows last := by
  cases direct <;> cases last <;> rfl

theorem legal_append (s : MachineState) (a b : List Row) (head : legal a s) (tail : legal b (walkRows s a)) :
    legal (a++b) s := by
  induction a generalizing s with
  | nil => exact tail
  | cons p a ih =>
    rcases p with ⟨i,op⟩
    exact ⟨head.1,head.2.1,ih _ head.2.2 tail⟩

def Direct (i : Index) := decide (rank i.val=0)
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

theorem rank_zero (i : Index) : BitVec.ofNat 64 (rank i.val)=0#64 ↔ rank i.val=0 := by
  constructor
  · intro h;have e:=congrArg BitVec.toNat h
    have small : rank i.val<2^64 := by unfold rank;omega
    change rank i.val%2^64=0 at e;omega
  · intro h;rw [h]

theorem choose_legal (s : MachineState) (i : Index) (pc : s.pc=address 747)
    (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val)) :
    legal (selectRows (Direct i)) s := by
  by_cases zero : rank i.val=0
  all_goals simp [selectRows,Direct,zero,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,sub,address,
    beq_iff_eq,rank_zero, show signExtend13 8#13=8#64 by decide] <;> decide

def choose (s : MachineState) (i : Index) := walkRows s (selectRows (Direct i))
theorem choose_keeps (s : MachineState) (i : Index) (r : Reg) (a : r≠.x7) (b : r≠.x30) :
    (choose s i).getReg r=s.getReg r := by
  unfold choose selectRows;cases (Direct i) <;> by_cases eq : s.getReg .x28=0#64 <;>
    simp [walkRows,execInstrBr,Ne.symm a,Ne.symm b,eq,beq_iff_eq]

theorem chosen_memory (s : MachineState) (i : Index) : (choose s i).mem=s.mem := by
  unfold choose selectRows;cases Direct i <;> by_cases eq : s.getReg .x28=0#64 <;> simp [walkRows,execInstrBr,eq,beq_iff_eq]

theorem chosen (s : MachineState) (i : Index) (pc : s.pc=address 747)
    (idx : s.getReg .x6=BitVec.ofNat 64 i.val) (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val))
    (out : s.getReg .x12=1536) (salts : s.getReg .x22=6979325984) :
    (choose s i).pc=address 753 ∧ (choose s i).getReg .x7=saltBase i ∧ (choose s i).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+6979325984#64=destAt i := salt_address i
  by_cases zero : rank i.val=0
  · simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,address,out,salts,beq_iff_eq,
      show signExtend13 8#13=8#64 by decide,show signExtend12 200#12=200#64 by decide,dst]
    exact (by simpa only [salt_base_zero i zero] using (show (200#64+1536#64 : Word)=1736#64 by decide))
  · have neq : BitVec.ofNat 64 (rank i.val)≠0#64 := mt (rank_zero i).mp zero
    simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,neq,address,out,salts,beq_iff_eq,
      show signExtend13 8#13=8#64 by decide,dst]
    exact (salt_base_pos i zero).symm

theorem copy_addresses (i : Index) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (destAt i) 8=true ∧ accessValid (destAt i+8) 8=true ∧ readAt i+8≠destAt i := by
  have hi : i.val<16777216:=i.isLt
  have r : rank i.val<11 := by unfold rank;omega
  have off : offAt i<200 ∧ offAt i%8=0 := by unfold offAt;split <;> constructor <;> omega
  unfold readAt destAt
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add,←BitVec.ofNat_add]
  have valid (a : Nat) (al : a%8=0) (room : a+8≤2^36) : accessValid (BitVec.ofNat 64 a) 8=true := by
    exact Opening.aligned_access a al room
  refine ⟨valid _ (by omega) (by omega),valid _ (by omega) (by omega),
    valid _ (by omega) (by omega),valid _ (by omega) (by omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 6979325984+16*i.val<2^64)] at this
  omega

def copied (s : MachineState) := walkRows s copyRows
def installed (s : MachineState) (i : Index) :=
  (s.setMem (destAt i) (s.getMem (readAt i))).setMem (destAt i+8) (s.getMem (readAt i+8))

theorem ld16_run (s : MachineState) (i : Index) (r : s.getReg .x7=saltBase i) :
    execInstrBr s (.LD .x31 .x7 (-16))=(s.setReg .x31 (s.getMem (readAt i))).setPC (s.pc+4) := by
  simp only [execInstrBr, r]
  rw [salt_base_sub16]

theorem ld8_run (s : MachineState) (i : Index) (r : s.getReg .x7=saltBase i) :
    execInstrBr s (.LD .x31 .x7 (-8))=(s.setReg .x31 (s.getMem (readAt i+8))).setPC (s.pc+4) := by
  simp only [execInstrBr, r]
  rw [salt_base_sub8]

theorem sd0_run (s : MachineState) :
    execInstrBr s (.SD .x30 .x31 0)=(s.setMem (s.getReg .x30) (s.getReg .x31)).setPC (s.pc+4) := by
  simp only [execInstrBr]
  rw [show signExtend12 (0:BitVec 12)=0#64 by decide]
  simp

theorem sd8_run (s : MachineState) :
    execInstrBr s (.SD .x30 .x31 8)=(s.setMem (s.getReg .x30+8#64) (s.getReg .x31)).setPC (s.pc+4) := by
  simp only [execInstrBr]
  rw [show signExtend12 (8:BitVec 12)=8#64 by decide]

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 753) (r : s.getReg .x7=saltBase i)
    (d : s.getReg .x30=destAt i) : legal copyRows s := by
  obtain ⟨a,b,c,e,_⟩:=copy_addresses i
  have v1 : memoryArgumentsValid s (.LD .x31 .x7 (-16))=true := by
    simp only [memoryArgumentsValid,memAccess,r,salt_base_sub16,a]
  have v2 : memoryArgumentsValid (execInstrBr s (.LD .x31 .x7 (-16))) (.SD .x30 .x31 0)=true := by
    simp only [memoryArgumentsValid,memAccess,execInstrBr,d,Opening.getReg_setReg,Opening.getReg_setMem,MachineState.getReg_setPC]
    rw [show signExtend12 (0:BitVec 12)=0#64 by decide, BitVec.add_zero]
    exact c
  have v3 : memoryArgumentsValid (execInstrBr (execInstrBr s (.LD .x31 .x7 (-16))) (.SD .x30 .x31 0))
      (.LD .x31 .x7 (-8))=true := by
    simp only [memoryArgumentsValid,memAccess,execInstrBr,r,Opening.getReg_setReg,Opening.getReg_setMem,MachineState.getReg_setPC]
    rw [if_neg (by decide)]
    rw [salt_base_sub8]
    exact b
  have v4 : memoryArgumentsValid (execInstrBr (execInstrBr (execInstrBr s (.LD .x31 .x7 (-16))) (.SD .x30 .x31 0))
      (.LD .x31 .x7 (-8))) (.SD .x30 .x31 8)=true := by
    simp only [memoryArgumentsValid,memAccess,execInstrBr,d,Opening.getReg_setReg,Opening.getReg_setMem,MachineState.getReg_setPC]
    rw [if_neg (by decide)]
    rw [show signExtend12 (8:BitVec 12)=8#64 by decide]
    exact e
  have p1 : (execInstrBr s (.LD .x31 .x7 (-16))).pc=address 754 := by
    rw [ld16_run s i r]; simp only [pc_of_set]; rw [pc]; decide
  have p2 : (execInstrBr (execInstrBr s (.LD .x31 .x7 (-16))) (.SD .x30 .x31 0)).pc=address 755 := by
    rw [ld16_run s i r, sd0_run]; simp only [pc_of_set]; rw [pc]; decide
  have p3 : (execInstrBr (execInstrBr (execInstrBr s (.LD .x31 .x7 (-16))) (.SD .x30 .x31 0))
      (.LD .x31 .x7 (-8))).pc=address 756 := by
    rw [ld16_run s i r, sd0_run, ld8_run _ i (by simp [r])]; simp only [pc_of_set]; rw [pc]; decide
  refine ⟨pc,?_,?_⟩
  · simp only [ordinaryStep,v1,if_true]
  · refine ⟨p1,?_,?_⟩
    · simp only [ordinaryStep,v2,if_true]
    · refine ⟨p2,?_,?_⟩
      · simp only [ordinaryStep,v3,if_true]
      · exact ⟨p3,by simp only [ordinaryStep,v4,if_true],trivial⟩

theorem copied_mem (s : MachineState) (i : Index) (r : s.getReg .x7=saltBase i) (d : s.getReg .x30=destAt i) :
    (copied s).mem=(installed s i).mem := by
  obtain ⟨_,_,_,_,ne⟩:=copy_addresses i
  have ne' : readAt i+8#64≠destAt i:=ne
  simp only [copied,walkRows,copyRows,List.foldl_cons,List.foldl_nil]
  rw [ld16_run s i r]
  rw [sd0_run]
  rw [ld8_run _ i (by simp [r])]
  rw [sd8_run]
  simp [installed,d,MachineState.getMem_setMem_ne ne',mem_of_store,
    show signExtend12 (8:BitVec 12)=8#64 by decide,show signExtend12 (0:BitVec 12)=0#64 by decide]

theorem copied_keeps (s : MachineState) (r : Reg) (ne : r≠.x31) : (copied s).getReg r=s.getReg r := by
  simp [copied,walkRows,copyRows,execInstrBr,Ne.symm ne]

theorem copied_pc (s : MachineState) (pc : s.pc=address 753) : (copied s).pc=address 757 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening
