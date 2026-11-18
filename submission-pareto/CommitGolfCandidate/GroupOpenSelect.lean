import CommitGolfCandidate.GroupOpenStep
import CommitGolfCandidate.CounterSaltWindows

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank msgWord)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def selectRows (direct : Bool) : List Row :=
  [(747,.ADDI .x7 .x28 (-1)),(748,.SLLI .x7 .x7 4),(749,.BNE .x28 .x0 8)] ++
  (if direct then [(750,.ADDI .x7 .x0 184)] else []) ++
  [(751,.ADD .x7 .x7 .x12),(752,.SLLI .x30 .x6 4),(753,.ADD .x30 .x30 .x22)]
def copyRows : List Row := [(754,.LD .x31 .x7 0),(755,.SD .x30 .x31 0),(756,.LD .x31 .x7 8),(757,.SD .x30 .x31 8)]
def nextRows (last : Bool) : List Row := [(758,.ADDI .x14 .x14 8),(759,.ADDI .x17 .x17 (-1)),(760,.BNE .x17 .x0 8108)] ++
  (if last then [(761,.JAL .x0 2094168)] else [])
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
    (choose s i).pc=address 754 ∧ (choose s i).getReg .x7=readAt i ∧ (choose s i).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+6979325984#64=destAt i := salt_address i
  by_cases zero : rank i.val=0
  · simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,address,out,salts,beq_iff_eq,
      show signExtend12 184#12=184#64 by decide,show signExtend13 8#13=8#64 by decide,dst]
    simpa only [readAt,offAt,if_pos zero] using (show 184#64+1536#64=BitVec.ofNat 64 (1536+184) by decide)
  · have neq : BitVec.ofNat 64 (rank i.val)≠0#64 := mt (rank_zero i).mp zero
    have src := output_address i zero
    change ((BitVec.ofNat 64 (rank i.val)+signExtend12 4095#12) <<< (4:Nat))+1536#64=readAt i at src
    simp at src
    simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,neq,address,out,salts,beq_iff_eq,
      show signExtend13 8#13=8#64 by decide,dst]
    exact src

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

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 754) (r : s.getReg .x7=readAt i)
    (d : s.getReg .x30=destAt i) : legal copyRows s := by
  obtain ⟨a,b,c,e,_⟩:=copy_addresses i
  simp [copyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,r,d,address,a,b,c,e,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide] <;> exact ⟨b,e⟩

theorem copied_mem (s : MachineState) (i : Index) (r : s.getReg .x7=readAt i) (d : s.getReg .x30=destAt i) :
    (copied s).mem=(installed s i).mem := by
  obtain ⟨_,_,_,_,ne⟩:=copy_addresses i
  have ne' : readAt i+8#64≠destAt i:=ne
  simp [copied,walkRows,copyRows,execInstrBr,r,d,installed,MachineState.getMem_setMem_ne ne',mem_of_store,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide]

theorem copied_keeps (s : MachineState) (r : Reg) (ne : r≠.x31) : (copied s).getReg r=s.getReg r := by
  simp [copied,walkRows,copyRows,execInstrBr,Ne.symm ne]

theorem copied_pc (s : MachineState) (pc : s.pc=address 754) : (copied s).pc=address 758 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening
