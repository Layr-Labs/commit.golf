import CommitGolfCandidate.GroupOpenSlot
import CommitGolfCandidate.CounterSaltWindows

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (msgWord sliceByte)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

theorem post_parts (last : Bool) : postRows last=selectRows++copyRows++nextRows last := rfl

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

/-- Words 766-768: source `reply + offset` in x31, destination salt slot in x30. -/
def choose (s : MachineState) := walkRows s selectRows

theorem choose_legal (s : MachineState) (pc : s.pc=address 766) : legal selectRows s := by
  refine ⟨pc,rfl,?_,rfl,?_,rfl,trivial⟩ <;> simp [execInstrBr,pc,address]

theorem choose_keeps (s : MachineState) (r : Reg) (a : r≠.x31) (b : r≠.x30) :
    (choose s).getReg r=s.getReg r := by
  simp [choose,walkRows,selectRows,execInstrBr,Ne.symm a,Ne.symm b]

theorem chosen_memory (s : MachineState) : (choose s).mem=s.mem := by
  simp [choose,walkRows,selectRows,execInstrBr]

theorem off_bounds (i : Index) : offAt i<200 ∧ offAt i%8=0 := by
  have h := (coord i).2.isLt
  unfold offAt sliceByte;split <;> constructor <;> omega

theorem chosen (s : MachineState) (i : Index) (pc : s.pc=address 766)
    (idx : s.getReg .x6=BitVec.ofNat 64 i.val) (off : s.getReg .x31=BitVec.ofNat 64 (offAt i))
    (out : s.getReg .x12=1536) (salts : s.getReg .x22=6979325984) :
    (choose s).pc=address 769 ∧ (choose s).getReg .x31=readAt i ∧ (choose s).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+6979325984#64=destAt i := by
    rw [shl_word,show (6979325984#64 : Word)=BitVec.ofNat 64 6979325984 from rfl,add_word];unfold destAt
    exact congrArg (BitVec.ofNat 64) (by omega)
  refine ⟨?_,?_,?_⟩
  · simp [choose,walkRows,selectRows,execInstrBr,pc,address]
  · simp [choose,walkRows,selectRows,execInstrBr,off,out]
    rw [show (1536#64 : Word)=BitVec.ofNat 64 1536 from rfl,add_word];unfold readAt
    exact congrArg (BitVec.ofNat 64) (by omega)
  · simp [choose,walkRows,selectRows,execInstrBr,idx,salts];exact dst

theorem copy_addresses (i : Index) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (destAt i) 8=true ∧ accessValid (destAt i+8) 8=true ∧ readAt i+8≠destAt i := by
  have hi : i.val<16777216:=i.isLt
  have off := off_bounds i
  unfold readAt destAt
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add,←BitVec.ofNat_add]
  have valid (a : Nat) (al : a%8=0) (room : a+8 ≤ 2^36) : accessValid (BitVec.ofNat 64 a) 8=true := by
    exact Opening.aligned_access a al room
  refine ⟨valid _ (by omega) (by omega),valid _ (by omega) (by omega),
    valid _ (by omega) (by omega),valid _ (by omega) (by omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 6979325984+16*i.val<2^64)] at this
  omega

/-- Words 769-772: copy the 16 salt bytes (scratch x28). -/
def copied (s : MachineState) := walkRows s copyRows
def installed (s : MachineState) (i : Index) :=
  (s.setMem (destAt i) (s.getMem (readAt i))).setMem (destAt i+8) (s.getMem (readAt i+8))

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 769) (r : s.getReg .x31=readAt i)
    (d : s.getReg .x30=destAt i) : legal copyRows s := by
  obtain ⟨a,b,c,e,_⟩:=copy_addresses i
  simp [copyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,r,d,address,a,b,c,e,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide] <;> exact ⟨b,e⟩

theorem copied_mem (s : MachineState) (i : Index) (r : s.getReg .x31=readAt i) (d : s.getReg .x30=destAt i) :
    (copied s).mem=(installed s i).mem := by
  obtain ⟨_,_,_,_,ne⟩:=copy_addresses i
  have ne' : readAt i+8#64≠destAt i:=ne
  simp [copied,walkRows,copyRows,execInstrBr,r,d,installed,MachineState.getMem_setMem_ne ne',mem_of_store,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide]

theorem copied_keeps (s : MachineState) (r : Reg) (ne : r≠.x28) : (copied s).getReg r=s.getReg r := by
  simp [copied,walkRows,copyRows,execInstrBr,Ne.symm ne]

theorem copied_pc (s : MachineState) (pc : s.pc=address 769) : (copied s).pc=address 773 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening
