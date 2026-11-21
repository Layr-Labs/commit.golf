import CommitGolfCandidate.GroupOpenStep

/-! Salt rows of the first pass (804..808): the destination `16 i + x22` from `x3 = 16 i`, then a two-dword
copy from the reply address `x28 = readAt i` that the table entry supplied, for every rank. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

theorem post_parts (last : Bool) : postRows last=selectRows++copyRows++nextRows last := rfl

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

/-- The table's salt source is the K1 reply address of the salt of `i`. -/
theorem tab_s_read (i : Index) : BitVec.ofNat 64 (tabS (i.val%4096))=readAt i := by
  unfold tabS tabOff readAt offAt rank
  congr 1

theorem choose_legal (s : MachineState) (i : Index) (pc : s.pc=address 804) :
    legal selectRows s := legal_of_chain _ _ (by decide) (by simp [selectRows,pcChain,execInstrBr,pc,address])

def choose (s : MachineState) (_i : Index) := walkRows s selectRows

theorem rows_preserve (rows : List Row) (s : MachineState) (r : Reg)
    (each : ∀ p∈rows, ∀ st : MachineState, (execInstrBr st p.2).getReg r=st.getReg r) :
    (walkRows s rows).getReg r=s.getReg r := by
  induction rows generalizing s with
  | nil => unfold walkRows;rfl
  | cons p rest ih => unfold walkRows;exact (ih (execInstrBr s p.2) (fun t h => each t (List.mem_cons_of_mem _ h))).trans (each p (by simp) s)

theorem rows_memory (rows : List Row) (s : MachineState)
    (each : ∀ p∈rows, ∀ st : MachineState, (execInstrBr st p.2).mem=st.mem) :
    (walkRows s rows).mem=s.mem := by
  induction rows generalizing s with
  | nil => unfold walkRows;rfl
  | cons p rest ih => unfold walkRows;exact (ih (execInstrBr s p.2) (fun t h => each t (List.mem_cons_of_mem _ h))).trans (each p (by simp) s)

theorem bne_reg (u : MachineState) (a b r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BNE a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

theorem bltu_reg (u : MachineState) (a b r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BLTU a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

theorem bne_mem (u : MachineState) (a b : Reg) (imm : BitVec 13) : (execInstrBr u (.BNE a b imm)).mem=u.mem := by
  simp only [execInstrBr];split <;> rfl

theorem bltu_mem (u : MachineState) (a b : Reg) (imm : BitVec 13) : (execInstrBr u (.BLTU a b imm)).mem=u.mem := by
  simp only [execInstrBr];split <;> rfl

theorem beq_mem (u : MachineState) (a b : Reg) (imm : BitVec 13) : (execInstrBr u (.BEQ a b imm)).mem=u.mem := by
  simp only [execInstrBr];split <;> rfl

theorem jal_mem (u : MachineState) (a : Reg) (imm : BitVec 21) : (execInstrBr u (.JAL a imm)).mem=u.mem := by
  simp [execInstrBr]

theorem choose_keeps (s : MachineState) (i : Index) (r : Reg) (_a : r≠.x7) (b : r≠.x30) :
    (choose s i).getReg r=s.getReg r := by
  simp [choose,selectRows,walkRows,execInstrBr,Ne.symm b]

theorem chosen_memory (s : MachineState) (i : Index) : (choose s i).mem=s.mem := by
  simp [choose,selectRows,walkRows,execInstrBr]

def copySource (s : MachineState) (_i : Index) : Word := s.getReg .x28

theorem chosen (s : MachineState) (i : Index) (pc : s.pc=address 804)
    (x3 : s.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat)) (src : s.getReg .x28=readAt i)
    (salts : s.getReg .x22=9126809632) :
    (choose s i).pc=address 805 ∧ copySource (choose s i) i=readAt i ∧ (choose s i).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+9126809632#64=destAt i := salt_address i
  refine ⟨?_,?_,?_⟩
  · simp [choose,selectRows,walkRows,execInstrBr,pc,address]
  · simp [choose,selectRows,walkRows,execInstrBr,copySource,src]
  · simp [choose,selectRows,walkRows,execInstrBr,x3,salts,dst]

theorem copy_addresses (i : Index) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (destAt i) 8=true ∧ accessValid (destAt i+8) 8=true ∧ readAt i+8≠destAt i := by
  have hi : i.val<16777216:=i.isLt
  have r : rank i.val<11 := by unfold rank;omega
  have off : offAt i<200 ∧ offAt i%8=0 := by unfold offAt;split_ifs <;> constructor <;> omega
  unfold readAt destAt
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add,←BitVec.ofNat_add]
  have valid (a : Nat) (al : a%8=0) (room : a+8≤2^36) : accessValid (BitVec.ofNat 64 a) 8=true := by
    exact Opening.aligned_access a al room
  refine ⟨valid _ (by omega) (by omega),valid _ (by omega) (by omega),
    valid _ (by omega) (by omega),valid _ (by omega) (by omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 9126809632+16*i.val<2^64)] at this
  omega

def copied (s : MachineState) (_i : Index) := walkRows s copyRows
def installed (s : MachineState) (i : Index) :=
  (s.setMem (destAt i) (s.getMem (readAt i))).setMem (destAt i+8) (s.getMem (readAt i+8))

private theorem source_next (s : MachineState) (i : Index) (r : copySource s i=readAt i) :
    s.getReg .x28+signExtend12 8#12=readAt i+8 := by
  unfold copySource at r
  rw [r]; rfl

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 805) (r : copySource s i=readAt i)
    (d : s.getReg .x30=destAt i) : legal copyRows s := by
  obtain ⟨a,b,c,e,_⟩:=copy_addresses i
  have r0 : s.getReg .x28=readAt i := r
  have rn := source_next s i r
  simp [copyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,d,address,a,b,c,e,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide,r0,rn]
  all_goals first | exact ⟨b,e⟩ | decide

theorem copied_mem (s : MachineState) (i : Index) (r : copySource s i=readAt i) (d : s.getReg .x30=destAt i) :
    (copied s i).mem=(installed s i).mem := by
  obtain ⟨_,_,_,_,ne⟩:=copy_addresses i
  have ne' : readAt i+8#64≠destAt i:=ne
  have r0 : s.getReg .x28=readAt i := r
  have rn := source_next s i r
  simp [copied,walkRows,copyRows,execInstrBr,d,installed,MachineState.getMem_setMem_ne ne',mem_of_store,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide,r0,rn]

theorem copied_keeps (s : MachineState) (i : Index) (r : Reg) (ne : r≠.x31) : (copied s i).getReg r=s.getReg r := by
  simp [copied,walkRows,copyRows,execInstrBr,Ne.symm ne]

theorem copied_pc (s : MachineState) (i : Index) (pc : s.pc=address 805) : (copied s i).pc=address 809 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening
