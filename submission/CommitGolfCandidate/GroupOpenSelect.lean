import CommitGolfCandidate.GroupOpenStep

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

theorem post_parts (k : Fin 3) (last : Bool) : postRows k last=selectRows k++copyRows++nextRows last := rfl

/-- Rank class of leaf `i` in the K1 offset map: 0 (rank 0), 1 (rank 1), 2 (rank ≥ 2). -/
def kindOf (i : Index) : Fin 3 := if rank i.val=0 then 0 else if rank i.val=1 then 1 else 2
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

theorem kind_cases (i : Index) :
    (rank i.val=0 ∧ kindOf i=0) ∨ (rank i.val=1 ∧ kindOf i=1) ∨ (2≤rank i.val ∧ kindOf i=2) := by
  unfold kindOf
  by_cases z : rank i.val=0
  · exact Or.inl ⟨z,by simp [z]⟩
  · by_cases o : rank i.val=1
    · exact Or.inr (Or.inl ⟨o,by simp [o]⟩)
    · exact Or.inr (Or.inr ⟨by omega,by simp [z,o]⟩)

theorem rank_ult (i : Index) (two : 2≤rank i.val) : BitVec.ult (1 : Word) (BitVec.ofNat 64 (rank i.val))=true := by
  have small : rank i.val<11 := by unfold rank;omega
  simp only [BitVec.ult,BitVec.toNat_ofNat,decide_eq_true_eq]
  change 1<rank i.val%2^64
  rw [Nat.mod_eq_of_lt (by omega)];omega

theorem choose_legal (s : MachineState) (i : Index) (pc : s.pc=address 796)
    (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : s.getReg .x23=1) :
    legal (selectRows (kindOf i)) s := by
  rcases kind_cases i with ⟨r,k⟩|⟨r,k⟩|⟨r,k⟩ <;> rw [k]
  · rw [r] at sub
    simp [selectRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,sub,one,address,
      show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide] <;> decide
  · rw [r] at sub
    simp [selectRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,sub,one,address,
      show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide] <;> decide
  · have lt := rank_ult i r
    rw [←sub,←one] at lt
    simp [selectRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,lt,address,
      show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide] <;> decide

def choose (s : MachineState) (i : Index) := walkRows s (selectRows (kindOf i))

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

theorem choose_keeps (s : MachineState) (i : Index) (r : Reg) (a : r≠.x7) (b : r≠.x30) :
    (choose s i).getReg r=s.getReg r := by
  unfold choose
  rcases kind_cases i with ⟨_,k⟩|⟨_,k⟩|⟨_,k⟩ <;> rw [k] <;> apply rows_preserve <;> intro p h u <;>
    simp [selectRows] at h <;> rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact bne_reg .. | exact bltu_reg .. | simp [execInstrBr,Ne.symm a,Ne.symm b]

theorem chosen_memory (s : MachineState) (i : Index) : (choose s i).mem=s.mem := by
  unfold choose
  rcases kind_cases i with ⟨_,k⟩|⟨_,k⟩|⟨_,k⟩ <;> rw [k] <;> apply rows_memory <;> intro p h u <;>
    simp [selectRows] at h <;> rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact bne_mem .. | exact bltu_mem .. | simp [execInstrBr]

theorem chosen (s : MachineState) (i : Index) (pc : s.pc=address 796)
    (idx : s.getReg .x6=BitVec.ofNat 64 i.val) (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val))
    (one : s.getReg .x23=1) (out : s.getReg .x12=1536) (salts : s.getReg .x22=9126809632) :
    (choose s i).pc=address 805 ∧ (choose s i).getReg .x7=readAt i ∧ (choose s i).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+9126809632#64=destAt i := salt_address i
  rcases kind_cases i with ⟨r,k⟩|⟨r,k⟩|⟨r,k⟩
  · rw [r] at sub
    simp [choose,walkRows,selectRows,k,execInstrBr,pc,idx,sub,one,address,out,salts,
      show signExtend12 0#12=0#64 by decide,show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide,dst]
    simpa only [readAt,offAt,if_pos r] using (show 0#64+1536#64=BitVec.ofNat 64 (1536+0) by decide)
  · rw [r] at sub
    simp [choose,walkRows,selectRows,k,execInstrBr,pc,idx,sub,one,address,out,salts,
      show signExtend12 184#12=184#64 by decide,show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide,dst]
    have e : readAt i=1720#64 := by unfold readAt offAt;rw [if_neg (by omega),if_pos r]
    simp only [e] <;> decide
  · have lt := rank_ult i r
    rw [←sub,←one] at lt
    have src := output_address i r
    change ((BitVec.ofNat 64 (rank i.val)+signExtend12 4095#12) <<< (4:Nat))+1536#64=readAt i at src
    simp at src
    simp [choose,walkRows,selectRows,k,execInstrBr,pc,idx,lt,address,out,salts,
      show signExtend13 8#13=8#64 by decide,show signExtend13 16#13=16#64 by decide,dst]
    simpa [sub] using src

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

def copied (s : MachineState) := walkRows s copyRows
def installed (s : MachineState) (i : Index) :=
  (s.setMem (destAt i) (s.getMem (readAt i))).setMem (destAt i+8) (s.getMem (readAt i+8))

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 805) (r : s.getReg .x7=readAt i)
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

theorem copied_pc (s : MachineState) (pc : s.pc=address 805) : (copied s).pc=address 809 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening
