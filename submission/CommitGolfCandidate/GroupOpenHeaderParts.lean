import CommitGolfCandidate.GroupOpenHeaderSpec

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

theorem header_fetch : presentRows headerRows := by
  have raw : ∀ i : Fin headerRows.length, let r:=headerRows[i]; r.1<896 ∧
    (openingImage.code[r.1]?).bind Opening.decodeBase=some r.2 := by decide +kernel
  intro p hp;obtain ⟨j,hj,eq⟩:=List.mem_iff_getElem.mp hp;subst p
  intro st pc;exact packed_fetch_base _ _ _ (raw ⟨j,hj⟩).1 pc (raw ⟨j,hj⟩).2

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set open_zero
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg

theorem layout_ok (s : MachineState) (pc : s.pc=address 0) (nz : s.getReg .x16≠0#64) :
    legal layoutRows s := by
  simp [layoutRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address,beq_iff_eq,nz,
    show signExtend13 2844#13=2844#64 by decide]

private def tailOps := setupInstructions.drop 3

private def linear : Instr → Bool
  | .ADDI .. | .ADD .. | .SLLI .. | .LUI .. => true
  | _ => false

private theorem assign_at_pc (s : MachineState) (r : Reg) (v p q : Word) :
    (((s.setPC p).setReg r v).setPC q)=((s.setReg r v).setPC q) := by cases r <;> rfl

private theorem linear_one (s : MachineState) (p : Word) (op : Instr) (h : linear op=true) :
    execInstrBr (s.setPC p) op=(execInstrBr s op).setPC (p+4) := by
  cases op <;> simp only [linear] at h <;> first | contradiction | skip
  all_goals simp only [execInstrBr,MachineState.getReg_setPC,pc_of_set,assign_at_pc]
  all_goals rfl

private theorem moved (s : MachineState) (p : Word) (ops : List Instr) (plain : ops.all linear=true) :
    ops.foldl execInstrBr (s.setPC p)=(ops.foldl execInstrBr s).setPC (p+BitVec.ofNat 64 (4*ops.length)) := by
  induction ops generalizing s p with
  | nil => simp
  | cons op rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at plain
    simp only [List.foldl_cons,linear_one _ _ _ plain.1,ih _ _ plain.2,List.length_cons,Nat.mul_add,BitVec.ofNat_add]
    congr 1
    rw [BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 (4*rest.length))];rfl

private theorem moved_tail (s : MachineState) :
    tailOps.foldl execInstrBr (s.setPC (address 713))=(tailOps.foldl execInstrBr s).setPC (address 725) :=
  moved s (address 713) tailOps (by decide)

private theorem instructions_of_rows (s : MachineState) (rows : List Row) :
    walkRows s rows=(rows.map Prod.snd).foldl execInstrBr s := by
  induction rows generalizing s with
  | nil => rfl
  | cons row tail ih => exact ih (execInstrBr s row.2)

private theorem setpc_twice (t : MachineState) (p q : Word) : (t.setPC p).setPC q=t.setPC q := rfl

theorem layout_sem (s : MachineState) (pc : s.pc=address 0) (nz : s.getReg .x16≠0#64) :
    walkRows s layoutRows=(setupPrefix s 15).setPC (address 725) := by
  let before:=setupPrefix s 2
  have here : before.pc=address 2 := by
    simp [before,setupPrefix,setupInstructions,execInstrBr,pc,address]
  have x16 : before.getReg .x16=s.getReg .x16 := by
    simp [before,setupPrefix,setupInstructions,execInstrBr]
  have jump : execInstrBr before (.BNE .x16 .x0 2844)=before.setPC (address 713) := by
    have yes : (before.getReg .x16 != before.getReg .x0)=true := by simp [x16,nz,open_zero]
    simp only [execInstrBr,yes,ite_true,here]
    exact congrArg before.setPC (by decide : address 2+signExtend13 2844=address 713)
  have fall : execInstrBr before (.BEQ .x16 .x0 2828)=before.setPC (address 3) := by
    have no : (before.getReg .x16 == before.getReg .x0)=false := by simp [x16,nz,open_zero]
    simp only [execInstrBr,no,Bool.false_eq_true,ite_false,here]
    exact congrArg before.setPC (by decide : address 2+4=address 3)
  have first : layoutRows.map Prod.snd=setupInstructions.take 2++[.BNE .x16 .x0 2844]++tailOps := rfl
  have original : setupInstructions.take 15=setupInstructions.take 2++[.BEQ .x16 .x0 2828]++tailOps := rfl
  rw [instructions_of_rows,first,setupPrefix,original]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change tailOps.foldl execInstrBr (execInstrBr before _)=(tailOps.foldl execInstrBr (execInstrBr before _)).setPC _
  rw [jump,fall,moved_tail,moved before (address 3) tailOps (by decide)]
  exact (setpc_twice _ _ _).symm

theorem config_ok (s : MachineState) (pc : s.pc=address 725) : legal configRows s := by
  simp [configRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address]

theorem config_frame (s : MachineState) (pc : s.pc=address 725) (p : Positions)
    (b : Base s p) (salt : s.getReg .x22=9126809632) (base : s.getReg .x26=4096)
    (shift : s.getReg .x25=BitVec.ofNat 64 (8*p.card)) (nz : 0<p.card) (selector : s.getReg .x5=0) :
    let t:=walkRows s configRows
    t.pc=address 733 ∧ t.mem=s.mem ∧ Base t p ∧ Registers t 0 p.card ∧ t.getReg .x10=1024 ∧ t.getReg .x1=65535 ∧
      t.getReg .x2=s.getReg .x2 := by
  let t:=walkRows s configRows
  have keep (k : Reg) (h : k ∉ ([.x10,.x12,.x11,.x13,.x4,.x14,.x17,.x25,.x1] : List Reg)) : t.getReg k=s.getReg k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := h
    simp [t,configRows,walkRows,execInstrBr,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,
      Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9]
  refine ⟨?_,?_,?_,?_,?_,?_,keep _ (by decide)⟩
  · simp [walkRows,configRows,execInstrBr,pc,address]
  · simp [walkRows,configRows,execInstrBr]
  · exact ⟨(keep _ (by decide)).trans b.indices,(keep _ (by decide)).trans b.heap,(keep _ (by decide)).trans b.count,
      (keep _ (by decide)).trans b.leaves,(keep _ (by decide)).trans b.start,(keep _ (by decide)).trans b.dest,
      (keep _ (by decide)).trans b.mark,(keep _ (by decide)).trans b.slots,
      (keep _ (by decide)).trans b.capLeaves⟩
  · constructor <;> simp [walkRows,configRows,execInstrBr,b.indices,b.count,salt,base,indexAt,countWord,indicesBase,
      trapdoorBase,trapdoorBytes,LENGTH,LOG_LENGTH,signExtend12,shift,selector,show p.card≠0 by omega] <;>
      first | rfl | (rw [← BitVec.ofNat_add]; try rfl)
  · simp [walkRows,configRows,execInstrBr,signExtend12]
    all_goals first | rfl | decide
  · simp [walkRows,configRows,execInstrBr]
    all_goals first | rfl | decide

def keyCopy (s : MachineState) := ((s.setMem 1032 (s.getMem 9126809640)).setMem 1040 (s.getMem 9126809648)).setMem 1048 (s.getMem 9126809656)

theorem key_ok (s : MachineState) (p : Positions) (pc : s.pc=address 733) (r : Registers s 0 p.card)
    (x10 : s.getReg .x10=1024) :
    legal keyRows s := by
  simp [keyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,r.salt,x10,pc,address,signExtend12] <;> decide

theorem key_frame (s : MachineState) (p : Positions) (pc : s.pc=address 733) (r : Registers s 0 p.card)
    (x10 : s.getReg .x10=1024) :
    let t:=walkRows s keyRows
    t.pc=address 739 ∧ t.mem=(keyCopy s).mem ∧ ∀ k, k≠.x31 → t.getReg k=s.getReg k := by
  refine ⟨?_,?_,?_⟩
  · simp [walkRows,keyRows,execInstrBr,pc,address]
  · simp [walkRows,keyRows,execInstrBr,mem_of_store,keyCopy,x10,r.salt,signExtend12,
      MachineState.getMem_setMem_ne (by decide : (9126809648#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (9126809656#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (9126809656#64)≠1040#64)]
  · intro k ne;simp [walkRows,keyRows,execInstrBr,Ne.symm ne]

theorem mark_ok (s : MachineState) (pc : s.pc=address 739) : legal markRows s := by
  simp [markRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address]
  all_goals decide

theorem mark_frame (s : MachineState) (pc : s.pc=address 739) :
    let t:=walkRows s markRows
    t.pc=address 3077 ∧ t.mem=s.mem ∧ ∀ k, t.getReg k=s.getReg k := by
  refine ⟨?_,?_,?_⟩
  · simp [walkRows,markRows,execInstrBr,pc,address]
    all_goals decide
  · simp [walkRows,markRows,execInstrBr]
  · intro k;simp [walkRows,markRows,execInstrBr]

theorem low_zero (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (low : w<1024) :
    memoryView (actual.initialState .opening (td,p)) w=0 := by
  change (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (8*w))=_
  rw [initial_input_word actual .opening (td,p) (8*w) (by omega)]
  have zero (j : Nat) (hj : j<8) : inputByte actual .opening (td,p) (8*w+j)=0 := by
    have lo : ¬actual.layout.trapdoor≤8*w+j := by change ¬4294971424≤_;omega
    have ix : ¬actual.layout.indices≤8*w+j := by change ¬9395245088≤_;omega
    have nd : ¬dataBase (actual.image .opening)≤8*w+j := by rw [actual_data_base]; simp only [tableBase]; omega
    simp [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,lo,ix,nd]
  rw [Finset.sum_eq_zero (fun j hj => by rw [zero _ (Finset.mem_range.mp hj)];simp)];rfl

theorem key_words (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (j : Fin 3) :
    (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (9126809640+8*j.val)) =
      (keyOf td).extractLsb' (64*j.val) 64 := by
  have hj:=j.isLt
  rw [←word_at _ _ (by omega),show 9126809640+8*j.val=trapdoorBase+(4831838216+8*j.val) by unfold trapdoorBase LENGTH LOG_LENGTH;omega,
    input_trapdoor_slice actual actual_layout td p _ _ (by change _≤5100273664;omega)]
  unfold keyOf
  rw [nested_slice _ (by omega : 64*j.val+64≤192)]
  congr 1 <;> omega


theorem original_base (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let t := setupPrefix (actual.initialState .opening (td,p)) 15
    Base t p ∧ t.getReg .x22=9126809632 ∧ t.getReg .x26=4096 ∧
      t.mem=(actual.initialState .opening (td,p)).mem := by
  let initial := actual.initialState .opening (td,p)
  have trapPointer : initial.getReg .x12 = BitVec.ofNat 64 trapdoorBase :=
    congrArg (BitVec.ofNat 64) actual_layout.trapdoor
  obtain ⟨proofStart, dest, ordinal, heap, count, size, nonce, slots, one, shift, marks, capLeaves, memory⟩ :=
    setup_registers initial
  refine ⟨opening_first_boundary actual actual_layout td p nz, ?_, ?_, ?_⟩
  · rw [nonce,trapPointer,← BitVec.ofNat_add]; rfl
  · simpa [Opening.markBase] using marks
  · exact memory

theorem base_at_pc (p : Positions) (s : MachineState) (pc : Word) (b : Base s p) : Base (s.setPC pc) p :=
  ⟨b.indices,b.heap,b.count,b.leaves,b.start,b.dest,b.mark,b.slots,b.capLeaves⟩

end TwoPermutationPrototype.GroupedOpening
