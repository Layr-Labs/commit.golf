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
    show signExtend21 2840#21=2840#64 by decide]

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

theorem layout_sem (s : MachineState) (pc : s.pc=address 0) (nz : s.getReg .x16≠0#64) :
    walkRows s layoutRows=(setupPrefix s 15).setPC (address 725) := by
  let before:=setupPrefix s 3
  have here : before.pc=address 3 := by
    simp [before,setupPrefix,setupInstructions,execInstrBr,pc,address,beq_iff_eq,nz]
  have jump : execInstrBr before (.JAL .x0 2840)=before.setPC (address 713) := by
    change before.setPC (before.pc+signExtend21 2840)=_;rw [here];rfl
  have first : layoutRows.map Prod.snd=setupInstructions.take 3++[.JAL .x0 2840]++tailOps := rfl
  have original : setupInstructions.take 15=setupInstructions.take 3++tailOps := rfl
  rw [instructions_of_rows,first,setupPrefix,original]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact (congrArg (List.foldl execInstrBr · tailOps) jump).trans (moved_tail before)

theorem config_ok (s : MachineState) (pc : s.pc=address 725) : legal configRows s := by
  simp [configRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address]

theorem config_frame (s : MachineState) (pc : s.pc=address 725) (p : Positions)
    (b : Base s p) (salt : s.getReg .x22=9126809632) (base : s.getReg .x26=4096)
    (shift : s.getReg .x25=BitVec.ofNat 64 (8*p.card)) (nz : 0<p.card) :
    let t:=walkRows s configRows
    t.pc=address 733 ∧ t.mem=s.mem ∧ Base t p ∧ Registers t 0 p.card := by
  let t:=walkRows s configRows
  have keep (k : Reg) (h : k ∉ ([.x10,.x12,.x11,.x13,.x5,.x14,.x17,.x25,.x29] : List Reg)) : t.getReg k=s.getReg k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := h
    simp [t,configRows,walkRows,execInstrBr,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,
      Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9]
  refine ⟨?_,?_,?_,?_⟩
  · simp [walkRows,configRows,execInstrBr,pc,address]
  · simp [walkRows,configRows,execInstrBr]
  · exact ⟨(keep _ (by decide)).trans b.indices,(keep _ (by decide)).trans b.heap,(keep _ (by decide)).trans b.count,
      (keep _ (by decide)).trans b.leaves,(keep _ (by decide)).trans b.start,(keep _ (by decide)).trans b.dest,
      (keep _ (by decide)).trans b.mark,(keep _ (by decide)).trans b.slots,
      (keep _ (by decide)).trans b.capLeaves⟩
  · constructor <;> simp [walkRows,configRows,execInstrBr,b.indices,b.count,salt,base,indexAt,countWord,indicesBase,
      trapdoorBase,trapdoorBytes,LENGTH,LOG_LENGTH,signExtend12,shift,show p.card≠0 by omega] <;>
      first | rfl | (rw [← BitVec.ofNat_add]; try rfl)

def keyCopy (s : MachineState) := ((s.setMem 1032 (s.getMem 9126809640)).setMem 1040 (s.getMem 9126809648)).setMem 1048 (s.getMem 9126809656)

theorem key_ok (s : MachineState) (p : Positions) (pc : s.pc=address 733) (r : Registers s 0 p.card) :
    legal keyRows s := by
  simp [keyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,r.salt,r.input,pc,address,signExtend12] <;> decide

theorem key_frame (s : MachineState) (p : Positions) (pc : s.pc=address 733) (r : Registers s 0 p.card) :
    let t:=walkRows s keyRows
    t.pc=address 739 ∧ t.mem=(keyCopy s).mem ∧ ∀ k, k≠.x31 → t.getReg k=s.getReg k := by
  refine ⟨?_,?_,?_⟩
  · simp [walkRows,keyRows,execInstrBr,pc,address]
  · simp [walkRows,keyRows,execInstrBr,mem_of_store,keyCopy,r.input,r.salt,signExtend12,
      MachineState.getMem_setMem_ne (by decide : (9126809648#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (9126809656#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (9126809656#64)≠1040#64)]
  · intro k ne;simp [walkRows,keyRows,execInstrBr,Ne.symm ne]

theorem mark_ok (s : MachineState) (pc : s.pc=address 739) : legal markRows s := by
  simp [markRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address]
  all_goals decide

theorem mark_frame (s : MachineState) (pc : s.pc=address 739) (x26 : s.getReg .x26=4096) :
    let t:=walkRows s markRows
    t.pc=address 740 ∧ t.mem=s.mem ∧ t.getReg .x4=BitVec.ofNat 64 (2^64-1) ∧ t.getReg .x3=374 ∧
      t.getReg .x2=4352 ∧ ∀ k, k≠.x4 → k≠.x3 → k≠.x2 → t.getReg k=s.getReg k := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [walkRows,markRows,execInstrBr,pc,address]
    all_goals decide
  · -- symbolic offsets: with the concrete `jal` offsets the kernel recurses too deeply
    have jm (s : MachineState) (offset : BitVec 21) : (execInstrBr s (.JAL .x0 offset)).mem=s.mem := by
      simp [execInstrBr]
    have a4 (s : MachineState) (imm : BitVec 12) : (execInstrBr s (.ADDI .x4 .x0 imm)).mem=s.mem := by
      simp [execInstrBr]
    have a3 (s : MachineState) (imm : BitVec 12) : (execInstrBr s (.ADDI .x3 .x0 imm)).mem=s.mem := by
      simp [execInstrBr]
    have a2 (s : MachineState) (imm : BitVec 12) : (execInstrBr s (.ADDI .x2 .x26 imm)).mem=s.mem := by
      simp [execInstrBr]
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 60)) (.ADDI .x4 .x0 (-1)))
      (.ADDI .x3 .x0 374)) (.ADDI .x2 .x26 256)) (.JAL .x0 2097084)).mem=s.mem
    rw [jm,a2,a3,a4,jm]
  · simp [walkRows,markRows,execInstrBr]
    all_goals decide
  · simp [walkRows,markRows,execInstrBr]
    all_goals decide
  · simp [walkRows,markRows,execInstrBr,x26]
    all_goals decide
  · intro k n4 n3 n2;simp [walkRows,markRows,execInstrBr,Ne.symm n4,Ne.symm n3,Ne.symm n2]

theorem low_zero (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (low : w<1024) :
    memoryView (actual.initialState .opening (td,p)) w=0 := by
  change (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (8*w))=_
  rw [initial_input_word actual .opening (td,p) (8*w) (by omega)]
  have zero (j : Nat) (hj : j<8) : inputByte actual .opening (td,p) (8*w+j)=0 := by
    have lo : ¬actual.layout.trapdoor≤8*w+j := by change ¬4294971424≤_;omega
    have ix : ¬actual.layout.indices≤8*w+j := by change ¬9395245088≤_;omega
    have img : (actual.image .opening).data=[]:=rfl
    simp [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,lo,ix,img]
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
