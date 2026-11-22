import CommitGolfCandidate.Layout2Steps

/-! Layout 2 opener: the first record's entry (header at words 15..17, the jump at 18 and the entry stub). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase bodyWord bodyLen tailWord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem jump_one : address 18+signExtend21 (jumpTo 18 5071)=address 5071 := by decide
theorem jump_two : address 5072+signExtend21 (jumpTo 5072 4099)=address 4099 := by decide

/-! Generic `jal x0` and `addi` effects with the offset as a variable: the kernel never evaluates a concrete
offset (unfolding `execInstrBr` on a concrete negative `jal` offset is very expensive for the kernel). -/
theorem jal0_mem (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).mem=u.mem := by
  simp only [execInstrBr]; rw [mem_of_set, mem_of_reg]
theorem jal0_reg (u : MachineState) (off : BitVec 21) (r : Reg) : (execInstrBr u (.JAL .x0 off)).getReg r=u.getReg r := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp
theorem jal0_pc (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).pc=u.pc+signExtend21 off := by
  simp only [execInstrBr]; rfl
theorem addi_mem (u : MachineState) (rd rs : Reg) (imm : BitVec 12) : (execInstrBr u (.ADDI rd rs imm)).mem=u.mem := by
  simp only [execInstrBr]; rw [mem_of_set, mem_of_reg]
theorem addi_pc (u : MachineState) (rd rs : Reg) (imm : BitVec 12) : (execInstrBr u (.ADDI rd rs imm)).pc=u.pc+4 := by
  simp only [execInstrBr]; rfl
theorem addi_other (u : MachineState) (rd rs : Reg) (imm : BitVec 12) (r : Reg) (h : r ≠ rd) :
    (execInstrBr u (.ADDI rd rs imm)).getReg r=u.getReg r := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp [Ne.symm h]
theorem addi_self (u : MachineState) (rd rs : Reg) (imm : BitVec 12) (h : rd ≠ .x0) :
    (execInstrBr u (.ADDI rd rs imm)).getReg rd=u.getReg rs+signExtend12 imm := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp [h]

/-- Word 18 and the entry stub: `jal <5071>; addi s2,s8,584; jal <4099>`. -/
theorem jump_step (st : MachineState) (pc : st.pc=address 18)
    (slots : st.getReg .x24=BitVec.ofNat 64 groupSlots) :
    RunsOpeningBlock st (walkRows st jumpRows) 3 ∧ (walkRows st jumpRows).pc=address 4099 ∧
      (walkRows st jumpRows).getReg .x18=BitVec.ofNat 64 (groupSlots+584) ∧
      (walkRows st jumpRows).mem=st.mem ∧
      (∀ r, r ≠ .x18 → (walkRows st jumpRows).getReg r=st.getReg r) := by
  have whole : walkRows st jumpRows=execInstrBr (execInstrBr (execInstrBr st (.JAL .x0 (jumpTo 18 5071)))
      (.ADDI .x18 .x24 584)) (.JAL .x0 (jumpTo 5072 4099)) := by
    simp only [walkRows, jumpRows, List.foldl_cons, List.foldl_nil]
  have p1 : (execInstrBr st (.JAL .x0 (jumpTo 18 5071))).pc=address 5071 := by rw [jal0_pc, pc, jump_one]
  have p2 : (execInstrBr (execInstrBr st (.JAL .x0 (jumpTo 18 5071))) (.ADDI .x18 .x24 584)).pc=address 5072 := by
    rw [addi_pc, p1, address_succ]
  have valid : legal jumpRows st := by
    simp only [jumpRows, legal]
    exact ⟨pc, rfl, p1, rfl, p2, rfl, trivial⟩
  refine ⟨rows_block _ _ valid jump_present 3 rfl rfl, ?_, ?_, ?_, ?_⟩
  · rw [whole, jal0_pc, p2, jump_two]
  · rw [whole, jal0_reg, addi_self _ _ _ _ (by decide), jal0_reg, slots,
      show signExtend12 (584 : BitVec 12)=BitVec.ofNat 64 584 from rfl, ← BitVec.ofNat_add]
  · rw [whole, jal0_mem, addi_mem, jal0_mem]
  · intro r h; rw [whole, jal0_reg, addi_other _ _ _ _ _ h, jal0_reg]

/-- The first record from word 15: header, jump, entry stub; then the phase-0 body. -/
theorem first_step (st : MachineState) (pos : Nat) (pc : st.pc=address 15)
    (idx : st.getReg .x8=BitVec.ofNat 64 indicesBase)
    (val : st.getMem (BitVec.ofNat 64 indicesBase)=BitVec.ofNat 64 pos) (small : pos<16777216)
    (nonce : st.getReg .x22=BitVec.ofNat 64 nonceBase) (slots : st.getReg .x24=BitVec.ofNat 64 groupSlots) :
    RunsOpeningBlock st (walkRows st firstRows) 6 ∧ (walkRows st firstRows).pc=address (bodyWord 0) ∧
      (walkRows st firstRows).getReg .x6=BitVec.ofNat 64 pos ∧
      (walkRows st firstRows).getReg .x7=BitVec.ofNat 64 (nonceBase+16*pos) ∧
      (walkRows st firstRows).getReg .x18=BitVec.ofNat 64 (groupSlots+584) ∧
      (walkRows st firstRows).mem=st.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x18 → (walkRows st firstRows).getReg r=st.getReg r) := by
  have al : indicesBase%8=0 := by decide
  have fit : indicesBase+8 ≤ MEMORY_BYTES := by decide
  obtain ⟨r1, p1, x6, x7, m1, k1⟩ := hdr_at_step 15 first_hdr_present st indicesBase pos pc idx al fit val small nonce
  let h := walkRows st (hdrRowsAt 15)
  obtain ⟨r2, p2, x18, m2, k2⟩ := jump_step h p1 ((k1 .x24 (by decide) (by decide)).trans slots)
  have whole : walkRows st firstRows=walkRows h jumpRows := by unfold firstRows; rw [walk_join]
  rw [whole]
  refine ⟨r1.next r2, p2, ?_, ?_, x18, by rw [m2, m1], ?_⟩
  · rw [k2 .x6 (by decide)]; exact x6
  · rw [k2 .x7 (by decide)]; exact x7
  · intro r a b c; rw [k2 r c, k1 r a b]

end TwoPermutationPrototype.GroupedOpening.Layout2
