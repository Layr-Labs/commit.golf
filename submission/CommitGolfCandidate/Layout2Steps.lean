import CommitGolfCandidate.Layout2Loop
import RiscvZkvm.Rv64.Logic.MemRegionWrite

/-! Fused opener: the effect of the loop code after the phase writers (per-phase tail with the latch, exit stubs),
each as a legal row walk or a `RunsOpeningBlock` with its register, memory and byte effects. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase)
open CommitGolfCandidate.Layout2Phase2 (bodyLen)
set_option maxRecDepth 16000
set_option maxHeartbeats 3200000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg open_zero

theorem rows_block (st : MachineState) (rows : List Row) (valid : legal rows st) (code : presentRows rows) (n : Nat)
    (len : rows.length=n) (cost : price rows=n) : RunsOpeningBlock st (walkRows st rows) n := by
  intro fuel coins
  have h := walk_rows_run st rows valid code fuel coins
  rw [len, cost] at h
  exact h

theorem shift_four (pos : Nat) (small : pos<16777216) :
    BitVec.ofNat 64 nonceBase+BitVec.ofNat 64 pos <<< 4=BitVec.ofNat 64 (nonceBase+16*pos) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  unfold nonceBase trapdoorBase LENGTH LOG_LENGTH
  norm_num
  omega

private theorem z12 : signExtend12 0#12=0#64 := by decide
private theorem e12 : signExtend12 8#12=8#64 := by decide

private theorem half_node (pos : Nat) (small : pos<16777216) :
    BitVec.ofNat 64 (512+pos/32768) >>> 1=BitVec.ofNat 64 (256+pos/65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

private theorem mark_address (g : Nat) (small : g<512) :
    4096#64+BitVec.ofNat 64 g=BitVec.ofNat 64 (Opening.markBase+g) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Opening.markBase]
  norm_num
  try omega

/-- A byte store sets exactly its own byte. -/
theorem set_byte_read (s : MachineState) (a q : Word) (v : Byte) :
    (s.setByte a v).getByte q=if q=a then v else s.getByte q := by
  by_cases eq : q=a
  · subst q
    simp only [ite_true, MachineState.setByte, MachineState.getByte, MachineState.getMem_setMem_eq]
    exact extractByte_replaceByte_same _ ⟨_, byteOffset_lt_8⟩ _
  · rw [if_neg eq]
    unfold MachineState.setByte MachineState.getByte
    by_cases same : alignToDword q=alignToDword a
    · rw [same, MachineState.getMem_setMem_eq]
      apply extractByte_replaceByte_diff _ _ byteOffset_lt_8 byteOffset_lt_8
      intro e
      exact eq (by rw [← alignToDword_add_byteOffset q, same, e, alignToDword_add_byteOffset])
    · rw [MachineState.getMem_setMem_ne same]

/-- A byte store leaves every other dword. -/
theorem set_byte_mem (s : MachineState) (a q : Word) (v : Byte) (h : q ≠ alignToDword a) :
    (s.setByte a v).getMem q=s.getMem q := by
  unfold MachineState.setByte; exact MachineState.getMem_setMem_ne h

private theorem index_ne (j k : Nat) (hk : k ≤ 16777216) (hj : j<k) :
    (BitVec.ofNat 64 (indicesBase+8*(j+1))=BitVec.ofNat 64 (indicesBase+8*k)) ↔ j+1=k := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    unfold indicesBase trapdoorBase trapdoorBytes LENGTH LOG_LENGTH at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro e; rw [e]

private theorem tail_branch (p : Nat) (hp : p<3) :
    address (ftailWord p+5)+signExtend13 (branchTo (ftailWord p+5) (fphaseWord (p+1)))=address (fphaseWord (p+1)) ∧
    address (ftailWord p+5)+4=address (fexitWord p) := by
  revert p; decide

private theorem beq_branch : address 5176+signExtend13 (branchTo 5176 5178)=address (fexitWord 3) ∧
    address 5176+4=address 5177 := by decide

private theorem jal_back : address 5177+signExtend21 (jumpTo 5177 4097)=address (fphaseWord 0) := by decide

private theorem one_byte : (1#64 : Word).truncate 8=1#8 := by decide
@[local simp] private theorem reg_byte8 (t : MachineState) (q : Word) (v : Byte) (r : Reg) :
    (t.setByte q v).getReg r=t.getReg r := rfl
private theorem mem_of_set_byte (s : MachineState) (a : Word) (v : Byte) :
    (s.setByte a v).mem=fun w => if w==alignToDword a then replaceByte (s.mem (alignToDword a)) (byteOffset a) v else s.mem w :=
  rfl

theorem jal_any_mem (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).mem=u.mem := by
  simp only [execInstrBr]; rw [mem_of_set, mem_of_reg]
theorem jal_any_reg (u : MachineState) (off : BitVec 21) (r : Reg) : (execInstrBr u (.JAL .x0 off)).getReg r=u.getReg r := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp
theorem jal_any_pc (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).pc=u.pc+signExtend21 off := by
  simp only [execInstrBr]; rfl

theorem beq_reg (u : MachineState) (a b : Reg) (imm : BitVec 13) (r : Reg) :
    (execInstrBr u (.BEQ a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..
theorem beq_mem (u : MachineState) (a b : Reg) (imm : BitVec 13) : (execInstrBr u (.BEQ a b imm)).mem=u.mem := by
  simp only [execInstrBr];split <;> rfl

/-- A fused phase tail: stride, byte mark of the record's cap leaf, index advance, latch. -/
theorem tail_step (p : Nat) (hp : p<4) (st : MachineState) (B pos j k : Nat) (pc : st.pc=address (ftailWord p))
    (dest : st.getReg .x21=BitVec.ofNat 64 B)
    (node : st.getReg .x6=BitVec.ofNat 64 (512+pos/32768)) (small : pos<16777216)
    (idx : st.getReg .x8=BitVec.ofNat 64 (indicesBase+8*j)) (last : st.getReg .x17=BitVec.ofNat 64 (indicesBase+8*k))
    (hj : j<k) (hk : k ≤ 16777216)
    (marks : st.getReg .x26=BitVec.ofNat 64 Opening.markBase) (one : st.getReg .x23=1#64) :
    let u:=walkRows st (ftailRows p (decide (j+1=k)))
    legal (ftailRows p (decide (j+1=k))) st ∧
      u.pc=address (if j+1=k then fexitWord p else fphaseWord ((p+1)%4)) ∧
      u.getReg .x21=BitVec.ofNat 64 (B+stride p) ∧
      u.getReg .x8=BitVec.ofNat 64 (indicesBase+8*(j+1)) ∧
      u.mem=(st.setByte (BitVec.ofNat 64 (Opening.markBase+(256+pos/65536))) 1#8).mem ∧
      (∀ r, r ≠ .x21 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u.getReg r=st.getReg r) := by
  intro u
  have g := half_node pos small
  have ma := mark_address (256+pos/65536) (by omega)
  have imm : signExtend12 (BitVec.ofNat 12 (stride p))=BitVec.ofNat 64 (stride p) := by
    interval_cases p <;> decide
  have m26 : st.getReg .x26=4096#64 := marks
  have markValid : accessValid (BitVec.ofNat 64 (Opening.markBase+(256+pos/65536))) 1=true := by
    simp [accessValid, rangeValid, MEMORY_BYTES, Opening.markBase, BitVec.toNat_ofNat]
    omega
  have next8 : BitVec.ofNat 64 (indicesBase+8*j)+8#64=BitVec.ofNat 64 (indicesBase+8*(j+1)) := by
    rw [show (8#64 : Word)=BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]; congr 1
  have dest' : BitVec.ofNat 64 B+BitVec.ofNat 64 (stride p)=BitVec.ofNat 64 (B+stride p) := by
    rw [← BitVec.ofNat_add]
  let s5 := walkRows st (tailBodyRows p)
  have whole : u=walkRows s5 (latchRows p (decide (j+1=k))) := by
    show walkRows st (tailBodyRows p ++ _)=_; rw [walk_join]
  have s5pc : s5.pc=address (ftailWord p+5) := by
    show st.pc+4+4+4+4+4=_
    rw [pc, address_succ, address_succ, address_succ, address_succ, address_succ]
  have s5x8 : s5.getReg .x8=BitVec.ofNat 64 (indicesBase+8*(j+1)) := by
    simp [s5, tailBodyRows, walkRows, execInstrBr, e12, idx, next8]
  have s5x17 : s5.getReg .x17=BitVec.ofNat 64 (indicesBase+8*k) := by
    simp [s5, tailBodyRows, walkRows, execInstrBr, last]
  have s5x21 : s5.getReg .x21=BitVec.ofNat 64 (B+stride p) := by
    simp [s5, tailBodyRows, walkRows, execInstrBr, dest, imm, dest']
  have s5mem : s5.mem=(st.setByte (BitVec.ofNat 64 (Opening.markBase+(256+pos/65536))) 1#8).mem := by
    simp [s5, tailBodyRows, walkRows, execInstrBr, node, g, m26, ma, z12, one, one_byte, mem_of_set_byte]
  have s5keep (r : Reg) (h21 : r ≠ .x21) (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h8 : r ≠ .x8) : s5.getReg r=st.getReg r := by
    simp [s5, tailBodyRows, walkRows, execInstrBr, Ne.symm h21, Ne.symm h6, Ne.symm h7, Ne.symm h8]
  have bodyLegal : legal (tailBodyRows p) st := by
    simp only [tailBodyRows, legal]
    refine ⟨pc, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, trivial⟩
    · show st.pc+4=_; rw [pc, address_succ]
    · show st.pc+4+4=_; rw [pc, address_succ, address_succ]
    · show st.pc+4+4+4=_; rw [pc, address_succ, address_succ, address_succ]
    · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, node, g, m26, ma, z12, markValid]
    · show st.pc+4+4+4+4=_; rw [pc, address_succ, address_succ, address_succ, address_succ]
  have eqIdx : (BitVec.ofNat 64 (indicesBase+8*(j+1))=BitVec.ofNat 64 (indicesBase+8*k)) ↔ j+1=k := index_ne j k hk hj
  by_cases p3 : p=3
  · subst p3
    have latchT : latchRows 3 true=[(5176,.BEQ .x8 .x17 (branchTo 5176 5178))] := rfl
    have latchF : latchRows 3 false=[(5176,.BEQ .x8 .x17 (branchTo 5176 5178)),(5177,.JAL .x0 (jumpTo 5177 4097))] := rfl
    have tw : ftailWord 3+5=5176 := by decide
    rw [tw] at s5pc
    by_cases e : j+1=k
    · have eq : BitVec.ofNat 64 (indicesBase+8*(j+1))=BitVec.ofNat 64 (indicesBase+8*k) := eqIdx.mpr e
      have dt : decide (j+1=k)=true := decide_eq_true e
      have hit : execInstrBr s5 (.BEQ .x8 .x17 (branchTo 5176 5178))=s5.setPC (address (fexitWord 3)) := by
        simp only [execInstrBr, s5x8, s5x17, eq, beq_self_eq_true, ite_true, s5pc]; rw [beq_branch.1]
      have uEq : u=s5.setPC (address (fexitWord 3)) := by
        rw [whole, dt, latchT]; exact hit
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [dt, show ftailRows 3 true=tailBodyRows 3 ++ latchRows 3 true from rfl]
        exact legal_append _ _ _ bodyLegal (by rw [latchT]; exact ⟨s5pc, rfl, trivial⟩)
      · rw [uEq, if_pos e]; rfl
      · rw [uEq]; exact s5x21
      · rw [uEq]; exact s5x8
      · rw [uEq]; exact s5mem
      · intro r h21 h6 h7 h8; rw [uEq]; exact s5keep r h21 h6 h7 h8
    · have ne : BitVec.ofNat 64 (indicesBase+8*(j+1)) ≠ BitVec.ofNat 64 (indicesBase+8*k) := fun h => e (eqIdx.mp h)
      have dt : decide (j+1=k)=false := decide_eq_false e
      let s6 := execInstrBr s5 (.BEQ .x8 .x17 (branchTo 5176 5178))
      have miss : s6=s5.setPC (address 5177) := by
        show execInstrBr s5 _=_
        simp only [execInstrBr, s5x8, s5x17, beq_iff_eq, ne, ite_false, s5pc]; rw [beq_branch.2]
      have uEq : u=execInstrBr s6 (.JAL .x0 (jumpTo 5177 4097)) := by
        rw [whole, dt, latchF]; rfl
      have s6pc : s6.pc=address 5177 := by rw [miss]; rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [dt, show ftailRows 3 false=tailBodyRows 3 ++ latchRows 3 false from rfl]
        exact legal_append _ _ _ bodyLegal (by rw [latchF]; exact ⟨s5pc, rfl, s6pc, rfl, trivial⟩)
      · rw [uEq, jal_any_pc, s6pc, jal_back, if_neg e]
      · rw [uEq, jal_any_reg, miss]; exact s5x21
      · rw [uEq, jal_any_reg, miss]; exact s5x8
      · rw [uEq, jal_any_mem, miss]; exact s5mem
      · intro r h21 h6 h7 h8; rw [uEq, jal_any_reg, miss]; exact s5keep r h21 h6 h7 h8
  · have hp3 : p<3 := by omega
    have br := tail_branch p hp3
    have latchN (lst : Bool) : latchRows p lst=[(ftailWord p+5,.BNE .x8 .x17 (branchTo (ftailWord p+5) (fphaseWord (p+1))))] := by
      simp [latchRows, p3]
    have uEq : u=execInstrBr s5 (.BNE .x8 .x17 (branchTo (ftailWord p+5) (fphaseWord (p+1)))) := by
      rw [whole, latchN]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact legal_append _ _ _ bodyLegal (by rw [latchN]; exact ⟨s5pc, rfl, trivial⟩)
    · rw [uEq]
      simp only [execInstrBr, s5x8, s5x17]
      by_cases e : j+1=k
      · have eq : BitVec.ofNat 64 (indicesBase+8*(j+1))=BitVec.ofNat 64 (indicesBase+8*k) := eqIdx.mpr e
        rw [eq, if_pos e]
        simp [s5pc]
        exact br.2
      · have ne : BitVec.ofNat 64 (indicesBase+8*(j+1)) ≠ BitVec.ofNat 64 (indicesBase+8*k) :=
          fun h => e (eqIdx.mp h)
        rw [if_neg e, show (p+1)%4=p+1 by omega]
        simp [ne, s5pc, br.1]
    · rw [uEq, bne_reg']; exact s5x21
    · rw [uEq, bne_reg']; exact s5x8
    · rw [uEq, bne_mem']; exact s5mem
    · intro r h21 h6 h7 h8; rw [uEq, bne_reg']; exact s5keep r h21 h6 h7 h8

private theorem low_word_byte (a : Word) (b : Nat) (hb : b<4) : (a.truncate 32).extractLsb' (8*b) 8=a.extractLsb' (8*b) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h : 8*b+i<32 := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, h, hi]

private theorem high_half_byte (a : Word) (c : Nat) (hc : c<2) :
    ((a >>> 32).truncate 16).extractLsb' (8*c) 8=a.extractLsb' (8*(4+c)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h : 8*c+i<16 := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h, hi,
    show 32+(8*c+i)=8*(4+c)+i by ring]

private theorem low_half_byte (a : Word) (c : Nat) (hc : c<2) : (a.truncate 16).extractLsb' (8*c) 8=a.extractLsb' (8*c) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h : 8*c+i<16 := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, h, hi]

@[local simp] private theorem reg_word32 (t : MachineState) (q : Word) (v : BitVec 32) (r : Reg) :
    (t.setWord32 q v).getReg r=t.getReg r := rfl
@[local simp] private theorem reg_half16 (t : MachineState) (q : Word) (v : BitVec 16) (r : Reg) :
    (t.setHalfword q v).getReg r=t.getReg r := rfl
@[local simp] private theorem se0 : signExtend12 (0 : BitVec 12)=0#64 := rfl
@[local simp] private theorem se2 : signExtend12 (2 : BitVec 12)=2#64 := rfl
@[local simp] private theorem se4 : signExtend12 (4 : BitVec 12)=4#64 := rfl
@[local simp] private theorem se6 : signExtend12 (6 : BitVec 12)=6#64 := rfl
@[local simp] private theorem se0h : signExtend12 0#12=0#64 := rfl
@[local simp] private theorem se2h : signExtend12 2#12=2#64 := rfl
@[local simp] private theorem se4h : signExtend12 4#12=4#64 := rfl
@[local simp] private theorem se6h : signExtend12 6#12=6#64 := rfl

private theorem jump_back (w : Nat) (hw : w ∈ [4362, 4636, 4908, 5178]) :
    address w+signExtend21 (jumpTo w 6960)=address 6960 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl <;> decide

private theorem word_mem_other (t : MachineState) (A : Word) (v : BitVec 32) (q : Word) (h : q ≠ alignToDword A) :
    (t.setWord32 A v).getMem q=t.getMem q := by
  simp [MachineState.setWord32, MachineState.getMem_setMem_ne h]

private theorem half_mem_other (t : MachineState) (A : Word) (v : BitVec 16) (q : Word) (h : q ≠ alignToDword A) :
    (t.setHalfword A v).getMem q=t.getMem q := by
  simp [MachineState.setHalfword, MachineState.getMem_setMem_ne h]

/-- The exit stub of phase `p`: flush `flushLen p` pending stream bytes of `a1` at the aligned cursor, advance the
cursor, jump to the cap stage at 6960. -/
theorem exit_step (p : Nat) (hp : p<4) (st : MachineState) (D : Nat) (a : Word) (pc : st.pc=address (fexitWord p))
    (dest : st.getReg .x21=BitVec.ofNat 64 D) (al : D%8=0) (fit : D+8 ≤ MEMORY_BYTES) (carry : st.getReg .x4=a) :
    RunsOpeningBlock st (walkRows st (fexitRows p)) (exitCost p) ∧
      (walkRows st (fexitRows p)).pc=address 6960 ∧
      (walkRows st (fexitRows p)).getReg .x21=BitVec.ofNat 64 (D+flushLen p) ∧
      (∀ b<flushLen p, (walkRows st (fexitRows p)).getByte (BitVec.ofNat 64 (D+b))=a.extractLsb' (8*b) 8) ∧
      (∀ x<2^64, x<D ∨ D+flushLen p ≤ x →
        (walkRows st (fexitRows p)).getByte (BitVec.ofNat 64 x)=st.getByte (BitVec.ofNat 64 x)) ∧
      (∀ q : Word, q ≠ BitVec.ofNat 64 D → (walkRows st (fexitRows p)).getMem q=st.getMem q) ∧
      (∀ r, r ≠ .x21 → r ≠ .x4 → (walkRows st (fexitRows p)).getReg r=st.getReg r) := by
  have mem : MEMORY_BYTES=68719476736 := rfl
  have z : st.getReg .x21+0#64=BitVec.ofNat 64 D := by rw [dest, BitVec.add_zero]
  have four : st.getReg .x21+4#64=BitVec.ofNat 64 (D+4) := by
    rw [dest, show (4#64 : Word)=BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  have dz : BitVec.ofNat 64 D+0#64=BitVec.ofNat 64 D := BitVec.add_zero _
  have d4 : BitVec.ofNat 64 D+4#64=BitVec.ofNat 64 (D+4) := by
    rw [show (4#64 : Word)=BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  have vw : accessValid (BitVec.ofNat 64 D) 4=true := by
    simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show D<2^64 by omega)]; omega
  have vh : accessValid (BitVec.ofNat 64 D) 2=true := by
    simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show D<2^64 by omega)]; omega
  have vh4 : accessValid (BitVec.ofNat 64 (D+4)) 2=true := by
    simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show D+4<2^64 by omega)]; omega
  have alignD : alignToDword (BitVec.ofNat 64 D)=BitVec.ofNat 64 D := by
    rw [table_align_eq D (by omega)]; congr 1; omega
  have alignD4 : alignToDword (BitVec.ofNat 64 (D+4))=BitVec.ofNat 64 D := by
    rw [table_align_eq (D+4) (by omega)]; congr 1; omega
  have byteSet (t : MachineState) (r : Reg) (v pcv : Word) (x : Word) : ((t.setReg r v).setPC pcv).getByte x=t.getByte x := by
    unfold MachineState.getByte MachineState.getMem; rw [mem_of_set, mem_of_reg]
  have memSet (t : MachineState) (r : Reg) (v pcv : Word) : ((t.setReg r v).setPC pcv).mem=t.mem := by
    rw [mem_of_set, mem_of_reg]
  have byteJal (t : MachineState) (pcv : Word) (x : Word) : (t.setPC pcv).getByte x=t.getByte x := rfl
  have keyD (q : Word) (h : q ≠ BitVec.ofNat 64 D) : q ≠ alignToDword (BitVec.ofNat 64 D) := by rwa [alignD]
  have keyD4 (q : Word) (h : q ≠ BitVec.ofNat 64 D) : q ≠ alignToDword (BitVec.ofNat 64 (D+4)) := by rwa [alignD4]
  have outW (t : MachineState) (x : Nat) (fx : x<2^64) (away : x<D ∨ D+4 ≤ x) (v : BitVec 32) :
      (t.setWord32 (BitVec.ofNat 64 D) v).getByte (BitVec.ofNat 64 x)=t.getByte (BitVec.ofNat 64 x) :=
    word_outside t D x v al (by omega) fx away
  have outH (t : MachineState) (x A : Nat) (fx : x<2^64) (fa : A+2 ≤ 2^64) (ev : A%2=0) (away : x ≠ A ∧ x ≠ A+1)
      (v : BitVec 16) : (t.setHalfword (BitVec.ofNat 64 A) v).getByte (BitVec.ofNat 64 x)=t.getByte (BitVec.ofNat 64 x) := by
    have tA : (BitVec.ofNat 64 A).toNat=A := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have tx : (BitVec.ofNat 64 x).toNat=x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fx]
    apply ProjectedHalfword.store_outside
    · rw [tA]; exact ev
    · constructor
      · intro e; have := congrArg BitVec.toNat e
        rw [tx, tA] at this
        exact away.1 this
      · intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_add, tx, tA, show (1 : Word).toNat=1 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        exact away.2 this
  interval_cases p
  · -- six bytes: sw, srli, sh, addi, jal
    have hpc : st.pc=address 4358 := pc
    let s1 := execInstrBr st (.SW .x21 .x4 0)
    have b1 (x : Word) : s1.getByte x=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getByte x := by
      show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 32)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    let s2 := execInstrBr s1 (.SRLI .x4 .x4 32)
    have b2 (x : Word) : s2.getByte x=s1.getByte x := byteSet _ _ _ _ x
    have r2 : s2.getReg .x4=a >>> 32 := by simp [s2, s1, execInstrBr, carry]
    have d2 : s2.getReg .x21=BitVec.ofNat 64 D := by simp [s2, s1, execInstrBr, dest]
    let s3 := execInstrBr s2 (.SH .x21 .x4 4)
    have b3 (x : Word) : s3.getByte x=(s2.setHalfword (BitVec.ofNat 64 (D+4)) ((a >>> 32).truncate 16)).getByte x := by
      show ((s2.setHalfword (s2.getReg .x21+signExtend12 4) ((s2.getReg .x4).truncate 16)).setPC (s2.pc+4)).getByte x=_
      rw [se4, d2, d4, r2]; rfl
    have whole : walkRows st (fexitRows 0)=execInstrBr (execInstrBr s3 (.ADDI .x21 .x21 6)) (.JAL .x0 (jumpTo 4362 6960)) := rfl
    have bAll (x : Word) : (walkRows st (fexitRows 0)).getByte x=s3.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 0 (by decide)) 5 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [fexitRows, if_pos, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vw]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, dest, d4, vh4]
      · show st.pc+4+4+4=_; rw [hpc, address_succ, address_succ, address_succ]
      · show st.pc+4+4+4+4=_; rw [hpc, address_succ, address_succ, address_succ, address_succ]
    · show st.pc+4+4+4+4+signExtend21 (jumpTo 4362 6960)=_
      rw [hpc, address_succ, address_succ, address_succ, address_succ]
      exact jump_back 4362 (by simp)
    · have d3 : s3.getReg .x21=BitVec.ofNat 64 D := by
        show ((s2.setHalfword _ _).setPC _).getReg .x21=_; simp [d2]
      rw [whole]; simp [execInstrBr, d3, flushLen]
      rw [show (6#64 : Word)=BitVec.ofNat 64 6 from rfl, ← BitVec.ofNat_add]
    · intro b hb
      simp only [flushLen, if_pos] at hb
      rw [bAll, b3]
      by_cases low : b<4
      · rw [outH _ (D+b) (D+4) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩, b2, b1,
          word_stored st D b _ al (by omega) low, low_word_byte a b low]
      · obtain ⟨c, rfl, hc⟩ : ∃ c, b=4+c ∧ c<2 := ⟨b-4, by omega, by omega⟩
        rw [show D+(4+c)=D+4+c by omega, half_stored _ (D+4) c _ (by omega) (by omega) hc, high_half_byte a c hc]
    · intro x fx away
      simp only [flushLen, if_pos] at away
      rw [bAll, b3, outH _ x (D+4) fx (by omega) (by omega) ⟨by omega, by omega⟩, b2, b1, outW st x fx (by omega)]
    · intro q hq
      have m1 : s1.getMem q=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getMem q := by
        show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 32)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have m3 : s3.getMem q=(s2.setHalfword (BitVec.ofNat 64 (D+4)) ((a >>> 32).truncate 16)).getMem q := by
        show ((s2.setHalfword (s2.getReg .x21+signExtend12 4) ((s2.getReg .x4).truncate 16)).setPC (s2.pc+4)).getMem q=_
        rw [se4, d2, d4, r2]; rfl
      have m2 : s2.getMem q=s1.getMem q := by
        show ((s1.setReg _ _).setPC _).getMem q=_; rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
      have mAll : (walkRows st (fexitRows 0)).getMem q=s3.getMem q := by
        rw [whole]; show (((s3.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m3, half_mem_other _ _ _ q (keyD4 q hq), m2, m1, word_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, fexitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- four bytes: sw, addi, jal
    have hpc : st.pc=address 4634 := pc
    let s1 := execInstrBr st (.SW .x21 .x4 0)
    have b1 (x : Word) : s1.getByte x=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getByte x := by
      show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 32)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    have d1 : s1.getReg .x21=BitVec.ofNat 64 D := by
      show ((st.setWord32 _ _).setPC _).getReg .x21=_; simp [dest]
    have whole : walkRows st (fexitRows 1)=execInstrBr (execInstrBr s1 (.ADDI .x21 .x21 4)) (.JAL .x0 (jumpTo 4636 6960)) := rfl
    have bAll (x : Word) : (walkRows st (fexitRows 1)).getByte x=s1.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 1 (by decide)) 3 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [fexitRows, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vw]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
    · show st.pc+4+4+signExtend21 (jumpTo 4636 6960)=_
      rw [hpc, address_succ, address_succ]
      exact jump_back 4636 (by simp)
    · rw [whole]; simp [execInstrBr, d1, flushLen]
      rw [show (4#64 : Word)=BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    · intro b hb
      simp [flushLen] at hb
      rw [bAll, b1, word_stored st D b _ al (by omega) (by omega), low_word_byte a b (by omega)]
    · intro x fx away
      simp [flushLen] at away
      rw [bAll, b1, outW st x fx (by omega)]
    · intro q hq
      have m1 : s1.getMem q=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getMem q := by
        show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 32)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have mAll : (walkRows st (fexitRows 1)).getMem q=s1.getMem q := by
        rw [whole]; show (((s1.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m1, word_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, fexitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- two bytes: sh, addi, jal
    have hpc : st.pc=address 4906 := pc
    let s1 := execInstrBr st (.SH .x21 .x4 0)
    have b1 (x : Word) : s1.getByte x=(st.setHalfword (BitVec.ofNat 64 D) (a.truncate 16)).getByte x := by
      show ((st.setHalfword (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 16)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    have d1 : s1.getReg .x21=BitVec.ofNat 64 D := by
      show ((st.setHalfword _ _).setPC _).getReg .x21=_; simp [dest]
    have whole : walkRows st (fexitRows 2)=execInstrBr (execInstrBr s1 (.ADDI .x21 .x21 2)) (.JAL .x0 (jumpTo 4908 6960)) := rfl
    have bAll (x : Word) : (walkRows st (fexitRows 2)).getByte x=s1.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 2 (by decide)) 3 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [fexitRows, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vh]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
    · show st.pc+4+4+signExtend21 (jumpTo 4908 6960)=_
      rw [hpc, address_succ, address_succ]
      exact jump_back 4908 (by simp)
    · rw [whole]; simp [execInstrBr, d1, flushLen]
      rw [show (2#64 : Word)=BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    · intro b hb
      simp [flushLen] at hb
      rw [bAll, b1, half_stored st D b _ (by omega) (by omega) (by omega), low_half_byte a b (by omega)]
    · intro x fx away
      simp [flushLen] at away
      rw [bAll, b1, outH st x D fx (by omega) (by omega) ⟨by omega, by omega⟩]
    · intro q hq
      have m1 : s1.getMem q=(st.setHalfword (BitVec.ofNat 64 D) (a.truncate 16)).getMem q := by
        show ((st.setHalfword (st.getReg .x21+signExtend12 0) ((st.getReg .x4).truncate 16)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have mAll : (walkRows st (fexitRows 2)).getMem q=s1.getMem q := by
        rw [whole]; show (((s1.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m1, half_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, fexitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- nothing to flush: jal
    have hpc : st.pc=address 5178 := pc
    have whole : walkRows st (fexitRows 3)=execInstrBr st (.JAL .x0 (jumpTo 5178 6960)) := rfl
    refine ⟨rows_block _ _ ?_ (exit_present 3 (by decide)) 1 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [fexitRows, legal]; exact ⟨hpc, rfl, trivial⟩
    · rw [whole]; show st.pc+signExtend21 (jumpTo 5178 6960)=_; rw [hpc]; exact jump_back 5178 (by simp)
    · rw [whole]; simp [execInstrBr, dest, flushLen]
    · intro b hb; simp [flushLen] at hb
    · intro x _ _; rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ _
    · intro q _; rw [whole]; simp only [execInstrBr]; rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
    · intro r h21 _; rw [whole]; simp [execInstrBr]


end TwoPermutationPrototype.GroupedOpening.Layout2
