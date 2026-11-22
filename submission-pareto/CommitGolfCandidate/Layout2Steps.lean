import CommitGolfCandidate.Layout2Loop

/-! Layout 2 opener: the effect of the loop code around the phase writers (first record entry, per-phase header,
per-phase tail, exit stubs), each as a `RunsOpeningBlock` with its register, memory and byte effects. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase bodyWord bodyLen tailWord)
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

/-- A record header at word `w`: `ld t1,0(s0); slli t2,t1,4; add t2,s6,t2`. -/
theorem hdr_at_step (w : Nat) (code : presentRows (hdrRowsAt w)) (st : MachineState) (X pos : Nat)
    (pc : st.pc=address w)
    (idx : st.getReg .x8=BitVec.ofNat 64 X) (al : X%8=0) (fit : X+8 ≤ MEMORY_BYTES)
    (val : st.getMem (BitVec.ofNat 64 X)=BitVec.ofNat 64 pos) (small : pos<16777216)
    (nonce : st.getReg .x22=BitVec.ofNat 64 nonceBase) :
    RunsOpeningBlock st (walkRows st (hdrRowsAt w)) 3 ∧ (walkRows st (hdrRowsAt w)).pc=address (w+3) ∧
      (walkRows st (hdrRowsAt w)).getReg .x6=BitVec.ofNat 64 pos ∧
      (walkRows st (hdrRowsAt w)).getReg .x7=BitVec.ofNat 64 (nonceBase+16*pos) ∧
      (walkRows st (hdrRowsAt w)).mem=st.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → (walkRows st (hdrRowsAt w)).getReg r=st.getReg r) := by
  have valid : accessValid (BitVec.ofNat 64 X) 8=true := Opening.aligned_access X al fit
  refine ⟨rows_block _ _ ?_ code 3 (by simp [hdrRowsAt]) (by simp [hdrRowsAt, price]; rfl), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hdrRowsAt, legal]
    refine ⟨pc, ?_, ?_, rfl, ?_, rfl, trivial⟩
    · simp [ordinaryStep, memoryArgumentsValid, memAccess, z12, idx, valid]
    · show st.pc+4=address (w+1); rw [pc, address_succ]
    · show st.pc+4+4=address (w+2); rw [pc, address_succ, address_succ]
  · show st.pc+4+4+4=_; rw [pc, address_succ, address_succ, address_succ]
  · simp [walkRows, hdrRowsAt, execInstrBr, z12, idx, val]
  · simp [walkRows, hdrRowsAt, execInstrBr, z12, idx, val, nonce]
    exact shift_four pos small
  · simp [walkRows, hdrRowsAt, execInstrBr]
  · intro r h6 h7; simp [walkRows, hdrRowsAt, execInstrBr, Ne.symm h6, Ne.symm h7]

/-- A phase header. -/
theorem hdr_step (p : Nat) (hp : p<4) (st : MachineState) (X pos : Nat) (pc : st.pc=address (hdrWord p))
    (idx : st.getReg .x8=BitVec.ofNat 64 X) (al : X%8=0) (fit : X+8 ≤ MEMORY_BYTES)
    (val : st.getMem (BitVec.ofNat 64 X)=BitVec.ofNat 64 pos) (small : pos<16777216)
    (nonce : st.getReg .x22=BitVec.ofNat 64 nonceBase) :
    RunsOpeningBlock st (walkRows st (hdrRows p)) 3 ∧ (walkRows st (hdrRows p)).pc=address (bodyWord p) ∧
      (walkRows st (hdrRows p)).getReg .x6=BitVec.ofNat 64 pos ∧
      (walkRows st (hdrRows p)).getReg .x7=BitVec.ofNat 64 (nonceBase+16*pos) ∧
      (walkRows st (hdrRows p)).mem=st.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → (walkRows st (hdrRows p)).getReg r=st.getReg r) := by
  have hw : bodyWord p=hdrWord p+3 := by unfold hdrWord; interval_cases p <;> decide
  rw [hw]
  exact hdr_at_step (hdrWord p) (hdr_present p hp) st X pos pc idx al fit val small nonce

private theorem half_node (pos : Nat) (small : pos<16777216) :
    BitVec.ofNat 64 (512+pos/32768) >>> 1=BitVec.ofNat 64 (256+pos/65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

private theorem mark_address (g : Nat) (small : g<512) :
    4096#64+BitVec.ofNat 64 g <<< 3=BitVec.ofNat 64 (Opening.markBase+8*g) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Opening.markBase]
  norm_num
  omega

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

private theorem tail_branch (p : Nat) (hp : p<4) :
    address (tailWord p+6)+signExtend13 (branchTo (tailWord p+6) (hdrWord ((p+1)%4)))=address (hdrWord ((p+1)%4)) ∧
    address (tailWord p+6)+4=address (exitWord p) := by
  revert p; decide

/-- The six straight-line rows of a phase tail (before the latch). -/
def tailBody (p : Nat) : List Row := (tailRows p).take 6

/-- A phase tail: stride, mark of the record's cap leaf, index advance, latch. -/
theorem tail_step (p : Nat) (hp : p<4) (st : MachineState) (B pos j k : Nat) (pc : st.pc=address (tailWord p))
    (dest : st.getReg .x21=BitVec.ofNat 64 B)
    (node : st.getReg .x6=BitVec.ofNat 64 (512+pos/32768)) (small : pos<16777216)
    (idx : st.getReg .x8=BitVec.ofNat 64 (indicesBase+8*j)) (last : st.getReg .x17=BitVec.ofNat 64 (indicesBase+8*k))
    (hj : j<k) (hk : k ≤ 16777216)
    (marks : st.getReg .x26=BitVec.ofNat 64 Opening.markBase) (one : st.getReg .x23=1#64) :
    RunsOpeningBlock st (walkRows st (tailRows p)) 7 ∧
      (walkRows st (tailRows p)).pc=address (if j+1=k then exitWord p else hdrWord ((p+1)%4)) ∧
      (walkRows st (tailRows p)).getReg .x21=BitVec.ofNat 64 (B+stride p) ∧
      (walkRows st (tailRows p)).getReg .x8=BitVec.ofNat 64 (indicesBase+8*(j+1)) ∧
      (walkRows st (tailRows p)).mem=(st.setMem (BitVec.ofNat 64 (Opening.markBase+8*(256+pos/65536))) 1#64).mem ∧
      (∀ r, r ≠ .x21 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → (walkRows st (tailRows p)).getReg r=st.getReg r) := by
  have g := half_node pos small
  have ma := mark_address (256+pos/65536) (by omega)
  have imm : signExtend12 (BitVec.ofNat 12 (stride p))=BitVec.ofNat 64 (stride p) := by
    interval_cases p <;> decide
  have m26 : st.getReg .x26=4096#64 := marks
  have markValid : accessValid (BitVec.ofNat 64 (Opening.markBase+8*(256+pos/65536))) 8=true :=
    Opening.aligned_access _ (by unfold Opening.markBase; omega) (by unfold Opening.markBase MEMORY_BYTES; omega)
  have next8 : BitVec.ofNat 64 (indicesBase+8*j)+8#64=BitVec.ofNat 64 (indicesBase+8*(j+1)) := by
    rw [show (8#64 : Word)=BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]; congr 1
  have dest' : BitVec.ofNat 64 B+BitVec.ofNat 64 (stride p)=BitVec.ofNat 64 (B+stride p) := by
    rw [← BitVec.ofNat_add]
  have br := tail_branch p hp
  let s6 := walkRows st (tailBody p)
  have split : tailRows p=tailBody p++[(tailWord p+6,.BNE .x8 .x17 (branchTo (tailWord p+6) (hdrWord ((p+1)%4))))] := by
    simp [tailRows, tailBody]
  have whole : walkRows st (tailRows p)=execInstrBr s6 (.BNE .x8 .x17 (branchTo (tailWord p+6) (hdrWord ((p+1)%4)))) := by
    rw [split, walk_join]; rfl
  have s6pc : s6.pc=address (tailWord p+6) := by
    show st.pc+4+4+4+4+4+4=_
    rw [pc, address_succ, address_succ, address_succ, address_succ, address_succ, address_succ]
  have s6x8 : s6.getReg .x8=BitVec.ofNat 64 (indicesBase+8*(j+1)) := by
    simp [s6, tailBody, tailRows, walkRows, execInstrBr, e12, idx, next8]
  have s6x17 : s6.getReg .x17=BitVec.ofNat 64 (indicesBase+8*k) := by
    simp [s6, tailBody, tailRows, walkRows, execInstrBr, last]
  have s6x21 : s6.getReg .x21=BitVec.ofNat 64 (B+stride p) := by
    simp [s6, tailBody, tailRows, walkRows, execInstrBr, dest, imm, dest']
  have s6mem : s6.mem=(st.setMem (BitVec.ofNat 64 (Opening.markBase+8*(256+pos/65536))) 1#64).mem := by
    simp [s6, tailBody, tailRows, walkRows, execInstrBr, node, g, m26, ma, z12, one, mem_of_store]
  have s6keep (r : Reg) (h21 : r ≠ .x21) (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h8 : r ≠ .x8) : s6.getReg r=st.getReg r := by
    simp [s6, tailBody, tailRows, walkRows, execInstrBr, Ne.symm h21, Ne.symm h6, Ne.symm h7, Ne.symm h8]
  refine ⟨rows_block _ _ ?_ (tail_present p hp) 7 (by simp [tailRows]) (by simp [tailRows, price]; rfl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [split]
    apply legal_append
    · simp only [tailBody, tailRows, List.take, legal]
      refine ⟨pc, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, trivial⟩
      · show st.pc+4=_; rw [pc, address_succ]
      · show st.pc+4+4=_; rw [pc, address_succ, address_succ]
      · show st.pc+4+4+4=_; rw [pc, address_succ, address_succ, address_succ]
      · show st.pc+4+4+4+4=_; rw [pc, address_succ, address_succ, address_succ, address_succ]
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, node, g, m26, ma, z12, markValid]
      · show st.pc+4+4+4+4+4=_; rw [pc, address_succ, address_succ, address_succ, address_succ, address_succ]
    · exact ⟨s6pc, rfl, trivial⟩
  · rw [whole]
    simp only [execInstrBr, s6x8, s6x17]
    by_cases e : j+1=k
    · have eq : BitVec.ofNat 64 (indicesBase+8*(j+1))=BitVec.ofNat 64 (indicesBase+8*k) := (index_ne j k hk hj).mpr e
      rw [eq, if_pos e]
      simp [s6pc]
      exact br.2
    · have ne : BitVec.ofNat 64 (indicesBase+8*(j+1)) ≠ BitVec.ofNat 64 (indicesBase+8*k) :=
        fun h => e ((index_ne j k hk hj).mp h)
      rw [if_neg e]
      simp [ne, s6pc, br.1]
  · rw [whole, bne_reg']; exact s6x21
  · rw [whole, bne_reg']; exact s6x8
  · rw [whole, bne_mem']; exact s6mem
  · intro r h21 h6 h7 h8; rw [whole, bne_reg']; exact s6keep r h21 h6 h7 h8

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

private theorem jump_back (w : Nat) (hw : w ∈ [4338, 4583, 4828, 5070]) :
    address w+signExtend21 (jumpTo w 1097)=address 1097 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl <;> decide

private theorem word_mem_other (t : MachineState) (A : Word) (v : BitVec 32) (q : Word) (h : q ≠ alignToDword A) :
    (t.setWord32 A v).getMem q=t.getMem q := by
  simp [MachineState.setWord32, MachineState.getMem_setMem_ne h]

private theorem half_mem_other (t : MachineState) (A : Word) (v : BitVec 16) (q : Word) (h : q ≠ alignToDword A) :
    (t.setHalfword A v).getMem q=t.getMem q := by
  simp [MachineState.setHalfword, MachineState.getMem_setMem_ne h]

/-- The exit stub of phase `p`: flush `flushLen p` pending stream bytes of `a1` at the aligned cursor, advance the
cursor, jump to the cap preparation. -/
theorem exit_step (p : Nat) (hp : p<4) (st : MachineState) (D : Nat) (a : Word) (pc : st.pc=address (exitWord p))
    (dest : st.getReg .x21=BitVec.ofNat 64 D) (al : D%8=0) (fit : D+8 ≤ MEMORY_BYTES) (carry : st.getReg .x11=a) :
    RunsOpeningBlock st (walkRows st (exitRows p)) (exitCost p) ∧
      (walkRows st (exitRows p)).pc=address 1097 ∧
      (walkRows st (exitRows p)).getReg .x21=BitVec.ofNat 64 (D+flushLen p) ∧
      (∀ b<flushLen p, (walkRows st (exitRows p)).getByte (BitVec.ofNat 64 (D+b))=a.extractLsb' (8*b) 8) ∧
      (∀ x<2^64, x<D ∨ D+flushLen p ≤ x →
        (walkRows st (exitRows p)).getByte (BitVec.ofNat 64 x)=st.getByte (BitVec.ofNat 64 x)) ∧
      (∀ q : Word, q ≠ BitVec.ofNat 64 D → (walkRows st (exitRows p)).getMem q=st.getMem q) ∧
      (∀ r, r ≠ .x21 → r ≠ .x11 → (walkRows st (exitRows p)).getReg r=st.getReg r) := by
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
    have hpc : st.pc=address 4334 := pc
    let s1 := execInstrBr st (.SW .x21 .x11 0)
    have b1 (x : Word) : s1.getByte x=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getByte x := by
      show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 32)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    let s2 := execInstrBr s1 (.SRLI .x11 .x11 32)
    have b2 (x : Word) : s2.getByte x=s1.getByte x := byteSet _ _ _ _ x
    have r2 : s2.getReg .x11=a >>> 32 := by simp [s2, s1, execInstrBr, carry]
    have d2 : s2.getReg .x21=BitVec.ofNat 64 D := by simp [s2, s1, execInstrBr, dest]
    let s3 := execInstrBr s2 (.SH .x21 .x11 4)
    have b3 (x : Word) : s3.getByte x=(s2.setHalfword (BitVec.ofNat 64 (D+4)) ((a >>> 32).truncate 16)).getByte x := by
      show ((s2.setHalfword (s2.getReg .x21+signExtend12 4) ((s2.getReg .x11).truncate 16)).setPC (s2.pc+4)).getByte x=_
      rw [se4, d2, d4, r2]; rfl
    have whole : walkRows st (exitRows 0)=execInstrBr (execInstrBr s3 (.ADDI .x21 .x21 6)) (.JAL .x0 (jumpTo 4338 1097)) := rfl
    have bAll (x : Word) : (walkRows st (exitRows 0)).getByte x=s3.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 0 (by decide)) 5 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [exitRows, if_pos, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vw]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, dest, d4, vh4]
      · show st.pc+4+4+4=_; rw [hpc, address_succ, address_succ, address_succ]
      · show st.pc+4+4+4+4=_; rw [hpc, address_succ, address_succ, address_succ, address_succ]
    · show st.pc+4+4+4+4+signExtend21 (jumpTo 4338 1097)=_
      rw [hpc, address_succ, address_succ, address_succ, address_succ]
      exact jump_back 4338 (by simp)
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
        show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 32)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have m3 : s3.getMem q=(s2.setHalfword (BitVec.ofNat 64 (D+4)) ((a >>> 32).truncate 16)).getMem q := by
        show ((s2.setHalfword (s2.getReg .x21+signExtend12 4) ((s2.getReg .x11).truncate 16)).setPC (s2.pc+4)).getMem q=_
        rw [se4, d2, d4, r2]; rfl
      have m2 : s2.getMem q=s1.getMem q := by
        show ((s1.setReg _ _).setPC _).getMem q=_; rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
      have mAll : (walkRows st (exitRows 0)).getMem q=s3.getMem q := by
        rw [whole]; show (((s3.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m3, half_mem_other _ _ _ q (keyD4 q hq), m2, m1, word_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, exitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- four bytes: sw, addi, jal
    have hpc : st.pc=address 4581 := pc
    let s1 := execInstrBr st (.SW .x21 .x11 0)
    have b1 (x : Word) : s1.getByte x=(st.setWord32 (BitVec.ofNat 64 D) (a.truncate 32)).getByte x := by
      show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 32)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    have d1 : s1.getReg .x21=BitVec.ofNat 64 D := by
      show ((st.setWord32 _ _).setPC _).getReg .x21=_; simp [dest]
    have whole : walkRows st (exitRows 1)=execInstrBr (execInstrBr s1 (.ADDI .x21 .x21 4)) (.JAL .x0 (jumpTo 4583 1097)) := rfl
    have bAll (x : Word) : (walkRows st (exitRows 1)).getByte x=s1.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 1 (by decide)) 3 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [exitRows, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vw]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
    · show st.pc+4+4+signExtend21 (jumpTo 4583 1097)=_
      rw [hpc, address_succ, address_succ]
      exact jump_back 4583 (by simp)
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
        show ((st.setWord32 (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 32)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have mAll : (walkRows st (exitRows 1)).getMem q=s1.getMem q := by
        rw [whole]; show (((s1.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m1, word_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, exitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- two bytes: sh, addi, jal
    have hpc : st.pc=address 4826 := pc
    let s1 := execInstrBr st (.SH .x21 .x11 0)
    have b1 (x : Word) : s1.getByte x=(st.setHalfword (BitVec.ofNat 64 D) (a.truncate 16)).getByte x := by
      show ((st.setHalfword (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 16)).setPC (st.pc+4)).getByte x=_
      rw [se0, z, carry]; rfl
    have d1 : s1.getReg .x21=BitVec.ofNat 64 D := by
      show ((st.setHalfword _ _).setPC _).getReg .x21=_; simp [dest]
    have whole : walkRows st (exitRows 2)=execInstrBr (execInstrBr s1 (.ADDI .x21 .x21 2)) (.JAL .x0 (jumpTo 4828 1097)) := rfl
    have bAll (x : Word) : (walkRows st (exitRows 2)).getByte x=s1.getByte x := by
      rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ x
    refine ⟨rows_block _ _ ?_ (exit_present 2 (by decide)) 3 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [exitRows, legal]
      refine ⟨hpc, ?_, ?_, rfl, ?_, rfl, trivial⟩
      · simp [ordinaryStep, memoryArgumentsValid, memAccess, dest, vh]
      · show st.pc+4=_; rw [hpc, address_succ]
      · show st.pc+4+4=_; rw [hpc, address_succ, address_succ]
    · show st.pc+4+4+signExtend21 (jumpTo 4828 1097)=_
      rw [hpc, address_succ, address_succ]
      exact jump_back 4828 (by simp)
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
        show ((st.setHalfword (st.getReg .x21+signExtend12 0) ((st.getReg .x11).truncate 16)).setPC (st.pc+4)).getMem q=_
        rw [se0, z, carry]; rfl
      have mAll : (walkRows st (exitRows 2)).getMem q=s1.getMem q := by
        rw [whole]; show (((s1.setReg _ _).setPC _).setPC _).getMem q=_
        rw [MachineState.getMem_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
      rw [mAll, m1, half_mem_other _ _ _ q (keyD q hq)]
    · intro r h21 h11
      simp [walkRows, exitRows, execInstrBr, Ne.symm h21, Ne.symm h11]
  · -- nothing to flush: jal
    have hpc : st.pc=address 5070 := pc
    have whole : walkRows st (exitRows 3)=execInstrBr st (.JAL .x0 (jumpTo 5070 1097)) := rfl
    refine ⟨rows_block _ _ ?_ (exit_present 3 (by decide)) 1 rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [exitRows, legal]; exact ⟨hpc, rfl, trivial⟩
    · rw [whole]; show st.pc+signExtend21 (jumpTo 5070 1097)=_; rw [hpc]; exact jump_back 5070 (by simp)
    · rw [whole]; simp [execInstrBr, dest, flushLen]
    · intro b hb; simp [flushLen] at hb
    · intro x _ _; rw [whole]; simp only [execInstrBr]; exact byteSet _ _ _ _ _
    · intro q _; rw [whole]; simp only [execInstrBr]; rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
    · intro r h21 _; rw [whole]; simp [execInstrBr]


end TwoPermutationPrototype.GroupedOpening.Layout2
