import CommitGolfCandidate.GroupOpenCapNode
import CommitGolfCandidate.GroupOpenCapChunkCode

/-! A marked level-5 node: the chunk jump (708), the chunk code (8192..8219) and the block of its leaf mask, one
emit block per frontier node, then `srli x6,x16,3; jal x0,<703>` back to the advance block with the node in `x6`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64
open Opening (CapSpan proofBase cap_span_node capDigestAddress)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

/-- One unit-cost instruction anywhere in the image. -/
theorem long_step (state : MachineState) (index : Nat) (instruction : Instr) (bounded : index<2^40)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase=some instruction)
    (ordinary : ordinaryStep state (.base instruction)=some (execInstrBr state instruction))
    (cost : instructionCycles (.base instruction)=1) :
    RunsOpeningBlock state (execInstrBr state instruction) 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (packed_fetch_long _ _ _ bounded pc decoded) ordinary,
    cost]

theorem jal_entry : ∀ k<4096,
    BitVec.ofNat 64 (4096+4*(8224+k))+signExtend21 (jalOffset (8224+k) 668)=0x1a70 := by decide +kernel

theorem jal_exit : ∀ k<4096,
    BitVec.ofNat 64 (4096+4*(8224+k))+signExtend21 (jalOffset (8224+k) 703)=0x1afc := by decide +kernel

theorem word_even : ∀ k<8224+4096, BitVec.ofNat 64 (4096+4*k) &&& ~~~1#64=BitVec.ofNat 64 (4096+4*k) := by
  intro k _
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases z : i=0
  · subst z
    simp [Nat.testBit_zero, show (4096+4*k)%2=0 by omega]
  · have one : Nat.testBit 1 i=false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow z)]; rfl
    simp [one]

theorem chunk_entries_range : ∀ mask<256, mask ≠ 0 → ∀ r ∈ chunkEntries mask, 2 ≤ r ∧ r<16 := by decide +kernel

private theorem chunk_node_lt (node r : Nat) (hn : node<64) (lo : 2 ≤ r) (hi : r<16) : chunkNode node r<512 := by
  unfold chunkNode depthOf
  interval_cases r <;> simp <;> omega

private theorem entry_node (node r : Nat) (lo : 2 ≤ r) (hi : r<16) :
    (8*node+entryOffset r)/2^(entryShift r)=chunkNode node r ∧ entryOffset r<8 := by
  unfold entryOffset entryShift chunkNode depthOf
  interval_cases r <;> simp <;> omega

private theorem small_imm (k : Nat) (hk : k<8) : signExtend12 (BitVec.ofNat 12 k)=BitVec.ofNat 64 k := by
  interval_cases k <;> decide

/-- The block code from word `w` decodes as listed. -/
def BlockAt (rs : List Nat) (w : Nat) : Prop :=
  ∀ j<(blockCode rs w).length, (openingImage.code[w+j]?).bind Opening.decodeBase=(blockCode rs w)[j]?

theorem block_at_tail (r : Nat) (rest : List Nat) (w : Nat) (code : BlockAt (r :: rest) w) :
    BlockAt rest (w+entryLen r) := by
  intro j hj
  have total : (blockCode (r :: rest) w).length=entryLen r+(blockCode rest (w+entryLen r)).length := by
    simp [blockCode, entry_code_length]
  have h := code (entryLen r+j) (by omega)
  rw [show w+(entryLen r+j)=w+entryLen r+j by omega] at h
  rw [h, blockCode, List.getElem?_append_right (by rw [entry_code_length]; omega), entry_code_length,
    show entryLen r+j-entryLen r=j by omega]

theorem block_at_head (r : Nat) (rest : List Nat) (w : Nat) (code : BlockAt (r :: rest) w) (j : Nat)
    (hj : j<entryLen r) :
    (openingImage.code[w+j]?).bind Opening.decodeBase=(entryCode r w)[j]? := by
  have h := code j (by simp [blockCode, entry_code_length]; omega)
  rw [h, blockCode, List.getElem?_append_left (by rw [entry_code_length]; exact hj)]

theorem block_code_two : ∀ (rs : List Nat) (w : Nat), 2 ≤ (blockCode rs w).length
  | [], w => by simp [blockCode]
  | r :: rest, w => by
    rw [blockCode, List.length_append, entry_code_length]
    have := block_code_two rest (w+entryLen r)
    omega

/-- The entries of a block from word `w` (inside the block area) emit their nodes and return to the advance block. -/
theorem entries_run (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart node : Nat)
    (hn : node<64) (separate : proofBase ≤ capStart) (aligned : capStart%2=0) :
    ∀ (rs : List Nat) (w : Nat) (vs : List (BitVec 256)) (state : MachineState) (current : Nat),
    BlockAt rs w → 8224 ≤ w → w+(blockCode rs w).length ≤ 8224+4096 → (∀ r ∈ rs, 2 ≤ r ∧ r<16) →
    state.pc=BitVec.ofNat 64 (4096+4*w) → state.getReg .x16=BitVec.ofNat 64 (8*node) →
    CapRun groups heap capStart vs state current →
    capStart+capOffset (vs.length+rs.length)+2 ≤ MEMORY_BYTES →
    ∃ after, RunsOpeningBlock state after (entriesCycles rs capStart vs.length+2) ∧ after.pc=0x1afc ∧
      CapRun groups heap capStart (vs++(rs.map (chunkNode node)).map heap) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+rs.length) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a))
  | [], w, vs, state, current, code, lo, hi, _, pc, level, run, _ => by
    have c0 := code 0 (by simp [blockCode])
    have c1 := code 1 (by simp [blockCode])
    simp only [blockCode, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1
    simp only [blockCode, List.length_cons, List.length_nil] at hi
    let s1 := execInstrBr state (.SRLI .x6 .x16 3)
    have r1 := long_step state w _ (by omega) pc c0 rfl rfl
    have pc1 : s1.pc=BitVec.ofNat 64 (4096+4*(w+1)) := by
      show state.pc+4=_; rw [pc]; exact address_succ w
    let s2 := execInstrBr s1 (.JAL .x0 (jalOffset (w+1) 703))
    have r2 := long_step s1 (w+1) _ (by omega) pc1 c1 rfl rfl
    have pc2 : s2.pc=0x1afc := by
      show s1.pc+signExtend21 (jalOffset (w+1) 703)=_
      rw [pc1]
      have := jal_exit (w+1-8224) (by omega)
      rwa [show 8224+(w+1-8224)=w+1 by omega] at this
    have x6 : s2.getReg .x6=BitVec.ofNat 64 node := by
      have e : s2.getReg .x6=BitVec.ofNat 64 (8*node) >>> (3 : BitVec 6).toNat := by
        simp [s2, s1, execInstrBr, level]
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    have keep (r : Reg) (h : r ≠ .x6) : s2.getReg r=state.getReg r := by
      simp [s2, s1, execInstrBr, Ne.symm h]
    have mem : s2.mem=state.mem := by simp [s2, s1, execInstrBr]; rfl
    refine ⟨s2, ?_, pc2, ?_, ?_⟩
    · simpa [entriesCycles] using r1.next r2
    · simp only [List.map_nil, List.append_nil]
      exact run.of_moved (fun r m => keep r (by intro e; subst e; simp at m)) mem x6
    · intro a _ _; exact byte_of_mem mem _
  | r :: rest, w, vs, state, current, code, lo, hi, range, pc, level, run, fits => by
    obtain ⟨rlo, rhi⟩ := range r (by simp)
    have total : (blockCode (r :: rest) w).length=entryLen r+(blockCode rest (w+entryLen r)).length := by
      simp [blockCode, entry_code_length]
    have restLen : 2 ≤ (blockCode rest (w+entryLen r)).length := block_code_two rest (w+entryLen r)
    obtain ⟨nodeEq, offSmall⟩ := entry_node node r rlo rhi
    have bounded := chunk_node_lt node r hn rlo rhi
    -- the entry: x6 := chunkNode node r, x18 := return word, pc := 668
    have entry : ∃ mid, RunsOpeningBlock state mid (entryLen r) ∧ mid.pc=0x1a70 ∧
        mid.getReg .x6=BitVec.ofNat 64 (chunkNode node r) ∧
        mid.getReg .x18=BitVec.ofNat 64 (4096+4*(w+entryLen r)) ∧ mid.mem=state.mem ∧
        (∀ q, q ≠ .x6 → q ≠ .x18 → mid.getReg q=state.getReg q) := by
      have c0 := block_at_head r rest w code 0 (by unfold entryLen; split <;> omega)
      let s1 := execInstrBr state (.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)))
      have x6a : s1.getReg .x6=BitVec.ofNat 64 (8*node+entryOffset r) := by
        simp [s1, execInstrBr, level, small_imm _ offSmall, BitVec.ofNat_add]
      have pc1 : s1.pc=BitVec.ofNat 64 (4096+4*(w+1)) := by
        show state.pc+4=_; rw [pc]; exact address_succ w
      by_cases leaf : depthOf r=3
      · have c1 := block_at_head r rest w code 1 (by unfold entryLen; rw [if_pos leaf]; omega)
        simp only [entryCode, leaf, ite_true, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.add_zero] at c0 c1
        have r1 := long_step state w _ (by omega) pc c0 rfl rfl
        let s2 := execInstrBr s1 (.JAL .x18 (jalOffset (w+1) 668))
        have r2 := long_step s1 (w+1) _ (by omega) pc1 c1 rfl rfl
        have len : entryLen r=2 := by unfold entryLen; rw [if_pos leaf]
        refine ⟨s2, by rw [len]; exact r1.next r2, ?_, ?_, ?_, ?_, ?_⟩
        · show s1.pc+signExtend21 (jalOffset (w+1) 668)=_
          rw [pc1]
          have := jal_entry (w+1-8224) (by omega)
          rwa [show 8224+(w+1-8224)=w+1 by omega] at this
        · have shift : entryShift r=0 := by unfold entryShift; omega
          rw [shift, pow_zero, Nat.div_one] at nodeEq
          simp only [s2, execInstrBr]; simp [x6a, nodeEq]
        · show s1.pc+4=_
          rw [pc1, len]; exact address_succ (w+1)
        · simp [s2, s1, execInstrBr]; rfl
        · intro q h6 h18; simp [s2, s1, execInstrBr, Ne.symm h6, Ne.symm h18]
      · have c1 := block_at_head r rest w code 1 (by unfold entryLen; rw [if_neg leaf]; omega)
        have c2 := block_at_head r rest w code 2 (by unfold entryLen; rw [if_neg leaf]; omega)
        simp only [entryCode, leaf, ite_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.add_zero] at c0 c1 c2
        have r1 := long_step state w _ (by omega) pc c0 rfl rfl
        let s2 := execInstrBr s1 (.SRLI .x6 .x6 (BitVec.ofNat 6 (entryShift r)))
        have r2 := long_step s1 (w+1) _ (by omega) pc1 c1 rfl rfl
        have pc2 : s2.pc=BitVec.ofNat 64 (4096+4*(w+2)) := by
          show s1.pc+4=_; rw [pc1]; exact address_succ (w+1)
        let s3 := execInstrBr s2 (.JAL .x18 (jalOffset (w+2) 668))
        have r3 := long_step s2 (w+2) _ (by omega) pc2 (by simpa using c2) rfl rfl
        have len : entryLen r=3 := by unfold entryLen; rw [if_neg leaf]
        refine ⟨s3, by rw [len]; exact (r1.next r2).next r3, ?_, ?_, ?_, ?_, ?_⟩
        · show s2.pc+signExtend21 (jalOffset (w+2) 668)=_
          rw [pc2]
          have := jal_entry (w+2-8224) (by omega)
          rwa [show 8224+(w+2-8224)=w+2 by omega] at this
        · have shiftSmall : entryShift r<4 := by unfold entryShift; omega
          simp only [s3, s2, execInstrBr]
          simp only [MachineState.getReg_setPC, Opening.getReg_setReg]
          simp [x6a]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
          have s64 : entryShift r%64=entryShift r := Nat.mod_eq_of_lt (by omega)
          have big : (8*node+entryOffset r)%2^64=8*node+entryOffset r := Nat.mod_eq_of_lt (by omega)
          have small2 : chunkNode node r%2^64=chunkNode node r := Nat.mod_eq_of_lt (by omega)
          simp only [s64, big, small2, Nat.reducePow] at *
          first
          | exact nodeEq
          | (rw [show (2:Nat)^(entryShift r%2^6)=2^(entryShift r) by rw [Nat.mod_eq_of_lt (by omega)]]; exact nodeEq)
          | omega
        · show s2.pc+4=_
          rw [pc2, len]; exact address_succ (w+2)
        · simp [s3, s2, s1, execInstrBr]; rfl
        · intro q h6 h18; simp [s3, s2, s1, execInstrBr, Ne.symm h6, Ne.symm h18]
    obtain ⟨mid, rmid, pcMid, x6Mid, x18Mid, memMid, keepMid⟩ := entry
    have runMid : CapRun groups heap capStart vs mid (chunkNode node r) :=
      run.of_moved (fun q m => keepMid q
        (by intro e; subst e; simp at m) (by intro e; subst e; simp at m)) memMid x6Mid
    have fitsOne : capStart+capOffset (vs.length+1)+2 ≤ MEMORY_BYTES := by
      have := cap_offset_mono (vs.length+1) (vs.length+(rest.length+1)) (by omega)
      simp only [List.length_cons] at fits; omega
    obtain ⟨emitted, rEmit, pcEmit, runEmit, frameEmit, keepEmit⟩ :=
      emit_node emit groups heap capStart vs mid (chunkNode node r) bounded runMid pcMid separate aligned fitsOne
    have link : emitted.getReg .x18=BitVec.ofNat 64 (4096+4*(w+entryLen r)) := by
      rw [keepEmit .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x18Mid]
    have even : BitVec.ofNat 64 (4096+4*(w+entryLen r)) &&& ~~~1#64=BitVec.ofNat 64 (4096+4*(w+entryLen r)) :=
      word_even (w+entryLen r) (by omega)
    let back := emitted.setPC (BitVec.ofNat 64 (4096+4*(w+entryLen r)))
    have rBack : RunsOpeningBlock emitted back 1 := fun fuel coins =>
      execute_emit_return emitted pcEmit _ link even fuel coins
    have levelBack : back.getReg .x16=BitVec.ofNat 64 (8*node) := by
      show emitted.getReg .x16=_
      rw [keepEmit .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        keepMid .x16 (by decide) (by decide), level]
    have runBack : CapRun groups heap capStart (vs++[heap (chunkNode node r)]) back (chunkNode node r) :=
      runEmit.of_kept (fun _ _ => rfl) rfl
    have lenVs : (vs++[heap (chunkNode node r)]).length=vs.length+1 := by simp
    have hidx' : vs.length+1+rest.length=vs.length+(r :: rest).length := by simp; omega
    obtain ⟨final, rRest, pcFinal, runFinal, frameRest⟩ :=
      entries_run emit groups heap capStart node hn separate aligned rest (w+entryLen r) _ back _
        (block_at_tail r rest w code) (by omega) (by omega) (fun q hq => range q (List.mem_cons_of_mem _ hq))
        rfl levelBack runBack (by rw [lenVs, hidx']; exact fits)
    refine ⟨final, ?_, pcFinal, ?_, ?_⟩
    · have chain := ((rmid.next rEmit).next rBack).next rRest
      rw [lenVs] at chain
      convert chain using 1
      simp only [entriesCycles]
      omega
    · simpa [List.append_assoc] using runFinal
    · intro a fit far
      rw [lenVs, hidx'] at frameRest
      rw [frameRest a fit far]
      rw [show back.getByte (BitVec.ofNat 64 a)=emitted.getByte (BitVec.ofNat 64 a) from rfl,
        frameEmit a fit (by
          have := cap_offset_mono (vs.length+1) (vs.length+(r :: rest).length) (by simp)
          omega)]
      exact byte_of_mem memMid _

attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

private theorem addr_word (node : Nat) (hn : node<64) :
    (BitVec.ofNat 64 (8*node) <<< (3 : BitVec 6).toNat)+BitVec.ofNat 64 4096=BitVec.ofNat 64 (4096+64*node) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  norm_num
  omega

theorem jump_target : ∀ m<256,
    ((BitVec.signExtend 64 ((9 : BitVec 20).zeroExtend 32 <<< 12)+(BitVec.ofNat 64 m <<< (6 : BitVec 6).toNat))+
      signExtend12 128) &&& ~~~1#64=BitVec.ofNat 64 (4096+4*chunkBlockWord m) := by
  unfold chunkBlockWord; decide +kernel

private theorem get_mem_of {a b : MachineState} (h : a.mem=b.mem) (w : Word) : a.getMem w=b.getMem w := by
  unfold MachineState.getMem; rw [h]

/-- Three mask rows: load leaf mark `j`, shift it to bit `j`, or it into `x28`. -/
private theorem mask_three (s : MachineState) (a j b : Nat) (hj : j<8) (pc : s.pc=address a)
    (load : s.getMem (s.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*j)))=BitVec.ofNat 64 b)
    (valid : accessValid (s.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*j))) 8=true) :
    legal [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
      (a+2,.OR .x28 .x28 .x29)] s ∧
    (walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
      (a+2,.OR .x28 .x28 .x29)]).pc=address (a+3) ∧
    (walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
      (a+2,.OR .x28 .x28 .x29)]).getReg .x28=s.getReg .x28 ||| (BitVec.ofNat 64 b <<< j) ∧
    (walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
      (a+2,.OR .x28 .x28 .x29)]).mem=s.mem ∧
    (∀ r, r ≠ .x28 → r ≠ .x29 → (walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),
      (a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),(a+2,.OR .x28 .x28 .x29)]).getReg r=s.getReg r) := by
  have sh : (BitVec.ofNat 6 j).toNat=j := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [legal]
    refine ⟨pc, ?_, ?_, rfl, ?_, rfl, trivial⟩
    · simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]
    · show s.pc+4=address (a+1); rw [pc, address_succ]
    · show s.pc+4+4=address (a+1+1); rw [pc, address_succ, address_succ]
  · show s.pc+4+4+4=address (a+3); rw [pc, address_succ, address_succ, address_succ]
  · simp [walkRows, execInstrBr, load, sh]
  · simp [walkRows, execInstrBr, mem_of_reg, mem_of_set]
  · intro r h28 h29
    simp [walkRows, execInstrBr, Ne.symm h28, Ne.symm h29]

private theorem mask_tail_run (bit : Nat → Nat) : ∀ (n j a : Nat) (s : MachineState), j+n ≤ 8 →
    s.pc=address a →
    (∀ i, j ≤ i → i<j+n → s.getMem (s.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*i)))=BitVec.ofNat 64 (bit i) ∧
      accessValid (s.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*i))) 8=true) →
    legal (maskTail a j n) s ∧ (walkRows s (maskTail a j n)).pc=address (a+3*n) ∧
    (walkRows s (maskTail a j n)).getReg .x28=
      (List.range' j n).foldl (fun acc i => acc ||| (BitVec.ofNat 64 (bit i) <<< i)) (s.getReg .x28) ∧
    (walkRows s (maskTail a j n)).mem=s.mem ∧
    (∀ r, r ≠ .x28 → r ≠ .x29 → (walkRows s (maskTail a j n)).getReg r=s.getReg r)
  | 0, j, a, s, _, pc, _ => by
    refine ⟨trivial, by simpa [maskTail, walkRows] using pc, by simp [maskTail, walkRows], rfl, fun r _ _ => rfl⟩
  | n+1, j, a, s, small, pc, marks => by
    obtain ⟨load, valid⟩ := marks j (le_refl _) (by omega)
    obtain ⟨l3, pc3, x28_3, mem3, keep3⟩ := mask_three s a j (bit j) (by omega) pc load valid
    have marks' : ∀ i, j+1 ≤ i → i<j+1+n →
        (walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
          (a+2,.OR .x28 .x28 .x29)]).getMem ((walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),
          (a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),(a+2,.OR .x28 .x28 .x29)]).getReg .x7+
            signExtend12 (BitVec.ofNat 12 (8*i)))=BitVec.ofNat 64 (bit i) ∧
        accessValid ((walkRows s [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),
          (a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),(a+2,.OR .x28 .x28 .x29)]).getReg .x7+
            signExtend12 (BitVec.ofNat 12 (8*i))) 8=true := by
      intro i h1 h2
      rw [keep3 .x7 (by decide) (by decide), get_mem_of mem3]
      exact marks i (by omega) (by omega)
    obtain ⟨lr, pcr, x28r, memr, keepr⟩ := mask_tail_run bit n (j+1) (a+3) _ (by omega) pc3 marks'
    have split : maskTail a j (n+1)=[(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),
        (a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),(a+2,.OR .x28 .x28 .x29)]++maskTail (a+3) (j+1) n := rfl
    rw [split, walk_join]
    refine ⟨legal_append _ _ _ l3 lr, ?_, ?_, ?_, ?_⟩
    · rw [pcr, show a+3+3*n=a+3*(n+1) by omega]
    · rw [x28r, x28_3, List.range'_succ, List.foldl_cons]
    · rw [memr, mem3]
    · intro r h28 h29; rw [keepr r h28 h29, keep3 r h28 h29]

/-- The chunk code: from the chunk jump target with `x16 = 8 node`, the jump into the block of the leaf mask. -/
theorem chunk_code_run (groups : List Nat) (state : MachineState) (node : Nat) (context : CapContext groups state)
    (span : CapSpan node 3) (level : state.getReg .x16=BitVec.ofNat 64 (8*node)) (pc : state.pc=0x9000) :
    RunsOpeningBlock state (walkRows state chunkRows) 28 ∧
      (walkRows state chunkRows).pc=BitVec.ofNat 64 (4096+4*chunkBlockWord (leafMask groups node)) ∧
      (walkRows state chunkRows).mem=state.mem ∧
      (∀ r, r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → r ≠ .x11 → (walkRows state chunkRows).getReg r=state.getReg r) := by
  have lo := span.start
  have hi := span.finish
  simp only [Nat.reducePow] at lo hi
  have hn : node<64 := by omega
  have pc0 : state.pc=address 8192 := pc
  -- address rows
  let t1 := walkRows state chunkAddrRows
  have legal1 : legal chunkAddrRows state := by
    simp only [chunkAddrRows, legal]
    exact ⟨pc0, rfl, by show state.pc+4=address 8193; rw [pc0, address_succ], rfl, trivial⟩
  have x7 : t1.getReg .x7=BitVec.ofNat 64 (4096+64*node) := by
    have e : t1.getReg .x7=(state.getReg .x16 <<< (3 : BitVec 6).toNat)+state.getReg .x26 := by
      simp [t1, walkRows, chunkAddrRows, execInstrBr]
    rw [e, level, context.markBaseWord]
    exact addr_word node hn
  have pc1 : t1.pc=address 8194 := by
    show state.pc+4+4=address 8194; rw [pc0, address_succ, address_succ]
  have mem1 : t1.mem=state.mem := by simp [t1, walkRows, chunkAddrRows, execInstrBr, mem_of_reg, mem_of_set]
  have keep1 (r : Reg) (h : r ≠ .x7) : t1.getReg r=state.getReg r := by
    simp [t1, walkRows, chunkAddrRows, execInstrBr, Ne.symm h]
  have ctx1 : CapContext groups t1 := context.of_preserved
    (fun r m => keep1 r (by intro e; subst e; simp at m))
    (fun n _ _ => congrFun mem1 (BitVec.ofNat 64 (Opening.markBase+8*n)))
  have mark (j : Nat) (hj : j<8) :
      t1.getMem (t1.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*j)))=
        BitVec.ofNat 64 (capIsMarked groups (8*node+j) 0).toNat := by
    rw [x7]; exact leaf_mark groups t1 ctx1 node j span hj
  have valid (j : Nat) (hj : j<8) : accessValid (t1.getReg .x7+signExtend12 (BitVec.ofNat 12 (8*j))) 8=true := by
    rw [x7, show signExtend12 (BitVec.ofNat 12 (8*j))=BitVec.ofNat 64 (8*j) by interval_cases j <;> decide,
      ← BitVec.ofNat_add]
    have memSize : MEMORY_BYTES=68719476736 := rfl
    exact Opening.aligned_access _ (by omega) (by omega)
  -- first mark row
  let t1b := execInstrBr t1 (.LD .x28 .x7 0)
  have legal1b : legal [(8194,.LD .x28 .x7 0)] t1 := by
    simp only [legal]
    refine ⟨pc1, ?_, trivial⟩
    have v := valid 0 (by decide)
    simp at v
    simp [ordinaryStep, memoryArgumentsValid, memAccess, v]
  have x28b : t1b.getReg .x28=BitVec.ofNat 64 (capIsMarked groups (8*node+0) 0).toNat := by
    have e : t1b.getReg .x28=t1.getMem (t1.getReg .x7+signExtend12 0) := by simp [t1b, execInstrBr]
    rw [e]; exact mark 0 (by decide)
  have pcb : t1b.pc=address 8195 := by show t1.pc+4=_; rw [pc1, address_succ]
  have memb : t1b.mem=t1.mem := by simp [t1b, execInstrBr, mem_of_reg, mem_of_set]
  have keepb (r : Reg) (h : r ≠ .x28) : t1b.getReg r=t1.getReg r := by simp [t1b, execInstrBr, Ne.symm h]
  -- the other seven mark rows
  obtain ⟨legalT, pcT, x28T, memT, keepT⟩ := mask_tail_run (fun i => (capIsMarked groups (8*node+i) 0).toNat)
    7 1 8195 t1b (by decide) pcb (fun i h1 h2 => by
      rw [keepb .x7 (by decide), get_mem_of memb]
      exact ⟨mark i (by omega), valid i (by omega)⟩)
  let t2 := walkRows t1b (maskTail 8195 1 7)
  have x28_2 : t2.getReg .x28=BitVec.ofNat 64 (leafMask groups node) := by
    show (walkRows t1b (maskTail 8195 1 7)).getReg .x28=_
    rw [x28T, x28b]
    simp only [List.range', List.foldl]
    rw [mask_combine]
    rfl
  have pc2 : t2.pc=address 8216 := pcT
  -- jump rows
  have legal3 : legal chunkJumpRows t2 := by
    simp only [chunkJumpRows, legal]
    exact ⟨pc2, rfl, by show t2.pc+4=address 8217; rw [pc2, address_succ], rfl,
      by show t2.pc+4+4=address 8218; rw [pc2, address_succ, address_succ], rfl,
      by show t2.pc+4+4+4=address 8219; rw [pc2, address_succ, address_succ, address_succ], rfl, trivial⟩
  have pc3 : (walkRows t2 chunkJumpRows).pc=BitVec.ofNat 64 (4096+4*chunkBlockWord (leafMask groups node)) := by
    have e : (walkRows t2 chunkJumpRows).pc=((BitVec.signExtend 64 ((9 : BitVec 20).zeroExtend 32 <<< 12)+
        (t2.getReg .x28 <<< (6 : BitVec 6).toNat))+signExtend12 128) &&& ~~~1#64 := rfl
    rw [e, x28_2]
    exact jump_target _ (leaf_mask_lt groups node)
  have whole : walkRows state chunkRows=walkRows t2 chunkJumpRows := by
    simp only [chunkRows, chunkMaskRows, walk_join]; rfl
  have legalAll : legal chunkRows state := by
    unfold chunkRows chunkMaskRows
    refine legal_append _ _ _ (legal_append _ _ _ legal1 (legal_append _ _ _ legal1b ?_)) ?_
    · exact legalT
    · rw [walk_join]; exact legal3
  refine ⟨fun fuel coins => ?_, by rw [whole]; exact pc3, ?_, ?_⟩
  · have h := walk_rows_run state chunkRows legalAll chunk_rows_present fuel coins
    rw [chunk_rows_price] at h
    exact h
  · rw [whole]
    have : (walkRows t2 chunkJumpRows).mem=t2.mem := by
      simp [walkRows, chunkJumpRows, execInstrBr, mem_of_reg, mem_of_set]
    rw [this]
    show (walkRows t1b (maskTail 8195 1 7)).mem=_
    rw [memT, memb, mem1]
  · intro r a b c d
    rw [whole]
    have : (walkRows t2 chunkJumpRows).getReg r=t2.getReg r := by
      simp [walkRows, chunkJumpRows, execInstrBr, Ne.symm b, Ne.symm d]
    rw [this]
    show (walkRows t1b (maskTail 8195 1 7)).getReg r=_
    rw [keepT r b c, keepb r b, keep1 r a]

/-- A marked level-5 node from the chunk jump at 708 back to the advance block, its frontier emitted. -/
theorem chunk_run (emit : EmitCap238) (groups : List Nat) (heap : Nat → BitVec 256) (capStart : Nat)
    (vs : List (BitVec 256)) (state : MachineState) (node : Nat) (span : CapSpan node 3)
    (run : CapRun groups heap capStart vs state node) (level : state.getReg .x16=BitVec.ofNat 64 (8*node))
    (pc : state.pc=0x1b10) (mark : capIsMarked groups node 3=true)
    (separate : proofBase ≤ capStart) (aligned : capStart%2=0)
    (fits : capStart+capOffset (vs.length+(capFrontierNodes groups node 3).length)+2 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (31+entriesCycles (chunkEntries (leafMask groups node)) capStart vs.length) ∧
      after.pc=0x1afc ∧
      CapRun groups heap capStart (vs++(capFrontierNodes groups node 3).map heap) after node ∧
      (∀ a<2^64, a<capStart ∨ capStart+capOffset (vs.length+(capFrontierNodes groups node 3).length) ≤ a →
        after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) := by
  have lo := span.start
  have hi := span.finish
  simp only [Nat.reducePow] at lo hi
  have hn : node<64 := by omega
  set mask := leafMask groups node with hmask
  have hm : mask<256 := leaf_mask_lt groups node
  have nz : mask ≠ 0 := by
    have := (mask_marked_iff mask hm).mp (by rw [hmask, ← chunk_marked]; exact mark)
    exact this
  let s1 := state.setPC 0x9000
  have r1 : RunsOpeningBlock state s1 1 := fun fuel coins => execute_chunk_jump state pc fuel coins
  have run1 : CapRun groups heap capStart vs s1 node := run.of_kept (fun _ _ => rfl) rfl
  obtain ⟨r2, pc2, mem2, keep2⟩ := chunk_code_run groups s1 node run1.position.context span level rfl
  let s2 := walkRows s1 chunkRows
  have run2 : CapRun groups heap capStart vs s2 node := run1.of_kept (fun r m => keep2 r
    (by intro e; subst e; simp at m) (by intro e; subst e; simp at m) (by intro e; subst e; simp at m)
    (by intro e; subst e; simp at m)) mem2
  have level2 : s2.getReg .x16=BitVec.ofNat 64 (8*node) :=
    (keep2 .x16 (by decide) (by decide) (by decide) (by decide)).trans level
  have code : BlockAt (chunkEntries mask) (chunkBlockWord mask) := fun j hj => block_instr mask j hm nz hj
  have fitsBlock := block_fits mask hm nz
  have hw : chunkBlockWord mask=8224+16*mask := rfl
  have count : (capFrontierNodes groups node 3).length=(chunkEntries mask).length := chunk_count groups node
  obtain ⟨final, r3, pc3, run3, frame3⟩ :=
    entries_run emit groups heap capStart node hn separate aligned (chunkEntries mask) (chunkBlockWord mask) vs s2 node
      code (by omega) (by omega) (chunk_entries_range mask hm nz)
      pc2 level2 run2 (by rw [← count]; exact fits)
  refine ⟨final, ?_, pc3, ?_, ?_⟩
  · have chain := (r1.next r2).next r3
    convert chain using 1
    omega
  · rw [chunk_frontier, List.map_map]
    simpa [List.map_map] using run3
  · intro a fit far
    rw [frame3 a fit (by rw [← count]; exact far)]
    exact (byte_of_mem mem2 _).trans (byte_of_mem rfl _)

end TwoPermutationPrototype.GroupedOpening
