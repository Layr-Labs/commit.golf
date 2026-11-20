import CommitGolfCandidate.K1CheckALeaf

/-! # The K1 A-leaf routine as one run: two permutation calls, the leaf digest and the frame -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-- What the A routine reads at word 500. -/
structure AReady (e : MachineState) (src proof : Nat) (index : Index) : Prop where
  pc : e.pc = BitVec.ofNat 64 (4096+4*500)
  source : e.getReg .x19 = wordAddress src
  proofPtr : e.getReg .x21 = BitVec.ofNat 64 proof
  scratch : e.getReg .x4 = 12272
  digest : e.getReg .x23 = wordAddress 1536
  selector : e.getReg .x5 = 0
  tagBase : e.getReg .x3 = 4056
  node : e.getReg .x6 = BitVec.ofNat 64 index.val
  ahead : isAHead index = true
  srcLow : 4096 ≤ src
  srcHigh : src + 37 ≤ 2^33
  proofLow : 12288 ≤ proof
  proofHigh : proof + 16 ≤ MEMORY_BYTES
  proofEven : proof % 2 = 0

theorem word_offset (a b off : Nat) (h : (8*a + off) % 2^64 = (8*b) % 2^64) :
    wordAddress a + BitVec.ofNat 64 off = wordAddress b := by
  unfold wordAddress
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact h

private theorem write_bits_pc {bits : Nat} (s : MachineState) (a : Word) (v : BitVec bits) :
    (writeBits s a v).pc = s.pc + 4 := by
  unfold writeBits; rfl

private theorem write_bits_mem_view (s : MachineState) (dst w : Nat) (v : BitVec 1600)
    (dstBound : dst + 25 ≤ 2^33) (bounded : w < 2^33) :
    memoryView (writeBits s (wordAddress dst) v) w = writeWindow (memoryView s) dst (replyWords v) w :=
  permutation_write_memory s dst w v dstBound bounded

/-! ### Registers and memory up to the first call -/

section
variable {e : MachineState} {src proof : Nat} {index : Index}

theorem a_staged_ready (ready : AReady e src proof index) : CopyReady aNonceCode (aSetup e) proof 12272 0 := by
  obtain ⟨pc, _, _, _, _, _, kept⟩ := a_setup_post e
  have lim := ready.proofHigh
  refine ⟨?_, ?_, ?_, ?_, ?_, ready.proofEven, by decide⟩
  · change (aSetup e).pc = BitVec.ofNat 64 (4096+4*(505+2*0))
    rw [pc, ready.pc, show (20 : Word) = BitVec.ofNat 64 20 from rfl, ← BitVec.ofNat_add]
  · change (aSetup e).getReg .x21 = _
    rw [kept .x21 (by decide) (by decide) (by decide) (by decide), ready.proofPtr]
  · change (aSetup e).getReg .x4 + BitVec.ofNat 64 0 = _
    rw [kept .x4 (by decide) (by decide) (by decide) (by decide), ready.scratch]; rfl
  · exact lim
  · change 12272 + 2*8 ≤ MEMORY_BYTES; decide

theorem a_staged_pc (ready : AReady e src proof index) : (aStaged e).pc = BitVec.ofNat 64 (4096+4*521) :=
  copy_field_pc aNonceCode (aSetup e) proof 12272 (a_staged_ready ready)

theorem a_staged_register (r : Reg) (h28 : r ≠ .x28) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h13 : r ≠ .x13)
    (h31 : r ≠ .x31) : (aStaged e).getReg r = e.getReg r :=
  (copy_field_register aNonceCode (aSetup e) r h31).trans ((a_setup_post e).2.2.2.2.2.2 r h28 h10 h11 h13)

theorem a_staged_view (ready : AReady e src proof index) (w : Nat) (bound : w < 2^33)
    (outside : w < 1534 ∨ 1536 ≤ w) : memoryView (aStaged e) w = memoryView e w := by
  have room := ready.proofHigh
  have low := ready.proofLow
  have frame := (code_bytes aNonceCode (aSetup e) proof 12272 (a_staged_ready ready) (by omega)).2
  apply Eq.trans (word_eq_of_byte_frame (aSetup e) (aStaged e) w ?_)
  · exact congrFun (a_setup_post e).2.1 _
  · intro i hi
    apply frame
    intro j hj eq
    have same := congrArg BitVec.toNat eq
    have one : 8*w+i<2^64 := by omega
    change j<16 at hj
    have two : 12272+j<2^64 := by omega
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt one,BitVec.toNat_ofNat,Nat.mod_eq_of_lt two] at same
    omega

theorem a_staged_read (ready : AReady e src proof index) :
    readBuffer (aStaged e) 12272 16 = readBuffer e proof 16 := by
  have low := ready.proofLow
  have bytes := (code_bytes aNonceCode (aSetup e) proof 12272 (a_staged_ready ready) (by omega)).1
  have mem := (a_setup_post e).2.1
  unfold readBuffer aStaged
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [bytes i (by have := Finset.mem_range.mp hi; change i < 16; omega)]
  simp only [MachineState.getByte, MachineState.getMem, mem]

theorem a_call_one_pc (ready : AReady e src proof index) : (aCallOne e).pc = BitVec.ofNat 64 (4096+4*523) := by
  rw [aCallOne, (a_scratch_post (aStaged e)).1, a_staged_pc ready]; rfl

theorem a_call_one_register (r : Reg) (h28 : r ≠ .x28) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h13 : r ≠ .x13)
    (h31 : r ≠ .x31) (h12 : r ≠ .x12) : (aCallOne e).getReg r = e.getReg r :=
  ((a_scratch_post (aStaged e)).2.2.2 r h12).trans (a_staged_register r h28 h10 h11 h13 h31)

theorem a_call_one_view (ready : AReady e src proof index) (w : Nat) (bound : w < 2^33)
    (outside : w < 1534 ∨ 1536 ≤ w) : memoryView (aCallOne e) w = memoryView e w := by
  rw [← a_staged_view ready w bound outside]
  exact congrFun (a_scratch_post (aStaged e)).2.1 _

theorem a_x10 (ready : AReady e src proof index) : (aCallOne e).getReg .x10 = wordAddress (src+12) := by
  rw [aCallOne, (a_scratch_post (aStaged e)).2.2.2 .x10 (by decide), aStaged,
    copy_field_register _ _ _ (by decide), (a_setup_post e).2.2.2.1, ready.source]
  exact word_offset src (src+12) 96 (by omega)

theorem a_x11 : (aCallOne e).getReg .x11 = 200 := by
  rw [aCallOne, (a_scratch_post (aStaged e)).2.2.2 .x11 (by decide), aStaged,
    copy_field_register _ _ _ (by decide), (a_setup_post e).2.2.2.2.1]

theorem a_x13 : (aCallOne e).getReg .x13 = 1 := by
  rw [aCallOne, (a_scratch_post (aStaged e)).2.2.2 .x13 (by decide), aStaged,
    copy_field_register _ _ _ (by decide), (a_setup_post e).2.2.2.2.2.1]

theorem a_x28 (ready : AReady e src proof index) :
    (aCallOne e).getReg .x28 = BitVec.ofNat 64 (4056 + 256*index.val) := by
  rw [aCallOne, (a_scratch_post (aStaged e)).2.2.2 .x28 (by decide), aStaged,
    copy_field_register _ _ _ (by decide), (a_setup_post e).2.2.1, ready.tagBase, ready.node,
    BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 4056 + BitVec.ofNat 64 index.val * BitVec.ofNat 64 256 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index.val]

theorem a_first_window (ready : AReady e src proof index) :
    window (memoryView (aCallOne e)) (src+12) = pinnedFirstInput index (window (memoryView e) (src+5)) := by
  funext i
  have low := ready.srcLow
  have high := ready.srcHigh
  have bounded := i.isLt
  simp only [pinnedFirstInput, if_pos ready.ahead, window]
  rw [a_call_one_view ready (src+12+i.val) (by omega) (Or.inr (by omega))]
  congr 1
  omega

end

/-! ### The second call -/

section
variable {e : MachineState} {src proof : Nat} {index : Index}

private theorem sx_msg (k : Nat) (small : k < 16) :
    signExtend12 (BitVec.ofNat 12 (4040+8*k)) = BitVec.ofNat 64 (2^64 - 56 + 8*k) := by
  interval_cases k <;> decide

private theorem sx_dst (k : Nat) (small : k < 16) :
    signExtend12 (BitVec.ofNat 12 (200+8*k)) = BitVec.ofNat 64 (200+8*k) := by
  interval_cases k <;> decide

private theorem sx_salt (k : Nat) (small : k < 2) :
    signExtend12 (BitVec.ofNat 12 (8*k)) = BitVec.ofNat 64 (8*k) := by
  interval_cases k <;> decide

private theorem sx_salt_dst (k : Nat) (small : k < 2) :
    signExtend12 (BitVec.ofNat 12 (328+8*k)) = BitVec.ofNat 64 (328+8*k) := by
  interval_cases k <;> decide

theorem a_x12 {e : MachineState} : (aCallOne e).getReg .x12 = wordAddress 1152 :=
  (a_scratch_post (aStaged e)).2.2.1

theorem a_msg_ready (ready : AReady e src proof index) (a : Block) :
    DReady aMsgCopy (aFirstReply e a) (src+5) 1177 0 := by
  have low := ready.srcLow
  have high := ready.srcHigh
  have x10 : (aFirstReply e a).getReg .x10 = wordAddress (src+12) := by
    rw [aFirstReply, writeBits_register]; exact a_x10 ready
  have x12 : (aFirstReply e a).getReg .x12 = wordAddress 1152 := by
    rw [aFirstReply, writeBits_register]; exact a_x12
  refine ⟨?_, ?_, ?_, by change src+5+16 ≤ 2^33; omega, by decide, Or.inr (by change 1177+16 ≤ src+5; omega)⟩
  · rw [aFirstReply, write_bits_pc, a_call_one_pc ready]; rfl
  · intro k hk
    change k < 16 at hk
    change (aFirstReply e a).getReg .x10 + signExtend12 (BitVec.ofNat 12 (4040+8*k)) = _
    rw [x10, sx_msg k hk]
    exact word_offset _ _ _ (by omega)
  · intro k hk
    change k < 16 at hk
    change (aFirstReply e a).getReg .x12 + signExtend12 (BitVec.ofNat 12 (200+8*k)) = _
    rw [x12, sx_dst k hk]
    exact word_offset _ _ _ (by omega)

def aMsgCopied (e : MachineState) (a : Block) : MachineState := dcopy aMsgCopy (aFirstReply e a)

theorem a_msg_register (a : Block) (r : Reg) (h31 : r ≠ .x31) :
    (aMsgCopied e a).getReg r = (aCallOne e).getReg r := by
  rw [aMsgCopied, dcopy_register _ _ _ h31, aFirstReply, writeBits_register]

theorem a_salt_ready (ready : AReady e src proof index) (a : Block) :
    DReady aSaltCopy (aMsgCopied e a) 1534 1193 0 := by
  have x4 : (aMsgCopied e a).getReg .x4 = wordAddress 1534 := by
    rw [a_msg_register a .x4 (by decide), a_call_one_register .x4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), ready.scratch]; rfl
  have x12 : (aMsgCopied e a).getReg .x12 = wordAddress 1152 := by
    rw [a_msg_register a .x12 (by decide)]; exact a_x12
  refine ⟨?_, ?_, ?_, by decide, by decide, Or.inr (by decide)⟩
  · rw [aMsgCopied, dcopy_pc _ _ _ _ (a_msg_ready ready a)]; rfl
  · intro k hk
    change k < 2 at hk
    change (aMsgCopied e a).getReg .x4 + signExtend12 (BitVec.ofNat 12 (8*k)) = _
    rw [x4, sx_salt k hk]
    exact word_offset _ _ _ (by omega)
  · intro k hk
    change k < 2 at hk
    change (aMsgCopied e a).getReg .x12 + signExtend12 (BitVec.ofNat 12 (328+8*k)) = _
    rw [x12, sx_salt_dst k hk]
    exact word_offset _ _ _ (by omega)

theorem a_copied_pc (ready : AReady e src proof index) (a : Block) :
    (aCopied e a).pc = BitVec.ofNat 64 (4096+4*560) := by
  change (dcopy aSaltCopy (aMsgCopied e a)).pc = _
  rw [dcopy_pc _ _ _ _ (a_salt_ready ready a)]; rfl

theorem a_copied_register (a : Block) (r : Reg) (h31 : r ≠ .x31) :
    (aCopied e a).getReg r = (aCallOne e).getReg r := by
  change (dcopy aSaltCopy (aMsgCopied e a)).getReg r = _
  rw [dcopy_register _ _ _ h31, a_msg_register a r h31]

private theorem a_tag_address : wordAddress 1152 + signExtend12 160 = wordAddress 1172 := by decide

private theorem a_tag_value (ready : AReady e src proof index) :
    BitVec.ofNat 64 (4056 + 256*index.val) + signExtend12 4080 = pinnedPositionTag index := by
  have bound : index.val < 2^24 := index.isLt
  rw [show signExtend12 4080 = BitVec.ofNat 64 (2^64-16) by decide, ← BitVec.ofNat_add]
  unfold pinnedPositionTag
  rw [if_pos ready.ahead]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem a_call_two_pc (ready : AReady e src proof index) (a : Block) :
    (aCallTwo e a).pc = BitVec.ofNat 64 (4096+4*564) := by
  rw [aCallTwo, (a_tail_post (aCopied e a)).1, a_copied_pc ready a]; rfl

theorem a_call_two_register (a : Block) (r : Reg) (h28 : r ≠ .x28) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h13 : r ≠ .x13) (h31 : r ≠ .x31) (h12 : r ≠ .x12) : (aCallTwo e a).getReg r = e.getReg r := by
  rw [aCallTwo, (a_tail_post (aCopied e a)).2.2.2.2 r h10 h12 h31, a_copied_register a r h31]
  exact a_call_one_register r h28 h10 h11 h13 h31 h12

theorem a_call_two_view (ready : AReady e src proof index) (a : Block) (w : Nat) (bounded : w < 2^33) :
    memoryView (aCallTwo e a) w = writeWord (memoryView (aCopied e a)) 1172 (pinnedPositionTag index) w := by
  have mem := (a_tail_post (aCopied e a)).2.2.2.1
  have x12 : (aCopied e a).getReg .x12 = wordAddress 1152 := by
    rw [a_copied_register a .x12 (by decide)]; exact a_x12
  have x28 : (aCopied e a).getReg .x28 = BitVec.ofNat 64 (4056 + 256*index.val) := by
    rw [a_copied_register a .x28 (by decide)]; exact a_x28 ready
  rw [x12, x28, a_tag_address, a_tag_value ready] at mem
  calc memoryView (aCallTwo e a) w
      = memoryView ((aCopied e a).setMem (wordAddress 1172) (pinnedPositionTag index)) w :=
        congrFun mem (wordAddress w)
    _ = _ := memory_at_store (by decide) (by omega)

theorem a_store_access (a : Block) :
    accessValid ((aCopied e a).getReg .x12 + signExtend12 160) 8 = true := by
  rw [a_copied_register a .x12 (by decide), a_x12, a_tag_address]
  exact aligned_access _ (by decide)

/-- Memory seen by the second call, word by word. -/
theorem a_copied_view (ready : AReady e src proof index) (a : Block) (w : Nat) (bounded : w < 2^33) :
    memoryView (aCopied e a) w =
      if 1193 ≤ w ∧ w < 1195 then memoryView (aStaged e) (1534 + (w - 1193))
      else if 1177 ≤ w ∧ w < 1193 then memoryView e (src + 5 + (w - 1177))
      else if h : 1152 ≤ w ∧ w < 1177 then replyWords a ⟨w - 1152, by omega⟩
      else memoryView (aCallOne e) w := by
  have low := ready.srcLow
  have high := ready.srcHigh
  have firstView (x : Nat) (xb : x < 2^33) :
      memoryView (aFirstReply e a) x = writeWindow (memoryView (aCallOne e)) 1152 (replyWords a) x :=
    write_bits_mem_view _ 1152 x a (by decide) xb
  have msgView (x : Nat) (xb : x < 2^33) := dcopy_view aMsgCopy (aFirstReply e a) (src+5) 1177
    (a_msg_ready ready a) x xb
  have saltView := dcopy_view aSaltCopy (aMsgCopied e a) 1534 1193 (a_salt_ready ready a) w bounded
  change memoryView (dcopy aSaltCopy (aMsgCopied e a)) w = _
  rw [saltView]
  change (if 1193 ≤ w ∧ w < 1193 + 2 then memoryView (aMsgCopied e a) (1534 + (w - 1193))
    else memoryView (aMsgCopied e a) w) = _
  by_cases salt : 1193 ≤ w ∧ w < 1195
  · have s1 : 1193 ≤ w ∧ w < 1193 + 2 := salt
    have m1 : ¬ (1177 ≤ 1534 + (w - 1193) ∧ 1534 + (w - 1193) < 1177 + 16) := by omega
    have r1 : ¬ (1152 ≤ 1534 + (w - 1193) ∧ 1534 + (w - 1193) < 1152 + 25) := by omega
    rw [if_pos s1, if_pos salt, aMsgCopied, msgView (1534 + (w - 1193)) (by omega)]
    change (if 1177 ≤ 1534 + (w - 1193) ∧ 1534 + (w - 1193) < 1177 + 16 then
      memoryView (aFirstReply e a) (src + 5 + (1534 + (w - 1193) - 1177))
      else memoryView (aFirstReply e a) (1534 + (w - 1193))) = _
    rw [if_neg m1, firstView (1534 + (w - 1193)) (by omega), writeWindow, dif_neg r1]
    exact congrFun (a_scratch_post (aStaged e)).2.1 _
  · have s1 : ¬ (1193 ≤ w ∧ w < 1193 + 2) := salt
    rw [if_neg s1, if_neg salt, aMsgCopied, msgView w bounded]
    change (if 1177 ≤ w ∧ w < 1177 + 16 then memoryView (aFirstReply e a) (src + 5 + (w - 1177))
      else memoryView (aFirstReply e a) w) = _
    by_cases msg : 1177 ≤ w ∧ w < 1193
    · have m1 : 1177 ≤ w ∧ w < 1177 + 16 := msg
      have r1 : ¬ (1152 ≤ src + 5 + (w - 1177) ∧ src + 5 + (w - 1177) < 1152 + 25) := by omega
      rw [if_pos m1, if_pos msg, firstView (src + 5 + (w - 1177)) (by omega), writeWindow, dif_neg r1,
        a_call_one_view ready (src + 5 + (w - 1177)) (by omega) (Or.inr (by omega))]
    · have m1 : ¬ (1177 ≤ w ∧ w < 1177 + 16) := msg
      rw [if_neg m1, if_neg msg, firstView w bounded, writeWindow]

theorem a_second_window (ready : AReady e src proof index) (a : Block) :
    window (memoryView (aCallTwo e a)) 1170 =
      pinnedSecondInput index (checkerNonce (aStaged e)) (replyWords a) (window (memoryView e) (src+5)) := by
  have nonce : checkerNonce (aStaged e) = window (memoryView (aStaged e)) 1534 := by
    apply checker_nonce_words
    rw [a_staged_register .x4 (by decide) (by decide) (by decide) (by decide) (by decide), ready.scratch]; rfl
  funext i
  have bounded := i.isLt
  have low := ready.srcLow
  have high := ready.srcHigh
  change memoryView (aCallTwo e a) (1170 + i.val) = _
  rw [a_call_two_view ready a (1170 + i.val) (by omega), nonce]
  unfold pinnedSecondInput
  rw [if_pos ready.ahead]
  simp only [writeWord, window]
  by_cases tag : i.val = 2
  · have t1 : 1170 + i.val = 1172 := by omega
    rw [if_pos t1, if_pos tag]
  · have t1 : ¬ (1170 + i.val = 1172) := by omega
    rw [if_neg t1, if_neg tag, a_copied_view ready a (1170 + i.val) (by omega)]
    by_cases chain : i.val < 7
    · have c1 : ¬ (1193 ≤ 1170 + i.val ∧ 1170 + i.val < 1195) := by omega
      have c2 : ¬ (1177 ≤ 1170 + i.val ∧ 1170 + i.val < 1193) := by omega
      have c3 : 1152 ≤ 1170 + i.val ∧ 1170 + i.val < 1177 := by omega
      rw [dif_pos chain, if_neg c1, if_neg c2, dif_pos c3]
      congr 1
      apply Fin.ext
      change 1170 + i.val - 1152 = i.val + 18
      omega
    · rw [dif_neg chain]
      by_cases msg : i.val < 23
      · have c1 : ¬ (1193 ≤ 1170 + i.val ∧ 1170 + i.val < 1195) := by omega
        have c2 : 1177 ≤ 1170 + i.val ∧ 1170 + i.val < 1193 := by omega
        rw [dif_pos msg, if_neg c1, if_pos c2]
        congr 1
        omega
      · have c1 : 1193 ≤ 1170 + i.val ∧ 1170 + i.val < 1195 := by omega
        rw [dif_neg msg, if_pos c1]
        congr 1
        omega

/-! ### The whole routine, words 500–564 -/

theorem a_call_two_regs (ready : AReady e src proof index) (a : Block) :
    (aCallTwo e a).getReg .x10 = wordAddress 1170 ∧ (aCallTwo e a).getReg .x12 = wordAddress 1536 ∧
      (aCallTwo e a).getReg .x5 = 0 ∧ (aCallTwo e a).getReg .x11 = 200 ∧ (aCallTwo e a).getReg .x13 = 1 := by
  obtain ⟨_, x10, x12, _, kept⟩ := a_tail_post (aCopied e a)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [aCallTwo, x10, a_copied_register a .x12 (by decide), a_x12]
    exact word_offset 1152 1170 144 (by decide)
  · rw [aCallTwo, x12, a_copied_register a .x23 (by decide),
      a_call_one_register .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ready.digest]
  · rw [a_call_two_register a .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ready.selector]
  · rw [aCallTwo, kept .x11 (by decide) (by decide) (by decide), a_copied_register a .x11 (by decide), a_x11]
  · rw [aCallTwo, kept .x13 (by decide) (by decide) (by decide), a_copied_register a .x13 (by decide), a_x13]

attribute [local irreducible] execute in
theorem execute_a_second (ready : AReady e src proof index) (a : Block) (fuel : Nat) :
    execute packedImage (41+fuel) (writeBits (aCallOne e) (wordAddress 1152) a) false = (do
      let b ← World.query (.inr (.inr (.inl (packBuffer
        (pinnedSecondInput index (checkerNonce (aStaged e)) (replyWords a) (window (memoryView e) (src+5)))))))
      let r ← execute packedImage fuel (aSecondReply e a b) false
      return r.charge 48 1) := by
  have m : execute packedImage (32+(4+(4+(fuel+1)))) (aFirstReply e a) false = (do
      let result ← execute packedImage (4+(4+(fuel+1))) (aMsgCopied e a) false
      return result.charge 32 0) :=
    dcopy_execute aMsgCopy (aFirstReply e a) (src+5) 1177 (a_msg_ready ready a) _ false
  have sl : execute packedImage (4+(4+(fuel+1))) (aMsgCopied e a) false = (do
      let result ← execute packedImage (4+(fuel+1)) (aCopied e a) false
      return result.charge 4 0) :=
    dcopy_execute aSaltCopy (aMsgCopied e a) 1534 1193 (a_salt_ready ready a) _ false
  have t : execute packedImage (4+(fuel+1)) (aCopied e a) false = (do
      let result ← execute packedImage (fuel+1) (aCallTwo e a) false
      return result.charge 4 0) :=
    execute_a_tail (aCopied e a) (a_copied_pc ready a) (a_store_access a) (fuel+1)
  obtain ⟨x10, x12, x5, x11, x13⟩ := a_call_two_regs ready a
  have call := execute_permutation_call packedImage fuel (aCallTwo e a) false 1170 1536 (by decide) (by decide)
    x10 x12 x5 x11 x13 (fetch_at _ 564 .ECALL (by decide) (a_call_two_pc ready a) rfl)
  rw [a_second_window ready a] at call
  rw [show 41+fuel = 32+(4+(4+(fuel+1))) by omega, show writeBits (aCallOne e) (wordAddress 1152) a = aFirstReply e a
    from rfl, m, sl, t, call]
  simp only [bind_assoc, pure_bind, aSecondReply]
  simp [Execution.charge, ← Nat.add_assoc]

attribute [local irreducible] execute in
theorem execute_a_leaf (ready : AReady e src proof index) (fuel : Nat) :
    execute packedImage (65+fuel) e false = (do
      let a ← World.query (.inr (.inr (.inl (packBuffer (pinnedFirstInput index (window (memoryView e) (src+5)))))))
      let b ← World.query (.inr (.inr (.inl (packBuffer
        (pinnedSecondInput index (checkerNonce (aStaged e)) (replyWords a) (window (memoryView e) (src+5)))))))
      let r ← execute packedImage fuel (aSecondReply e a b) false
      return r.charge 79 2) := by
  have low := ready.srcLow
  have high := ready.srcHigh
  have setup := execute_a_setup e ready.pc (16+(2+((41+fuel)+1)))
  have copy : execute packedImage (16+(2+((41+fuel)+1))) (aSetup e) false = (do
      let result ← execute packedImage (2+((41+fuel)+1)) (aStaged e) false
      return result.charge 16 0) :=
    copy_field_execute aNonceCode (aSetup e) proof 12272 (a_staged_ready ready) _ false
  have scratch : execute packedImage (2+((41+fuel)+1)) (aStaged e) false = (do
      let result ← execute packedImage ((41+fuel)+1) (aCallOne e) false
      return result.charge 2 0) :=
    execute_a_scratch (aStaged e) (a_staged_pc ready) ((41+fuel)+1)
  have x5 : (aCallOne e).getReg .x5 = 0 := by
    rw [a_call_one_register .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ready.selector]
  have call := execute_permutation_call packedImage (41+fuel) (aCallOne e) false (src+12) 1152 (by omega)
    (by decide) (a_x10 ready) a_x12 x5 a_x11 a_x13 (fetch_at _ 523 .ECALL (by decide) (a_call_one_pc ready) rfl)
  rw [a_first_window ready] at call
  rw [show 65+fuel = 5+(16+(2+((41+fuel)+1))) by omega, setup, copy, scratch, call]
  simp only [bind_assoc, pure_bind, execute_a_second ready]
  simp [Execution.charge, ← Nat.add_assoc]

/-! ### After the routine: PC, registers, digest, frame -/

theorem a_second_pc (ready : AReady e src proof index) (a b : Block) :
    (aSecondReply e a b).pc = BitVec.ofNat 64 (4096+4*565) := by
  rw [aSecondReply, write_bits_pc, a_call_two_pc ready a]; rfl

theorem a_second_register (a b : Block) (r : Reg) (h28 : r ≠ .x28) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h13 : r ≠ .x13) (h31 : r ≠ .x31) (h12 : r ≠ .x12) : (aSecondReply e a b).getReg r = e.getReg r := by
  rw [aSecondReply, writeBits_register]
  exact a_call_two_register a r h28 h10 h11 h13 h31 h12

theorem a_second_x11 (ready : AReady e src proof index) (a b : Block) : (aSecondReply e a b).getReg .x11 = 200 := by
  rw [aSecondReply, writeBits_register]; exact (a_call_two_regs ready a).2.2.2.1

theorem a_second_x13 (ready : AReady e src proof index) (a b : Block) : (aSecondReply e a b).getReg .x13 = 1 := by
  rw [aSecondReply, writeBits_register]; exact (a_call_two_regs ready a).2.2.2.2

theorem a_second_digest (a b : Block) : readBuffer (aSecondReply e a b) 12288 32 = outputDigest b := by
  unfold aSecondReply
  simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
    write_bits_digest (aCallTwo e a) 12288 0 b (by decide) (by decide)

theorem a_second_frame (ready : AReady e src proof index) (a b : Block) (w : Nat) (bounded : w < 2^33)
    (outside : w < 1152 ∨ 1561 ≤ w) : memoryView (aSecondReply e a b) w = memoryView e w := by
  change BitVec 1600 at b
  show memoryView (writeBits (aCallTwo e a) (wordAddress 1536) b) w = _
  rw [write_bits_mem_view _ 1536 w b (by decide) bounded, writeWindow]
  by_cases low : w < 1152
  · have r1 : ¬ (1536 ≤ w ∧ w < 1536 + 25) := by omega
    have t1 : ¬ (w = 1172) := by omega
    rw [dif_neg r1, a_call_two_view ready a w bounded, writeWord, if_neg t1, a_copied_view ready a w bounded]
    have c1 : ¬ (1193 ≤ w ∧ w < 1195) := by omega
    have c2 : ¬ (1177 ≤ w ∧ w < 1193) := by omega
    have c3 : ¬ (1152 ≤ w ∧ w < 1177) := by omega
    rw [if_neg c1, if_neg c2, dif_neg c3, a_call_one_view ready w bounded (Or.inl (by omega))]
  · have r1 : ¬ (1536 ≤ w ∧ w < 1536 + 25) := by omega
    have t1 : ¬ (w = 1172) := by omega
    rw [dif_neg r1, a_call_two_view ready a w bounded, writeWord, if_neg t1, a_copied_view ready a w bounded]
    have c1 : ¬ (1193 ≤ w ∧ w < 1195) := by omega
    have c2 : ¬ (1177 ≤ w ∧ w < 1193) := by omega
    have c3 : ¬ (1152 ≤ w ∧ w < 1177) := by omega
    rw [if_neg c1, if_neg c2, dif_neg c3, a_call_one_view ready w bounded (Or.inr (by omega))]

end

end TwoPermutationPrototype.Packed.RecordLeaf
