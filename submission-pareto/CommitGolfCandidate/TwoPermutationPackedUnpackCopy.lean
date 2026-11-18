import CommitGolfCandidate.TwoPermutationPackedUnpackDecode

/-! The back-to-front copy loop of the unpacking wrapper (words 432-478): shared tails. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Unpacked length `48k + 30n`. -/
def lenOf (input : CheckInput) : Nat := 48*input.positions.card + 30*countOf input

def mainMem (input : CheckInput) (m : Nat) (a : Word) : Byte :=
  if scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + countOf input then
    remByte input.proof input.positions.card (countOf input) (a.toNat - scratchBase)
  else if proofBase + m ≤ a.toNat ∧ a.toNat < proofBase + lenOf input then
    unpackedByte input.proof input.positions.card (countOf input) (a.toNat - proofBase)
  else (unpackStart input).getByte a

def mainWrites : List Reg := [.x22,.x23,.x24,.x25,.x26,.x27,.x30,.x31]

structure MainAt (input : CheckInput) (vM : Reg → Nat) (m : Nat) (s : MachineState) : Prop where
  view : ∃ v, View s v ∧ v .x22 = m ∧ ∀ r, r ∉ mainWrites → v r = vM r
  pc : s.pc = BitVec.ofNat 64 (4096+4*432)
  mem : ∀ a, s.getByte a = mainMem input m a

/-- Size facts of a well-formed admitted proof. -/
structure Sizes (input : CheckInput) : Prop where
  k : input.positions.card ≤ 2^24
  n : countOf input ≤ 2^33
  records : 15*input.positions.card ≤ countOf input
  len : lenOf input + 2^27 ≤ 2^33

theorem sizes_of (input : CheckInput) (wf : WellFormed input.positions.card input.proof.length)
    (fits : input.proof.length ≤ 8355061248) : Sizes input := by
  have kb := checker_positions_bound input
  obtain ⟨_, _, r, e⟩ := wf
  simp only [packedLength, bodyLength] at e
  refine ⟨by omega, ?_, r, ?_⟩ <;> simp only [countOf, lenOf] <;> omega

theorem decode_main_mem (input : CheckInput) (a : Word) :
    decodeMem input (countOf input) a = mainMem input (lenOf input) a := by
  unfold decodeMem mainMem
  split_ifs <;> first | rfl | omega

theorem byte_ofNat_toNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  apply BitVec.eq_of_toNat_eq; simp

def writeTail : List Instr := [.ADD .x23 .x22 .x15]

theorem wt_x23 (v : Reg → Nat) (i : Nat) (h22 : v .x22 = i) (h15 : v .x15 = proofBase) (ib : i ≤ 2^34) :
    writeTail.foldl stepV v .x23 = proofBase + i := by
  simp only [writeTail]; vsimp; rw [h22, h15]; unfold proofBase; omega

/-- Words 476-478: store byte `x31` at `proofBase + i` and jump back to the loop test. -/
theorem write_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*476)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (hb : v .x31 = (unpackedByte input.proof input.positions.card (countOf input) (m-1)).toNat) :
    ∃ t, Hop s t 3 3 ∧ MainAt input vM (m-1) t := by
  have h15 : v .x15 = proofBase := (fr .x15 (by decide)).trans mv.x15
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 476 writeTail v hv (by decide) pc
    (by intro i hi; simp only [writeTail, List.length] at hi; interval_cases i <;> rfl) rfl
  have e23 := wt_x23 v (m-1) h22 h15 (by have := sz.len; omega)
  obtain ⟨h4, w4, p4, m4⟩ := sb_step _ _ wA 477 .x23 .x31 0 (by decide) pA rfl
    (proofBase + (m-1)) (by rw [e23, se12_0, Nat.add_zero]) (by have := sz.len; unfold proofBase; omega)
  have j := jal_step _ 478 2096968 (by decide) p4 rfl 432 rfl
  refine ⟨_, (hA.thenDo h4).thenDo j, ⟨⟨_, view_pc_only _ _ _ w4, ?_, ?_⟩, rfl, ?_⟩⟩
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact h22
  · intro r hr
    rw [foldl_stepV_within writeTail mainWrites (by decide) _ r hr]; exact fr r hr
  · intro q
    have len := sz.len
    rw [setPC_getByte, m4, getByte_of_mem mA, mem]
    have hb' : BitVec.ofNat 8 (writeTail.foldl stepV v .x31) =
        unpackedByte input.proof input.positions.card (countOf input) (m-1) := by
      rw [foldl_stepV_notin _ _ _ (by decide), hb, byte_ofNat_toNat]
    rw [hb']
    unfold mainMem
    by_cases hq : q = BitVec.ofNat 64 (proofBase + (m-1))
    · subst hq
      have e : (BitVec.ofNat 64 (proofBase + (m-1))).toNat = proofBase + (m-1) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega)]
      rw [if_pos rfl, e, if_neg (by unfold scratchBase proofBase; omega), if_pos (by omega),
        Nat.add_sub_cancel_left]
    · rw [if_neg hq]
      have hq' : q.toNat ≠ proofBase + (m-1) := by
        intro e; apply hq; apply BitVec.eq_of_toNat_eq
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega)]
      split_ifs <;> first | rfl | omega

/-- The byte the copy loop reads from the packed body is still the original one. -/
theorem read_main (input : CheckInput) (m : Nat) (s : MachineState)
    (mem : ∀ a, s.getByte a = mainMem input m a) (p : Nat) (hp : p < m) (hb : p < 2^33) :
    s.getByte (BitVec.ofNat 64 (proofBase + p)) = input.proof.getD p 0 := by
  rw [mem, mainMem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega),
    if_neg (by unfold scratchBase proofBase; omega), if_neg (by omega)]
  exact start_proof_byte input p (by omega)

theorem read_scratch (input : CheckInput) (m : Nat) (s : MachineState)
    (mem : ∀ a, s.getByte a = mainMem input m a) (j : Nat) (hj : j < countOf input) (nb : countOf input ≤ 2^33) :
    s.getByte (BitVec.ofNat 64 (scratchBase + j)) =
      remByte input.proof input.positions.card (countOf input) j := by
  rw [mem, mainMem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega),
    if_pos (by omega), Nat.add_sub_cancel_left]

/-- Words 472-473 then the write tail: copy packed byte `p`. -/
theorem copy_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*472)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (p : Nat) (h26 : v .x26 = proofBase + p) (hp : p < m)
    (hb : input.proof.getD p 0 = unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 5 5 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step s v hv 472 .x31 .x26 0 (by decide) pc rfl (proofBase + p)
    (by rw [h26, se12_0, Nat.add_zero]) (by unfold proofBase; omega)
  have j := jal_step _ 473 12 (by decide) p1 rfl 476 rfl
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ w1) rfl
    (by rw [setV_ne _ _ _ _ (by decide), h22])
    (fun r hr => by rw [setV_ne _ _ _ _ (fun e => hr (by rw [e]; decide)), fr r hr])
    (fun a => by rw [setPC_getByte, getByte_of_mem m1, mem])
    (by rw [setV_eq _ _ _ (by decide), read_main input m s mem p hp (by omega), hb])
  exact ⟨t, (h1.thenDo j).thenDo ht, at'⟩

def remBlock : List Instr := [.ADD .x31 .x21 .x30]

theorem rb_x31 (v : Reg → Nat) (j : Nat) (h21 : v .x21 = scratchBase) (h30 : v .x30 = j) (jb : j ≤ 2^34) :
    remBlock.foldl stepV v .x31 = scratchBase + j := by
  simp only [remBlock]; vsimp; rw [h21, h30]; unfold scratchBase; omega

/-- Words 474-475 then the write tail: restore byte 29 of digest `j` from scratch. -/
theorem rem_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*474)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (j : Nat) (h30 : v .x30 = j) (hj : j < countOf input)
    (hb : remByte input.proof input.positions.card (countOf input) j =
      unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 5 5 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  have nb := sz.n
  have h21 : v .x21 = scratchBase := (fr .x21 (by decide)).trans mv.x21
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 474 remBlock v hv (by decide) pc
    (by intro i hi; simp only [remBlock, List.length] at hi; interval_cases i <;> rfl) rfl
  have e31 := rb_x31 v j h21 h30 (by omega)
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step _ _ wA 475 .x31 .x31 0 (by decide) pA rfl (scratchBase + j)
    (by rw [e31, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ w1 p1
    (by rw [setV_ne _ _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), h22])
    (fun r hr => by
      rw [setV_ne _ _ _ _ (fun e => hr (by rw [e]; decide)),
        foldl_stepV_within remBlock mainWrites (by decide) _ r hr, fr r hr])
    (fun a => by rw [getByte_of_mem m1, getByte_of_mem mA, mem])
    (by rw [setV_eq _ _ _ (by decide), getByte_of_mem mA, read_scratch input m s mem j hj nb, hb])
  exact ⟨t, (hA.thenDo h1).thenDo ht, at'⟩

end TwoPermutationPrototype.Packed.Checker
