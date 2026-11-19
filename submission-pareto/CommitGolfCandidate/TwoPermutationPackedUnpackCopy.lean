import CommitGolfCandidate.TwoPermutationPackedUnpackHeads

/-! The back-to-front copy loop of the unpacking wrapper (words 445-513): shared tails. -/
namespace TwoPermutationPrototype.Packed.Checker
variable [UnpackOrigin]
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Unpacked length `48k + 30n`. -/
def lenOf (input : CheckInput) : Nat := 48*input.positions.card + 30*countOf input

def mainMem (input : CheckInput) (m : Nat) (a : Word) : Byte :=
  if scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + countOf input + input.positions.card then
    scratchByte input (a.toNat - scratchBase)
  else if proofBase + m ≤ a.toNat ∧ a.toNat < proofBase + lenOf input then
    unpackedByte input.proof input.positions.card (countOf input) (a.toNat - proofBase)
  else (unpackStart input).getByte a

def mainWrites : List Reg := [.x22,.x23,.x24,.x25,.x26,.x30,.x31]

structure MainAt (input : CheckInput) (vM : Reg → Nat) (m : Nat) (s : MachineState) : Prop where
  view : ∃ v, View s v ∧ v .x22 = m ∧ ∀ r, r ∉ mainWrites → v r = vM r
  pc : s.pc = BitVec.ofNat 64 (4096+4*445)
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

theorem head_main_mem (input : CheckInput) (a : Word) :
    headMem input input.positions.card a = mainMem input (lenOf input) a := by
  unfold headMem mainMem
  split_ifs <;> first | omega | rfl

def writeTail : List Instr := [.ADD .x23 .x22 .x15]

theorem wt_x23 (v : Reg → Nat) (i : Nat) (h22 : v .x22 = i) (h15 : v .x15 = proofBase) (ib : i ≤ 2^34) :
    writeTail.foldl stepV v .x23 = proofBase + i := by
  simp only [writeTail]; vsimp; rw [h22, h15]; unfold proofBase; omega

/-- Words 511-513: store byte `x31` at `proofBase + i` and jump back to the loop test. -/
theorem write_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*511)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (hb : BitVec.ofNat 8 (v .x31) = unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 3 3 ∧ MainAt input vM (m-1) t := by
  have h15 : v .x15 = proofBase := (fr .x15 (by decide)).trans mv.x15
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 511 writeTail v hv (by decide) pc
    (by intro i hi; simp only [writeTail, List.length] at hi; interval_cases i <;> rfl) rfl
  have e23 := wt_x23 v (m-1) h22 h15 (by have := sz.len; omega)
  obtain ⟨h4, w4, p4, m4⟩ := sb_step _ _ wA 512 .x23 .x31 0 (by decide) pA rfl
    (proofBase + (m-1)) (by rw [e23, se12_0, Nat.add_zero]) (by have := sz.len; unfold proofBase; omega)
  have j := jal_step _ 513 2096880 (by decide) p4 rfl 445 rfl
  refine ⟨_, (hA.thenDo h4).thenDo j, ⟨⟨_, view_pc_only _ _ _ w4, ?_, ?_⟩, rfl, ?_⟩⟩
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact h22
  · intro r hr
    rw [foldl_stepV_within writeTail mainWrites (by decide) _ r hr]; exact fr r hr
  · intro q
    have len := sz.len
    rw [setPC_getByte, m4, getByte_of_mem mA, mem]
    have hb' : BitVec.ofNat 8 (writeTail.foldl stepV v .x31) =
        unpackedByte input.proof input.positions.card (countOf input) (m-1) := by
      rw [foldl_stepV_notin _ _ _ (by decide), hb]
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
      split_ifs <;> first | omega | rfl

/-- The byte the copy loop reads from the packed body is still the original one. -/
theorem read_main (input : CheckInput) (m : Nat) (s : MachineState)
    (mem : ∀ a, s.getByte a = mainMem input m a) (p : Nat) (hp : p < m) (hb : p < 2^33) :
    s.getByte (BitVec.ofNat 64 (proofBase + p)) = input.proof.getD p 0 := by
  rw [mem, mainMem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega),
    if_neg (by unfold scratchBase proofBase; omega), if_neg (by omega)]
  exact start_proof_byte input p (by omega)

theorem read_scratch (input : CheckInput) (m : Nat) (s : MachineState)
    (mem : ∀ a, s.getByte a = mainMem input m a) (j : Nat) (hj : j < countOf input + input.positions.card)
    (nb : countOf input ≤ 2^33) (kb : input.positions.card ≤ 2^24) :
    s.getByte (BitVec.ofNat 64 (scratchBase + j)) = scratchByte input j := by
  rw [mem, mainMem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega),
    if_pos (by omega), Nat.add_sub_cancel_left]

/-- Words 507-508 then the write tail: copy packed byte `p`. -/
theorem copy_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*507)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (p : Nat) (h26 : v .x26 = proofBase + p) (hp : p < m)
    (hb : input.proof.getD p 0 = unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 5 5 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step s v hv 507 .x31 .x26 0 (by decide) pc rfl (proofBase + p)
    (by rw [h26, se12_0, Nat.add_zero]) (by unfold proofBase; omega)
  have j := jal_step _ 508 12 (by decide) p1 rfl 511 rfl
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ w1) rfl
    (by rw [setV_ne _ _ _ _ (by decide), h22])
    (fun r hr => by rw [setV_ne _ _ _ _ (fun e => hr (by rw [e]; decide)), fr r hr])
    (fun a => by rw [setPC_getByte, getByte_of_mem m1, mem])
    (by rw [setV_eq _ _ _ (by decide), read_main input m s mem p hp (by omega), byte_ofNat_toNat, hb])
  exact ⟨t, (h1.thenDo j).thenDo ht, at'⟩

def remBlock : List Instr := [.ADD .x31 .x21 .x30]

theorem rb_x31 (v : Reg → Nat) (j : Nat) (h21 : v .x21 = scratchBase) (h30 : v .x30 = j) (jb : j ≤ 2^34) :
    remBlock.foldl stepV v .x31 = scratchBase + j := by
  simp only [remBlock]; vsimp; rw [h21, h30]; unfold scratchBase; omega

/-- Words 509-510 then the write tail: restore byte 29 of digest `j` from scratch. -/
theorem rem_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*509)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (j : Nat) (h30 : v .x30 = j) (hj : j < countOf input)
    (hb : remByte input.proof input.positions.card (countOf input) j =
      unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 5 5 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  have nb := sz.n
  have h21 : v .x21 = scratchBase := (fr .x21 (by decide)).trans mv.x21
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 509 remBlock v hv (by decide) pc
    (by intro i hi; simp only [remBlock, List.length] at hi; interval_cases i <;> rfl) rfl
  have e31 := rb_x31 v j h21 h30 (by omega)
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step _ _ wA 510 .x31 .x31 0 (by decide) pA rfl (scratchBase + j)
    (by rw [e31, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ w1 p1
    (by rw [setV_ne _ _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), h22])
    (fun r hr => by
      rw [setV_ne _ _ _ _ (fun e => hr (by rw [e]; decide)),
        foldl_stepV_within remBlock mainWrites (by decide) _ r hr, fr r hr])
    (fun a => by rw [getByte_of_mem m1, getByte_of_mem mA, mem])
    (by rw [setV_eq _ _ _ (by decide), getByte_of_mem mA, read_scratch input m s mem j (by omega) nb sz.k,
      byte_ofNat_toNat, scratchByte, if_pos hj, hb])
  exact ⟨t, (hA.thenDo h1).thenDo ht, at'⟩

/-! ### The combined head byte -/

def stashRead : List Instr := [.ADD .x31 .x27 .x24]
def saltMask : List Instr := [.ANDI .x31 .x31 7]
def leafShift : List Instr := [.SRLI .x31 .x31 3]
def zeroByte : List Instr := [.ADDI .x31 .x0 0]

theorem sr_x31 (v : Reg → Nat) (n r : Nat) (h27 : v .x27 = scratchBase + n) (h24 : v .x24 = r)
    (nb : n ≤ 2^34) (rb : r ≤ 2^34) : stashRead.foldl stepV v .x31 = scratchBase + n + r := by
  simp only [stashRead]; vsimp; rw [h27, h24]; unfold scratchBase; omega

theorem sm_x31 (v : Reg → Nat) (x : Nat) (h : v .x31 = x) : saltMask.foldl stepV v .x31 = x % 8 := by
  simp only [saltMask]; vsimp; rw [h, show (7:Nat) = 2^3 - 1 from rfl, and_low]; rfl

theorem lsh_x31 (v : Reg → Nat) (x : Nat) (h : v .x31 = x) : leafShift.foldl stepV v .x31 = x / 8 := by
  simp only [leafShift]; vsimp; rw [h]

theorem zb_x31 (v : Reg → Nat) (h0 : v .x0 = 0) : zeroByte.foldl stepV v .x31 = 0 := by
  simp only [zeroByte]; vsimp; rw [h0]

theorem read_stash (input : CheckInput) (m : Nat) (s : MachineState) (sz : Sizes input)
    (mem : ∀ a, s.getByte a = mainMem input m a) (r : Nat) (hr : r < input.positions.card) :
    s.getByte (BitVec.ofNat 64 (scratchBase + countOf input + r)) = input.proof.getD (481*r + 45) 0 := by
  rw [Nat.add_assoc, read_scratch input m s mem _ (by omega) sz.n sz.k, scratchByte, if_neg (by omega),
    Nat.add_sub_cancel_left]

/-- Words 469-472 then the write tail: salt byte 15, the low three bits of the stashed byte. -/
theorem salt_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*469)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (r : Nat) (h24 : v .x24 = r) (hr : r < input.positions.card)
    (hb : BitVec.ofNat 8 ((input.proof.getD (481*r + 45) 0).toNat % 8) =
      unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 7 7 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  have nb := sz.n
  have kb := sz.k
  have h27 : v .x27 = scratchBase + countOf input := (fr .x27 (by decide)).trans mv.x27
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 469 stashRead v hv (by decide) pc
    (by intro i hi; simp only [stashRead, List.length] at hi; interval_cases i <;> rfl) rfl
  have e31 := sr_x31 v (countOf input) r h27 h24 (by omega) (by omega)
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step _ _ wA 470 .x31 .x31 0 (by decide) pA rfl
    (scratchBase + countOf input + r) (by rw [e31, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  rw [getByte_of_mem mA, read_stash input m s sz mem r hr] at w1
  obtain ⟨hM, wM, pM, mM⟩ := block_run _ 471 saltMask _ w1 (by decide) p1
    (by intro i hi; simp only [saltMask, List.length] at hi; interval_cases i <;> rfl) rfl
  have j := jal_step _ 472 156 (by decide) pM rfl 511 rfl
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ wM) rfl
    (by rw [foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
      foldl_stepV_notin _ _ _ (by decide), h22])
    (fun reg hreg => by
      rw [foldl_stepV_within saltMask mainWrites (by decide) _ reg hreg,
        setV_ne _ _ _ _ (fun e => hreg (by rw [e]; decide)),
        foldl_stepV_within stashRead mainWrites (by decide) _ reg hreg]; exact fr reg hreg)
    (fun a => by rw [setPC_getByte, getByte_of_mem mM, getByte_of_mem m1, getByte_of_mem mA, mem])
    (by rw [sm_x31 _ _ (setV_eq _ _ _ (by decide)), hb])
  exact ⟨t, (((hA.thenDo h1).thenDo hM).thenDo j).thenDo ht, at'⟩

/-- Words 473-476 then the write tail: leaf byte 30, the high five bits of the stashed byte. -/
theorem leaf_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*473)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (r : Nat) (h24 : v .x24 = r) (hr : r < input.positions.card)
    (hb : BitVec.ofNat 8 ((input.proof.getD (481*r + 45) 0).toNat / 8) =
      unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 7 7 ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  have nb := sz.n
  have kb := sz.k
  have h27 : v .x27 = scratchBase + countOf input := (fr .x27 (by decide)).trans mv.x27
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 473 stashRead v hv (by decide) pc
    (by intro i hi; simp only [stashRead, List.length] at hi; interval_cases i <;> rfl) rfl
  have e31 := sr_x31 v (countOf input) r h27 h24 (by omega) (by omega)
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step _ _ wA 474 .x31 .x31 0 (by decide) pA rfl
    (scratchBase + countOf input + r) (by rw [e31, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  rw [getByte_of_mem mA, read_stash input m s sz mem r hr] at w1
  obtain ⟨hM, wM, pM, mM⟩ := block_run _ 475 leafShift _ w1 (by decide) p1
    (by intro i hi; simp only [leafShift, List.length] at hi; interval_cases i <;> rfl) rfl
  have j := jal_step _ 476 140 (by decide) pM rfl 511 rfl
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ wM) rfl
    (by rw [foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
      foldl_stepV_notin _ _ _ (by decide), h22])
    (fun reg hreg => by
      rw [foldl_stepV_within leafShift mainWrites (by decide) _ reg hreg,
        setV_ne _ _ _ _ (fun e => hreg (by rw [e]; decide)),
        foldl_stepV_within stashRead mainWrites (by decide) _ reg hreg]; exact fr reg hreg)
    (fun a => by rw [setPC_getByte, getByte_of_mem mM, getByte_of_mem m1, getByte_of_mem mA, mem])
    (by rw [lsh_x31 _ _ (setV_eq _ _ _ (by decide)), hb])
  exact ⟨t, (((hA.thenDo h1).thenDo hM).thenDo j).thenDo ht, at'⟩

/-- Words 462-463 then the write tail: leaf byte 31 is zero. -/
theorem zero_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*462)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (hb : 0 = unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t 5 5 ∧ MainAt input vM (m-1) t := by
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 462 zeroByte v hv (by decide) pc
    (by intro i hi; simp only [zeroByte, List.length] at hi; interval_cases i <;> rfl) rfl
  have j := jal_step _ 463 192 (by decide) pA rfl 511 rfl
  obtain ⟨t, ht, at'⟩ := write_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ wA) rfl
    (by rw [foldl_stepV_notin _ _ _ (by decide), h22])
    (fun reg hreg => by rw [foldl_stepV_within zeroByte mainWrites (by decide) _ reg hreg]; exact fr reg hreg)
    (fun a => by rw [setPC_getByte, getByte_of_mem mA, mem])
    (by rw [zb_x31 _ (view_x0 hv), ← hb]; rfl)
  exact ⟨t, (hA.thenDo j).thenDo ht, at'⟩

end TwoPermutationPrototype.Packed.Checker
