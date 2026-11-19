import CommitGolfCandidate.TwoPermutationPackedUnpackDecode

/-! The head-byte stash (words 426-436) and the copy-loop setup (words 437-444). The combined
head byte of record `r` (packed byte `481r + 45`) is copied to scratch byte
`scratchBase + n + r` before the copy loop can overwrite it. -/
namespace TwoPermutationPrototype.Packed.Checker
variable [UnpackOrigin]
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Scratch byte `j` once the stash is complete: the decoded remainders, then the stashed
combined head bytes. -/
def scratchByte (input : CheckInput) (j : Nat) : Byte :=
  if j < countOf input then remByte input.proof input.positions.card (countOf input) j
  else input.proof.getD (481*(j - countOf input) + 45) 0

theorem byte_ofNat_toNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  apply BitVec.eq_of_toNat_eq; simp

def headMem (input : CheckInput) (r : Nat) (a : Word) : Byte :=
  if scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + countOf input + r then
    scratchByte input (a.toNat - scratchBase)
  else (unpackStart input).getByte a

theorem decode_head_mem (input : CheckInput) (a : Word) :
    decodeMem input (countOf input) a = headMem input 0 a := by
  unfold decodeMem headMem scratchByte
  split_ifs <;> first | rfl | omega

/-- Registers fixed during the stash loop. -/
structure HeadView (input : CheckInput) (v : Reg → Nat) : Prop where
  x0 : v .x0 = 0
  x8 : v .x8 = countOf input
  x15 : v .x15 = proofBase
  x16 : v .x16 = input.positions.card
  x21 : v .x21 = scratchBase
  x27 : v .x27 = scratchBase + countOf input
  other : ∀ r, r ∉ unpackTemps → v r = startView input r

def headWrites : List Reg := [.x22,.x23,.x24,.x25,.x26]

structure HeadAt (input : CheckInput) (vH : Reg → Nat) (r : Nat) (s : MachineState) : Prop where
  view : ∃ v, View s v ∧ v .x22 = r ∧ ∀ reg, reg ∉ headWrites → v reg = vH reg
  pc : s.pc = BitVec.ofNat 64 (4096+4*428)
  mem : ∀ a, s.getByte a = headMem input r a

def headEntry : List Instr := [.ADDI .x22 .x0 0, .ADD .x27 .x21 .x8]

theorem hen_x22 (v : Reg → Nat) (h0 : v .x0 = 0) : headEntry.foldl stepV v .x22 = 0 := by
  simp only [headEntry]; vsimp; rw [h0]

theorem hen_x27 (v : Reg → Nat) (n : Nat) (h21 : v .x21 = scratchBase) (h8 : v .x8 = n)
    (nb : n ≤ 2^34) : headEntry.foldl stepV v .x27 = scratchBase + n := by
  simp only [headEntry]; vsimp; rw [h21, h8]; unfold scratchBase; omega

/-- Words 426-427: enter the stash loop. -/
theorem head_entry (input : CheckInput) (vD : Reg → Nat) (pv : PrefixView input vD)
    (wf : WellFormed input.positions.card input.proof.length) (t : MachineState) (v : Reg → Nat)
    (hv : View t v) (fr : ∀ r, r ∉ decodeWrites → v r = vD r) (pc : t.pc = BitVec.ofNat 64 (4096+4*426))
    (mem : ∀ a, t.getByte a = decodeMem input (countOf input) a) :
    ∃ u vH, Hop t u 2 2 ∧ HeadView input vH ∧ HeadAt input vH 0 u := by
  obtain ⟨cb, _⟩ := count_bound input wf
  obtain ⟨hE, wE, pE, mE⟩ := block_run _ 426 headEntry v hv (by decide) pc
    (by intro i hi; simp only [headEntry, List.length] at hi; interval_cases i <;> rfl) rfl
  have x0 : v .x0 = 0 := view_x0 hv
  have x8 : v .x8 = countOf input := (fr .x8 (by decide)).trans pv.x8
  have x21 : v .x21 = scratchBase := (fr .x21 (by decide)).trans pv.x21
  refine ⟨_, _, hE, ⟨view_x0 wE, ?_, ?_, ?_, ?_, hen_x27 v _ x21 x8 (by omega), ?_⟩,
    ⟨⟨_, wE, hen_x22 v x0, fun _ _ => rfl⟩, pE, fun a => by rw [getByte_of_mem mE, mem, decode_head_mem]⟩⟩
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact x8
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact (fr .x15 (by decide)).trans pv.x15
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact (fr .x16 (by decide)).trans pv.x16
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact x21
  · intro r hr
    rw [foldl_stepV_within headEntry unpackTemps (by decide) _ r hr,
      fr r (notin_sub _ _ (by decide) hr), pv.other r (notin_sub _ _ (by decide) hr)]

def stashAddr : List Instr := [.ADDI .x23 .x0 481, .MUL .x24 .x22 .x23, .ADD .x24 .x24 .x15]
def stashDest : List Instr := [.ADD .x26 .x27 .x22]
def stashNext : List Instr := [.ADDI .x22 .x22 1]

theorem sa_x24 (v : Reg → Nat) (r : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = r) (h15 : v .x15 = proofBase)
    (rb : r ≤ 2^34) : stashAddr.foldl stepV v .x24 = proofBase + 481*r := by
  simp only [stashAddr]; vsimp; rw [h0, h22, h15]; vnorm; unfold proofBase; omega

theorem sd_x26 (v : Reg → Nat) (n r : Nat) (h27 : v .x27 = scratchBase + n) (h22 : v .x22 = r)
    (nb : n ≤ 2^34) (rb : r ≤ 2^34) : stashDest.foldl stepV v .x26 = scratchBase + n + r := by
  simp only [stashDest]; vsimp; rw [h27, h22]; unfold scratchBase; omega

theorem sn_x22 (v : Reg → Nat) (r : Nat) (h22 : v .x22 = r) (rb : r ≤ 2^34) :
    stashNext.foldl stepV v .x22 = r+1 := by
  simp only [stashNext]; vsimp; rw [h22]; omega

/-- Records fit in the packed body: `481k ≤ L ≤ 2^33`. -/
theorem records_fit (input : CheckInput) (wf : WellFormed input.positions.card input.proof.length) :
    481*input.positions.card ≤ input.proof.length ∧ input.proof.length ≤ 2^33 := by
  obtain ⟨l, _, r, e⟩ := wf
  simp only [packedLength, bodyLength] at e
  constructor <;> omega

theorem head_step (input : CheckInput) (vH : Reg → Nat) (hw : HeadView input vH)
    (wf : WellFormed input.positions.card input.proof.length) (r : Nat) (hr : r < input.positions.card)
    (s : MachineState) (h : HeadAt input vH r s) :
    ∃ t, Hop s t 9 12 ∧ HeadAt input vH (r+1) t := by
  obtain ⟨⟨v, hv, h22, fr⟩, pc, mem⟩ := h
  obtain ⟨cb, _⟩ := count_bound input wf
  obtain ⟨fit, lb⟩ := records_fit input wf
  have x16 : v .x16 = input.positions.card := (fr .x16 (by decide)).trans hw.x16
  have x15 : v .x15 = proofBase := (fr .x15 (by decide)).trans hw.x15
  have x27 : v .x27 = scratchBase + countOf input := (fr .x27 (by decide)).trans hw.x27
  have x0 : v .x0 = 0 := view_x0 hv
  have g := beq_step s v hv 428 .x22 .x16 36 (by decide) pc rfl 437 rfl
  rw [if_neg (by rw [h22, x16]; omega)] at g
  have w0 := view_pc_only s v (BitVec.ofNat 64 (4096+4*(428+1))) hv
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 429 stashAddr v w0 (by decide) rfl
    (by intro i hi; simp only [stashAddr, List.length] at hi; interval_cases i <;> rfl) rfl
  have eA := sa_x24 v r x0 h22 x15 (by omega)
  have rd : (stashAddr.foldl execInstrBr (s.setPC (BitVec.ofNat 64 (4096+4*(428+1))))).getByte
      (BitVec.ofNat 64 (proofBase + 481*r + 45)) = input.proof.getD (481*r + 45) 0 := by
    rw [getByte_of_mem mA, setPC_getByte, mem, headMem, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold proofBase; omega), if_neg (by unfold scratchBase proofBase; omega),
      Nat.add_assoc, start_proof_byte input _ (by omega)]
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step _ _ wA 432 .x25 .x24 45 (by decide) pA rfl
    (proofBase + 481*r + 45) (by rw [eA, se12_45]) (by unfold proofBase; omega)
  rw [rd] at w1
  obtain ⟨hD, wD, pD, mD⟩ := block_run _ 433 stashDest _ w1 (by decide) p1
    (by intro i hi; simp only [stashDest, List.length] at hi; interval_cases i <;> rfl) rfl
  have eD := sd_x26 (setV (stashAddr.foldl stepV v) .x25 (input.proof.getD (481*r + 45) 0).toNat)
    (countOf input) r
    (by rw [setV_ne _ _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), x27])
    (by rw [setV_ne _ _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), h22]) (by omega) (by omega)
  obtain ⟨h2, w2, p2, m2⟩ := sb_step _ _ wD 434 .x26 .x25 0 (by decide) pD rfl
    (scratchBase + countOf input + r) (by rw [eD, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  obtain ⟨hN, wN, pN, mN⟩ := block_run _ 435 stashNext _ w2 (by decide) p2
    (by intro i hi; simp only [stashNext, List.length] at hi; interval_cases i <;> rfl) rfl
  have jm := jal_step _ 436 2097120 (by decide) pN rfl 428 rfl
  refine ⟨_, ((((((g.thenDo hA).thenDo h1).thenDo hD).thenDo h2).thenDo hN).thenDo jm).cast rfl rfl,
    ⟨⟨_, view_pc_only _ _ _ wN, ?_, ?_⟩, rfl, ?_⟩⟩
  · rw [sn_x22 _ r (by
      rw [foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
        foldl_stepV_notin _ _ _ (by decide), h22]) (by omega)]
  · intro reg hreg
    rw [foldl_stepV_within stashNext headWrites (by decide) _ reg hreg,
      foldl_stepV_within stashDest headWrites (by decide) _ reg hreg,
      setV_within _ _ _ headWrites (by decide) reg hreg,
      foldl_stepV_within stashAddr headWrites (by decide) _ reg hreg]
    exact fr reg hreg
  · intro q
    rw [setPC_getByte, getByte_of_mem mN, m2, getByte_of_mem mD, getByte_of_mem m1, getByte_of_mem mA,
      setPC_getByte, mem]
    have hb : BitVec.ofNat 8 (stashDest.foldl stepV
        (setV (stashAddr.foldl stepV v) .x25 (input.proof.getD (481*r + 45) 0).toNat) .x25) =
        input.proof.getD (481*r + 45) 0 := by
      rw [foldl_stepV_notin _ _ _ (by decide), setV_eq _ _ _ (by decide), byte_ofNat_toNat]
    rw [hb]
    unfold headMem
    by_cases hq : q = BitVec.ofNat 64 (scratchBase + countOf input + r)
    · subst hq
      have e : (BitVec.ofNat 64 (scratchBase + countOf input + r)).toNat = scratchBase + countOf input + r := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      rw [if_pos rfl, e, if_pos (by omega), scratchByte, if_neg (by omega),
        show scratchBase + countOf input + r - scratchBase - countOf input = r by omega]
    · rw [if_neg hq]
      have hq' : q.toNat ≠ scratchBase + countOf input + r := by
        intro e; apply hq; apply BitVec.eq_of_toNat_eq
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      by_cases inr : scratchBase ≤ q.toNat ∧ q.toNat < scratchBase + countOf input + r
      · rw [if_pos inr, if_pos (by omega)]
      · rw [if_neg inr, if_neg (by omega)]

theorem head_loop (input : CheckInput) (vH : Reg → Nat) (hw : HeadView input vH)
    (wf : WellFormed input.positions.card input.proof.length) :
    ∀ d r s, r + d = input.positions.card → HeadAt input vH r s →
      ∃ t, Hop s t (9*d) (12*d) ∧ HeadAt input vH input.positions.card t := by
  intro d
  induction d with
  | zero => intro r s e h; exact ⟨s, Hop.refl s, by simpa using e ▸ h⟩
  | succ d ih =>
    intro r s e h
    obtain ⟨t, ht, ha⟩ := head_step input vH hw wf r (by omega) s h
    obtain ⟨u, hu, au⟩ := ih (r+1) t (by omega) ha
    exact ⟨u, (ht.thenDo hu).cast (by ring) (by ring), au⟩

def loopSetup : List Instr :=
  [.ADDI .x28 .x0 30, .MUL .x28 .x8 .x28, .ADDI .x29 .x0 48, .MUL .x29 .x16 .x29, .ADD .x28 .x28 .x29,
   .ADDI .x29 .x0 498, .MUL .x29 .x16 .x29, .ADDI .x22 .x28 0]

theorem ls_x28 (v : Reg → Nat) (k n : Nat) (h0 : v .x0 = 0) (h8 : v .x8 = n) (h16 : v .x16 = k)
    (kb : k ≤ 2^24) (nb : n ≤ 2^33) : loopSetup.foldl stepV v .x28 = 48*k + 30*n := by
  simp only [loopSetup]; vsimp; rw [h0, h8, h16]; vnorm
  have e1 : n * 30 % 18446744073709551616 = n * 30 := Nat.mod_eq_of_lt (by omega)
  have e2 : k * 48 % 18446744073709551616 = k * 48 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2]; omega

theorem ls_x22 (v : Reg → Nat) (k n : Nat) (h0 : v .x0 = 0) (h8 : v .x8 = n) (h16 : v .x16 = k)
    (kb : k ≤ 2^24) (nb : n ≤ 2^33) : loopSetup.foldl stepV v .x22 = 48*k + 30*n := by
  simp only [loopSetup]; vsimp; rw [h0, h8, h16]; vnorm
  have e1 : n * 30 % 18446744073709551616 = n * 30 := Nat.mod_eq_of_lt (by omega)
  have e2 : k * 48 % 18446744073709551616 = k * 48 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2]; omega

theorem ls_x29 (v : Reg → Nat) (k : Nat) (h0 : v .x0 = 0) (h16 : v .x16 = k) (kb : k ≤ 2^24) :
    loopSetup.foldl stepV v .x29 = 498*k := by
  simp only [loopSetup]; vsimp; rw [h0, h16]; vnorm; omega

/-- Register view at the main copy loop. -/
structure MainView (input : CheckInput) (v : Reg → Nat) : Prop where
  x0 : v .x0 = 0
  x8 : v .x8 = countOf input
  x15 : v .x15 = proofBase
  x16 : v .x16 = input.positions.card
  x21 : v .x21 = scratchBase
  x27 : v .x27 = scratchBase + countOf input
  x28 : v .x28 = 48*input.positions.card + 30*countOf input
  x29 : v .x29 = 498*input.positions.card
  other : ∀ r, r ∉ unpackTemps → v r = startView input r

/-- Words 428 (exit) and 437-444: leave the stash loop and set up the copy loop. -/
theorem head_exit (input : CheckInput) (vH : Reg → Nat) (hw : HeadView input vH)
    (wf : WellFormed input.positions.card input.proof.length) (s : MachineState)
    (h : HeadAt input vH input.positions.card s) :
    ∃ t v, Hop s t 9 18 ∧ View t v ∧ MainView input v ∧
      v .x22 = 48*input.positions.card + 30*countOf input ∧
      t.pc = BitVec.ofNat 64 (4096+4*445) ∧ ∀ a, t.getByte a = headMem input input.positions.card a := by
  obtain ⟨⟨v, hv, h22, fr⟩, pc, mem⟩ := h
  obtain ⟨cb, _⟩ := count_bound input wf
  have kb := checker_positions_bound input
  have x16 : v .x16 = input.positions.card := (fr .x16 (by decide)).trans hw.x16
  have x8 : v .x8 = countOf input := (fr .x8 (by decide)).trans hw.x8
  have x0 : v .x0 = 0 := view_x0 hv
  have g := beq_step s v hv 428 .x22 .x16 36 (by decide) pc rfl 437 rfl
  rw [if_pos (by rw [h22, x16])] at g
  obtain ⟨hE, wE, pE, mE⟩ := block_run _ 437 loopSetup v (view_pc_only s v _ hv) (by decide) rfl
    (by intro i hi; simp only [loopSetup, List.length] at hi; interval_cases i <;> rfl) rfl
  refine ⟨_, _, g.thenDo hE, wE, ⟨view_x0 wE, ?_, ?_, ?_, ?_, ?_, ls_x28 v _ _ x0 x8 x16 kb cb,
    ls_x29 v _ x0 x16 kb, ?_⟩, ls_x22 v _ _ x0 x8 x16 kb cb, pE, fun a => by
      rw [getByte_of_mem mE, setPC_getByte]; exact mem a⟩
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact x8
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact (fr .x15 (by decide)).trans hw.x15
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact x16
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact (fr .x21 (by decide)).trans hw.x21
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact (fr .x27 (by decide)).trans hw.x27
  · intro r hr
    rw [foldl_stepV_within loopSetup unpackTemps (by decide) _ r hr,
      fr r (notin_sub _ _ (by decide) hr), hw.other r hr]

/-- The stash phase, from the decode loop's exit to the copy loop. -/
theorem head_phase (input : CheckInput) (vD : Reg → Nat) (pv : PrefixView input vD)
    (wf : WellFormed input.positions.card input.proof.length) (t : MachineState) (v : Reg → Nat)
    (hv : View t v) (fr : ∀ r, r ∉ decodeWrites → v r = vD r) (pc : t.pc = BitVec.ofNat 64 (4096+4*426))
    (mem : ∀ a, t.getByte a = decodeMem input (countOf input) a) :
    ∃ u vM, Hop t u (9*input.positions.card + 11) (12*input.positions.card + 20) ∧ View u vM ∧
      MainView input vM ∧ vM .x22 = 48*input.positions.card + 30*countOf input ∧
      u.pc = BitVec.ofNat 64 (4096+4*445) ∧ ∀ a, u.getByte a = headMem input input.positions.card a := by
  obtain ⟨u0, vH, h0, hw, a0⟩ := head_entry input vD pv wf t v hv fr pc mem
  obtain ⟨u1, h1, a1⟩ := head_loop input vH hw wf input.positions.card 0 u0 (by omega) a0
  obtain ⟨u2, vM, h2, w2, mv, e22, p2, m2⟩ := head_exit input vH hw wf u1 a1
  exact ⟨u2, vM, ((h0.thenDo h1).thenDo h2).cast (by ring) (by ring), w2, mv, e22, p2, m2⟩

end TwoPermutationPrototype.Packed.Checker
