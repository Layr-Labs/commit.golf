import CommitGolfCandidate.TwoPermutationPackedUnpackMemory

/-! The remainder decode loop (words 403-425): the six stored bits of every digest
are written to scratch byte `scratchBase + j`. -/
namespace TwoPermutationPrototype.Packed.Checker
variable [UnpackOrigin]
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

@[simp] theorem se12_2 : (signExtend12 2).toNat = 2 := rfl

def countOf (input : CheckInput) : Nat := packedCount input.positions.card input.proof.length

def decodeMem (input : CheckInput) (j : Nat) (a : Word) : Byte :=
  if scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + j then
    remByte input.proof input.positions.card (countOf input) (a.toNat - scratchBase)
  else (unpackStart input).getByte a

def decodeWrites : List Reg := [.x22,.x23,.x24,.x25,.x26,.x27]

structure DecodeAt (input : CheckInput) (vD : Reg → Nat) (j : Nat) (s : MachineState) : Prop where
  view : ∃ v, View s v ∧ v .x22 = j ∧ ∀ r, r ∉ decodeWrites → v r = vD r
  pc : s.pc = BitVec.ofNat 64 (4096+4*403)
  mem : ∀ a, s.getByte a = decodeMem input j a

def decodeA : List Instr :=
  [.SRLI .x23 .x22 2, .ADD .x24 .x23 .x23, .ADD .x24 .x24 .x23, .ADD .x24 .x24 .x18, .ADD .x24 .x24 .x15]
def decodeB : List Instr := [.SLLI .x26 .x26 8, .OR .x25 .x25 .x26]
def decodeC : List Instr :=
  [.SLLI .x26 .x26 16, .OR .x25 .x25 .x26, .ANDI .x26 .x22 3, .ADD .x27 .x26 .x26, .ADD .x26 .x27 .x26,
   .ADD .x26 .x26 .x26, .SRL .x25 .x25 .x26, .ANDI .x25 .x25 63, .ADD .x27 .x21 .x22]
def decodeD : List Instr := [.ADDI .x22 .x22 1]

theorem setV_ne (v : Reg → Nat) (rd : Reg) (x : Nat) (r : Reg) (h : r ≠ rd) : setV v rd x r = v r := by
  simp only [setV]; rw [if_neg (fun e => h e.1)]

theorem setV_eq (v : Reg → Nat) (rd : Reg) (x : Nat) (h : rd ≠ .x0) : setV v rd x rd = x := by
  unfold setV; exact if_pos ⟨rfl, h⟩

theorem lor_256 (a b : Nat) (h : a < 256) : a ||| b * 256 = a + b * 256 := lor_shift a b 8 h
theorem lor_65536 (a b : Nat) (h : a < 65536) : a ||| b * 65536 = a + b * 65536 := lor_shift a b 16 h

theorem and_63 (x : Nat) : x &&& 63 = x % 64 := and_low x 6
theorem and_3 (x : Nat) : x &&& 3 = x % 4 := and_low x 2

theorem dA_x24 (v : Reg → Nat) (j B : Nat) (h22 : v .x22 = j) (h18 : v .x18 = B) (h15 : v .x15 = proofBase)
    (jb : j ≤ 2^34) (bb : B ≤ 2^34) :
    decodeA.foldl stepV v .x24 = proofBase + (B + 3*(j/4)) := by
  simp only [decodeA]; vsimp; rw [h22, h18, h15]; unfold proofBase; vnorm; omega

theorem dB_x25 (v : Reg → Nat) (b0 b1 : Nat) (h25 : v .x25 = b0) (h26 : v .x26 = b1)
    (l0 : b0 < 256) (l1 : b1 < 256) : decodeB.foldl stepV v .x25 = b0 + 256*b1 := by
  simp only [decodeB]; vsimp; rw [h25, h26, Nat.mod_eq_of_lt (by omega), lor_256 _ _ (by omega)]; omega

theorem dC_x25 (v : Reg → Nat) (w b2 j : Nat) (h25 : v .x25 = w) (h26 : v .x26 = b2) (h22 : v .x22 = j)
    (lw : w < 65536) (l2 : b2 < 256) (jb : j ≤ 2^34) :
    decodeC.foldl stepV v .x25 = (w + 65536*b2) / 64^(j%4) % 64 := by
  simp only [decodeC]; vsimp; rw [h25, h26, h22, Nat.mod_eq_of_lt (by omega), lor_65536 _ _ (by omega),
    and_63, and_3]
  have m4 : j % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize j % 4 = m at m4 ⊢
  interval_cases m <;> vnorm <;> omega

theorem dC_x27 (v : Reg → Nat) (j : Nat) (h21 : v .x21 = scratchBase) (h22 : v .x22 = j) (jb : j ≤ 2^34) :
    decodeC.foldl stepV v .x27 = scratchBase + j := by
  simp only [decodeC]; vsimp; rw [h21, h22]; unfold scratchBase; omega

theorem dD_x22 (v : Reg → Nat) (j : Nat) (h22 : v .x22 = j) (jb : j ≤ 2^34) :
    decodeD.foldl stepV v .x22 = j+1 := by
  simp only [decodeD]; vsimp; rw [h22]; omega

theorem foldl_stepV_within (is : List Instr) (ws : List Reg) (h : (is.map aluDest).all (ws.contains ·) = true)
    (v : Reg → Nat) (r : Reg) (hr : r ∉ ws) : is.foldl stepV v r = v r := by
  apply foldl_stepV_notin
  intro hm
  simp only [List.all_eq_true] at h
  exact hr (by simpa using h r hm)

theorem setV_within (v : Reg → Nat) (rd : Reg) (x : Nat) (ws : List Reg) (hd : rd ∈ ws) (r : Reg)
    (hr : r ∉ ws) : setV v rd x r = v r := by
  simp only [setV]
  rw [if_neg (fun (h : r = rd ∧ rd ≠ .x0) => hr (h.1 ▸ hd))]

theorem read_packed (input : CheckInput) (s : MachineState) (j : Nat)
    (mem : ∀ a, s.getByte a = decodeMem input j a) (p : Nat) (hp : p < 2^33) :
    s.getByte (BitVec.ofNat 64 (proofBase + p)) = input.proof.getD p 0 := by
  rw [mem, decodeMem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega),
    if_neg (by unfold scratchBase proofBase; omega)]
  exact start_proof_byte input p (by omega)

theorem count_bound (input : CheckInput) (wf : WellFormed input.positions.card input.proof.length) :
    countOf input ≤ 2^33 ∧ bodyLength input.positions.card (countOf input) + 3*((countOf input + 3)/4) ≤ 2^33 := by
  obtain ⟨l, _, _, e⟩ := wf
  unfold countOf
  simp only [packedLength, bodyLength] at e ⊢
  constructor <;> omega

set_option maxHeartbeats 4000000 in
theorem decode_step (input : CheckInput) (vD : Reg → Nat) (pv : PrefixView input vD)
    (wf : WellFormed input.positions.card input.proof.length) (j : Nat) (hj : j < countOf input)
    (s : MachineState) (h : DecodeAt input vD j s) :
    ∃ t, Hop s t 23 23 ∧ DecodeAt input vD (j+1) t := by
  obtain ⟨⟨v, hv, h22, fr⟩, pc, mem⟩ := h
  obtain ⟨cb, lb⟩ := count_bound input wf
  have x8 : v .x8 = countOf input := (fr .x8 (by decide)).trans pv.x8
  have x18 : v .x18 = bodyLength input.positions.card (countOf input) := (fr .x18 (by decide)).trans pv.x18
  have x15 : v .x15 = proofBase := (fr .x15 (by decide)).trans pv.x15
  have x21 : v .x21 = scratchBase := (fr .x21 (by decide)).trans pv.x21
  generalize hB : bodyLength input.positions.card (countOf input) = B at x18 lb
  -- the loop test
  have g := beq_step s v hv 403 .x22 .x8 92 (by decide) pc rfl 426 rfl
  rw [if_neg (by rw [h22, x8]; omega)] at g
  have w0 := view_pc_only s v (BitVec.ofNat 64 (4096+4*(403+1))) hv
  -- address of the remainder word
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 404 decodeA v w0 (by decide) rfl
    (by intro i hi; simp only [decodeA, List.length] at hi; interval_cases i <;> rfl) rfl
  generalize hsA : decodeA.foldl execInstrBr (s.setPC (BitVec.ofNat 64 (4096+4*(403+1)))) = sA at hA wA pA mA
  have eA := dA_x24 v j B h22 x18 x15 (by omega) (by omega)
  have mA' : ∀ a, sA.getByte a = decodeMem input j a := fun a => (getByte_of_mem mA a).trans (mem a)
  generalize hvA : decodeA.foldl stepV v = vA at wA eA
  -- three byte loads
  have r0 := read_packed input sA j mA' (B + 3*(j/4)) (by omega)
  have r1 := read_packed input sA j mA' (B + 3*(j/4) + 1) (by omega)
  have r2 := read_packed input sA j mA' (B + 3*(j/4) + 2) (by omega)
  obtain ⟨h1, w1, p1, m1⟩ := lbu_step sA vA wA 409 .x25 .x24 0 (by decide) pA rfl
    (proofBase + (B + 3*(j/4))) (by rw [eA, se12_0, Nat.add_zero]) (by unfold proofBase; omega)
  generalize hs1 : execInstrBr sA (.LBU .x25 .x24 0) = s1 at h1 w1 p1 m1
  rw [r0] at w1
  obtain ⟨h2, w2, p2, m2⟩ := lbu_step s1 _ w1 410 .x26 .x24 1 (by decide) p1 rfl
    (proofBase + (B + 3*(j/4) + 1)) (by rw [setV_ne _ _ _ _ (by decide), eA, se12_1]; omega) (by unfold proofBase; omega)
  generalize hs2 : execInstrBr s1 (.LBU .x26 .x24 1) = s2 at h2 w2 p2 m2
  rw [getByte_of_mem m1, r1] at w2
  obtain ⟨hB', wB, pB, mB⟩ := block_run _ 411 decodeB _ w2 (by decide) p2
    (by intro i hi; simp only [decodeB, List.length] at hi; interval_cases i <;> rfl) rfl
  generalize hsB : decodeB.foldl execInstrBr s2 = sB at hB' wB pB mB
  have eB := dB_x25 (setV (setV vA .x25 (input.proof.getD (B + 3*(j/4)) 0).toNat) .x26
      (input.proof.getD (B + 3*(j/4) + 1) 0).toNat) (input.proof.getD (B + 3*(j/4)) 0).toNat
    (input.proof.getD (B + 3*(j/4) + 1) 0).toNat
    (by rw [setV_ne _ _ _ _ (by decide), setV_eq _ _ _ (by decide)]) (setV_eq _ _ _ (by decide))
    (BitVec.isLt _) (BitVec.isLt _)
  generalize hvB : decodeB.foldl stepV (setV (setV vA .x25 (input.proof.getD (B + 3*(j/4)) 0).toNat) .x26
      (input.proof.getD (B + 3*(j/4) + 1) 0).toNat) = vB at wB eB
  have eB24 : vB .x24 = proofBase + (B + 3*(j/4)) := by
    rw [← hvB, foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
      setV_ne _ _ _ _ (by decide), eA]
  obtain ⟨h3, w3, p3, m3⟩ := lbu_step sB vB wB 413 .x26 .x24 2 (by decide) pB rfl
    (proofBase + (B + 3*(j/4) + 2)) (by rw [eB24, se12_2]; omega) (by unfold proofBase; omega)
  generalize hs3 : execInstrBr sB (.LBU .x26 .x24 2) = s3 at h3 w3 p3 m3
  rw [getByte_of_mem mB, getByte_of_mem m2, getByte_of_mem m1, r2] at w3
  have vB22 : vB .x22 = j := by
    rw [← hvB, foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
      setV_ne _ _ _ _ (by decide), ← hvA, foldl_stepV_notin _ _ _ (by decide), h22]
  have vB21 : vB .x21 = scratchBase := by
    rw [← hvB, foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide),
      setV_ne _ _ _ _ (by decide), ← hvA, foldl_stepV_notin _ _ _ (by decide), x21]
  obtain ⟨hC, wC, pC, mC⟩ := block_run _ 414 decodeC _ w3 (by decide) p3
    (by intro i hi; simp only [decodeC, List.length] at hi; interval_cases i <;> rfl) rfl
  generalize hsC : decodeC.foldl execInstrBr s3 = sC at hC wC pC mC
  have w25 : (input.proof.getD (B + 3*(j/4)) 0).toNat + 256*(input.proof.getD (B + 3*(j/4) + 1) 0).toNat < 65536 := by
    have a := (input.proof.getD (B + 3*(j/4)) 0).isLt
    have b := (input.proof.getD (B + 3*(j/4) + 1) 0).isLt
    simp only [Nat.reducePow] at a b; omega
  have eC := dC_x25 (setV vB .x26 (input.proof.getD (B + 3*(j/4) + 2) 0).toNat)
    ((input.proof.getD (B + 3*(j/4)) 0).toNat + 256*(input.proof.getD (B + 3*(j/4) + 1) 0).toNat)
    (input.proof.getD (B + 3*(j/4) + 2) 0).toNat j
    (by rw [setV_ne _ _ _ _ (by decide), eB]) (setV_eq _ _ _ (by decide))
    (by rw [setV_ne _ _ _ _ (by decide), vB22]) w25 (BitVec.isLt _) (by omega)
  have eC27 := dC_x27 (setV vB .x26 (input.proof.getD (B + 3*(j/4) + 2) 0).toNat) j
    (by rw [setV_ne _ _ _ _ (by decide), vB21]) (by rw [setV_ne _ _ _ _ (by decide), vB22]) (by omega)
  generalize hvC : decodeC.foldl stepV (setV vB .x26 (input.proof.getD (B + 3*(j/4) + 2) 0).toNat) = vC
    at wC eC eC27
  obtain ⟨h4, w4, p4, m4⟩ := sb_step sC vC wC 423 .x27 .x25 0 (by decide) pC rfl
    (scratchBase + j) (by rw [eC27, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  generalize hs4 : execInstrBr sC (.SB .x27 .x25 0) = s4 at h4 w4 p4 m4
  have vC22 : vC .x22 = j := by
    rw [← hvC, foldl_stepV_notin _ _ _ (by decide), setV_ne _ _ _ _ (by decide), vB22]
  obtain ⟨h5, w5, p5, m5⟩ := block_run _ 424 decodeD _ w4 (by decide) p4
    (by intro i hi; simp only [decodeD, List.length] at hi; interval_cases i <;> rfl) rfl
  have j6 := jal_step _ 425 2097064 (by decide) p5 rfl 403 rfl
  refine ⟨_, ((((((((g.thenDo hA).thenDo h1).thenDo h2).thenDo hB').thenDo h3).thenDo hC).thenDo h4).thenDo h5).thenDo j6,
    ⟨⟨decodeD.foldl stepV vC, view_pc_only _ _ _ w5, dD_x22 vC j vC22 (by omega), ?_⟩, rfl, ?_⟩⟩
  · intro r hr
    have hr' : r ∉ decodeWrites := hr
    rw [foldl_stepV_within decodeD decodeWrites (by decide) _ r hr', ← hvC,
      foldl_stepV_within decodeC decodeWrites (by decide) _ r hr',
      setV_within _ _ _ decodeWrites (by decide) r hr', ← hvB,
      foldl_stepV_within decodeB decodeWrites (by decide) _ r hr',
      setV_within _ _ _ decodeWrites (by decide) r hr', setV_within _ _ _ decodeWrites (by decide) r hr',
      ← hvA, foldl_stepV_within decodeA decodeWrites (by decide) _ r hr']
    exact fr r hr
  · intro q
    rw [setPC_getByte, getByte_of_mem m5, m4, getByte_of_mem mC, getByte_of_mem m3, getByte_of_mem mB,
      getByte_of_mem m2, getByte_of_mem m1, mA', eC]
    unfold decodeMem
    by_cases hq : q = BitVec.ofNat 64 (scratchBase + j)
    · subst hq
      have e : (BitVec.ofNat 64 (scratchBase + j)).toNat = scratchBase + j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      rw [if_pos rfl, e, if_pos (by omega), Nat.add_sub_cancel_left]
      simp only [remByte, packedWord, hB]
    · rw [if_neg hq]
      have hq' : q.toNat ≠ scratchBase + j := by
        intro e; apply hq; apply BitVec.eq_of_toNat_eq
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      by_cases inr : scratchBase ≤ q.toNat ∧ q.toNat < scratchBase + j
      · rw [if_pos inr, if_pos (by omega)]
      · rw [if_neg inr, if_neg (by omega)]

theorem notin_sub (ws ws' : List Reg) {r : Reg} (sub : ws.all (ws'.contains ·) = true) (h : r ∉ ws') :
    r ∉ ws := by
  intro m
  simp only [List.all_eq_true] at sub
  exact h (by simpa using sub r m)

theorem decode_loop (input : CheckInput) (vD : Reg → Nat) (pv : PrefixView input vD)
    (wf : WellFormed input.positions.card input.proof.length) :
    ∀ d j s, j + d = countOf input → DecodeAt input vD j s →
      ∃ t, Hop s t (23*d) (23*d) ∧ DecodeAt input vD (countOf input) t := by
  intro d
  induction d with
  | zero => intro j s e h; exact ⟨s, Hop.refl s, by simpa using e ▸ h⟩
  | succ d ih =>
    intro j s e h
    obtain ⟨t, ht, ha⟩ := decode_step input vD pv wf j (by omega) s h
    obtain ⟨u, hu, au⟩ := ih (j+1) t (by omega) ha
    exact ⟨u, (ht.thenDo hu).cast (by ring) (by ring), au⟩

/-- The decode loop's exit at word 426, with every remainder decoded. -/
theorem decode_phase (input : CheckInput) (vD : Reg → Nat) (pv : PrefixView input vD)
    (wf : WellFormed input.positions.card input.proof.length) (s : MachineState)
    (h : DecodeAt input vD 0 s) :
    ∃ t v, Hop s t (23*countOf input + 1) (23*countOf input + 1) ∧ View t v ∧
      (∀ r, r ∉ decodeWrites → v r = vD r) ∧
      t.pc = BitVec.ofNat 64 (4096+4*426) ∧ ∀ a, t.getByte a = decodeMem input (countOf input) a := by
  obtain ⟨t, ht, ⟨⟨v, hv, h22, fr⟩, pc, mem⟩⟩ := decode_loop input vD pv wf (countOf input) 0 s (by omega) h
  have x8 : v .x8 = countOf input := (fr .x8 (by decide)).trans pv.x8
  have g := beq_step t v hv 403 .x22 .x8 92 (by decide) pc rfl 426 rfl
  rw [if_pos (by rw [h22, x8])] at g
  exact ⟨_, v, ht.thenDo g, view_pc_only t v _ hv, fr, rfl, fun a => by rw [setPC_getByte]; exact mem a⟩

end TwoPermutationPrototype.Packed.Checker
