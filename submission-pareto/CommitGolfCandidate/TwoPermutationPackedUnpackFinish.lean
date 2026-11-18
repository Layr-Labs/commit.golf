import CommitGolfCandidate.TwoPermutationPackedUnpackCopyLoop

/-! The end of the unpacking wrapper (words 514-541): clear the scratch bytes, publish the
unpacked length in `a7`, clear the temporaries, set `t1 := 498k` and return to word 2. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

def zeroMem (input : CheckInput) (j : Nat) (a : Word) : Byte :=
  if scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + j then 0 else mainMem input 0 a

structure ZeroAt (input : CheckInput) (vM : Reg → Nat) (j : Nat) (s : MachineState) : Prop where
  view : ∃ v, View s v ∧ v .x22 = j ∧ v .x23 = countOf input + input.positions.card ∧
    ∀ r, r ∉ mainWrites → v r = vM r
  pc : s.pc = BitVec.ofNat 64 (4096+4*516)
  mem : ∀ a, s.getByte a = zeroMem input j a

def clearStart : List Instr := [.ADDI .x22 .x0 0, .ADD .x23 .x8 .x16]
def zeroAddr : List Instr := [.ADD .x24 .x21 .x22]
def zeroNext : List Instr := [.ADDI .x22 .x22 1]

theorem cs_x22 (v : Reg → Nat) (h0 : v .x0 = 0) : clearStart.foldl stepV v .x22 = 0 := by
  simp only [clearStart]; vsimp; rw [h0]

theorem cs_x23 (v : Reg → Nat) (n k : Nat) (h8 : v .x8 = n) (h16 : v .x16 = k) (nb : n ≤ 2^34) (kb : k ≤ 2^34) :
    clearStart.foldl stepV v .x23 = n + k := by
  simp only [clearStart]; vsimp; rw [h8, h16]; omega

theorem za_x24 (v : Reg → Nat) (j : Nat) (h21 : v .x21 = scratchBase) (h22 : v .x22 = j) (jb : j ≤ 2^34) :
    zeroAddr.foldl stepV v .x24 = scratchBase + j := by
  simp only [zeroAddr]; vsimp; rw [h21, h22]; unfold scratchBase; omega

theorem zn_x22 (v : Reg → Nat) (j : Nat) (h22 : v .x22 = j) (jb : j ≤ 2^34) :
    zeroNext.foldl stepV v .x22 = j+1 := by
  simp only [zeroNext]; vsimp; rw [h22]; omega

theorem zero_step (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (j : Nat) (hj : j < countOf input + input.positions.card) (s : MachineState) (h : ZeroAt input vM j s) :
    ∃ t, Hop s t 5 5 ∧ ZeroAt input vM (j+1) t := by
  obtain ⟨⟨v, hv, h22, h23, fr⟩, pc, mem⟩ := h
  have nb := sz.n
  have kb := sz.k
  have x21 : v .x21 = scratchBase := (fr .x21 (by decide)).trans mv.x21
  have g := beq_step s v hv 516 .x22 .x23 20 (by decide) pc rfl 521 rfl
  rw [if_neg (by rw [h22, h23]; omega)] at g
  have w0 := view_pc_only s v (BitVec.ofNat 64 (4096+4*(516+1))) hv
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 517 zeroAddr v w0 (by decide) rfl
    (by intro i hi; simp only [zeroAddr, List.length] at hi; interval_cases i <;> rfl) rfl
  have eA := za_x24 v j x21 h22 (by omega)
  have A0 : zeroAddr.foldl stepV v .x0 = 0 := view_x0 wA
  obtain ⟨h1, w1, p1, m1⟩ := sb_step _ _ wA 518 .x24 .x0 0 (by decide) pA rfl (scratchBase + j)
    (by rw [eA, se12_0, Nat.add_zero]) (by unfold scratchBase; omega)
  obtain ⟨hN, wN, pN, mN⟩ := block_run _ 519 zeroNext _ w1 (by decide) p1
    (by intro i hi; simp only [zeroNext, List.length] at hi; interval_cases i <;> rfl) rfl
  have jm := jal_step _ 520 2097136 (by decide) pN rfl 516 rfl
  refine ⟨_, (((g.thenDo hA).thenDo h1).thenDo hN).thenDo jm,
    ⟨⟨_, view_pc_only _ _ _ wN, zn_x22 _ j (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact h22) (by omega),
      by rw [foldl_stepV_notin _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide)]; exact h23, ?_⟩,
      rfl, ?_⟩⟩
  · intro r hr
    rw [foldl_stepV_within zeroNext mainWrites (by decide) _ r hr,
      foldl_stepV_within zeroAddr mainWrites (by decide) _ r hr]
    exact fr r hr
  · intro q
    rw [setPC_getByte, getByte_of_mem mN, m1, getByte_of_mem mA, setPC_getByte, mem, A0]
    unfold zeroMem
    by_cases hq : q = BitVec.ofNat 64 (scratchBase + j)
    · subst hq
      have e : (BitVec.ofNat 64 (scratchBase + j)).toNat = scratchBase + j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      rw [if_pos rfl, e, if_pos (by omega)]
      rfl
    · rw [if_neg hq]
      have hq' : q.toNat ≠ scratchBase + j := by
        intro e; apply hq; apply BitVec.eq_of_toNat_eq
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold scratchBase; omega)]
      split_ifs <;> first | rfl | omega

theorem zero_loop (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input) :
    ∀ d j s, j + d = countOf input + input.positions.card → ZeroAt input vM j s →
      ∃ t, Hop s t (5*d) (5*d) ∧ ZeroAt input vM (countOf input + input.positions.card) t := by
  intro d
  induction d with
  | zero => intro j s e h; exact ⟨s, Hop.refl s, by simpa using e ▸ h⟩
  | succ d ih =>
    intro j s e h
    obtain ⟨t, ht, ha⟩ := zero_step input vM mv sz j (by omega) s h
    obtain ⟨u, hu, au⟩ := ih (j+1) t (by omega) ha
    exact ⟨u, (ht.thenDo hu).cast (by ring) (by ring), au⟩

/-! ### Final registers -/

def finalBlock : List Instr :=
  [.ADDI .x17 .x28 0] ++ unpackTemps.map (fun r => .ADDI r .x0 0) ++ [.MUL .x6 .x16 .x6]

theorem stepV_same (v : Reg → Nat) (i : Instr) (r : Reg) (h : aluDest i = r) (hr : r ≠ .x0) :
    stepV v i r = aluVal v i := by
  unfold stepV; rw [h]; exact setV_eq _ _ _ hr

theorem stepV_other (v : Reg → Nat) (i : Instr) (r : Reg) (h : aluDest i ≠ r) : stepV v i r = v r := by
  unfold stepV; exact setV_ne _ _ _ _ (fun e => h e.symm)

theorem clear_fold (rs : List Reg) (v : Reg → Nat) (h0 : v .x0 = 0) (r : Reg) :
    (rs.map (fun r => Instr.ADDI r .x0 0)).foldl stepV v r = if r ∈ rs then 0 else v r := by
  induction rs generalizing v with
  | nil => simp
  | cons a rs ih =>
    rw [List.map_cons, List.foldl_cons]
    have s0 : stepV v (.ADDI a .x0 0) = setV v a 0 := by
      unfold stepV; simp only [aluDest, aluVal, h0, se12_0, Nat.zero_add, Nat.zero_mod]
    rw [s0, ih _ (by unfold setV; split_ifs with h <;> simp_all)]
    by_cases m : r ∈ rs
    · simp [m]
    · simp only [m, ite_false, List.mem_cons, false_or, or_false]
      unfold setV
      by_cases e : r = a
      · subst e; by_cases z : r = .x0
        · subst z; simp [h0]
        · simp [z]
      · simp [e]

theorem final_fold (v : Reg → Nat) (h0 : v .x0 = 0) (r : Reg) :
    finalBlock.foldl stepV v r =
      if r = .x6 then (v .x16 * v .x6) % 2^64
      else if r ∈ unpackTemps then 0
      else if r = .x17 then (v .x28 + 0) % 2^64 else v r := by
  rw [finalBlock, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_cons,
    List.foldl_nil]
  have a0 : stepV v (.ADDI .x17 .x28 0) .x0 = 0 := by rw [stepV_other _ _ _ (by decide)]; exact h0
  by_cases r6 : r = .x6
  · subst r6
    rw [stepV_same _ (.MUL .x6 .x16 .x6) .x6 rfl (by decide), if_pos rfl]
    simp only [aluVal]
    rw [clear_fold _ _ a0, clear_fold _ _ a0, if_neg (by decide), if_neg (by decide),
      stepV_other _ _ _ (by decide), stepV_other _ _ _ (by decide)]
  · rw [if_neg r6, stepV_other _ _ _ (fun e => r6 e.symm), clear_fold _ _ a0]
    by_cases t : r ∈ unpackTemps
    · rw [if_pos t, if_pos t]
    · rw [if_neg t, if_neg t]
      by_cases r17 : r = .x17
      · subst r17; rw [stepV_same _ (.ADDI .x17 .x28 0) .x17 rfl (by decide), if_pos rfl]; rfl
      · rw [stepV_other _ _ _ (fun e => r17 e.symm), if_neg r17]

end TwoPermutationPrototype.Packed.Checker
