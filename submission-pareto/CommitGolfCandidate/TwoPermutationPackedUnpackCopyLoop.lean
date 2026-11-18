import CommitGolfCandidate.TwoPermutationPackedUnpackCopyStep

/-! The copy loop: one iteration per unpacked byte, from the last byte down. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- Steps of the copy-loop iteration that writes unpacked byte `i`. -/
def iterSteps (k i : Nat) : Nat :=
  if i < 498*k then (if i%498 < 48 then 19 else if (i%498-48)%30 = 29 then 27 else 32)
  else if (i-498*k)%30 = 29 then 21 else 26

def iterCycles (k i : Nat) : Nat :=
  if i < 498*k then (if i%498 < 48 then 28 else if (i%498-48)%30 = 29 then 45 else 53)
  else if (i-498*k)%30 = 29 then 33 else 41

theorem iter_steps_le (k i : Nat) : iterSteps k i ≤ 32 := by
  unfold iterSteps; split_ifs <;> omega

theorem main_step (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (i : Nat) (hl : i+1 ≤ lenOf input) (s : MachineState) (h : MainAt input vM (i+1) s) :
    ∃ t, Hop s t (iterSteps input.positions.card i) (iterCycles input.positions.card i) ∧
      MainAt input vM i t := by
  obtain ⟨⟨v, hv, h22, fr⟩, pc, mem⟩ := h
  have len := sz.len
  have kb := sz.k
  have nb := sz.n
  have recs := sz.records
  have h0 : v .x0 = 0 := view_x0 hv
  have x29 : v .x29 = 498*input.positions.card := (fr .x29 (by decide)).trans mv.x29
  have x16 : v .x16 = input.positions.card := (fr .x16 (by decide)).trans mv.x16
  have x15 : v .x15 = proofBase := (fr .x15 (by decide)).trans mv.x15
  generalize hk : input.positions.card = k at x29 x16 kb recs ⊢
  have lenk : lenOf input = 48*k + 30*countOf input := by rw [← hk]; rfl
  -- loop test, decrement, footer test
  have g0 := beq_step s v hv 432 .x22 .x0 188 (by decide) pc rfl 479 rfl
  rw [if_neg (by rw [h22, h0]; omega)] at g0
  have w0 := view_pc_only s v (BitVec.ofNat 64 (4096+4*(432+1))) hv
  obtain ⟨hL, wL, pL, mL⟩ := block_run _ 433 loopStep v w0 (by decide) rfl
    (by intro j hj; simp only [loopStep, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hsL : loopStep.foldl execInstrBr (s.setPC (BitVec.ofNat 64 (4096+4*(432+1)))) = sL at hL wL pL mL
  have eL := ls_x22 v (i+1) h22 (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at eL
  generalize hvL : loopStep.foldl stepV v = vL at wL eL
  have frL : ∀ r, r ∉ mainWrites → vL r = vM r := fun r hr => by
    rw [← hvL, foldl_stepV_within loopStep mainWrites (by decide) _ r hr]; exact fr r hr
  have memL : ∀ a, sL.getByte a = mainMem input (i+1) a := fun a => by rw [getByte_of_mem mL]; exact mem a
  have L0 : vL .x0 = 0 := view_x0 wL
  have L29 : vL .x29 = 498*k := by rw [← hvL, foldl_stepV_notin _ _ _ (by decide)]; exact x29
  have L16 : vL .x16 = k := by rw [← hvL, foldl_stepV_notin _ _ _ (by decide)]; exact x16
  have g1 := bgeu_step sL vL wL 434 .x22 .x29 80 (by decide) pL rfl 454 rfl
  rw [eL, L29] at g1
  have hm' : (i+1) - 1 = i := by omega
  by_cases rc : i < 498*k
  · rw [if_pos rc] at g1
    have w1 := view_pc_only sL vL (BitVec.ofNat 64 (4096+4*(434+1))) wL
    obtain ⟨hR, wR, pR, mR⟩ := block_run _ 435 recordBlock vL w1 (by decide) rfl
      (by intro j hj; simp only [recordBlock, List.length] at hj; interval_cases j <;> rfl) rfl
    generalize hsR : recordBlock.foldl execInstrBr (sL.setPC (BitVec.ofNat 64 (4096+4*(434+1)))) = sR
      at hR wR pR mR
    have eR24 := rc_x24 vL i L0 eL (by omega)
    have eR25 := rc_x25 vL i L0 eL (by omega)
    have eR26 := rc_x26 vL i L0 eL (by omega)
    have eR23 := rc_x23 vL L0
    have eR22 : recordBlock.foldl stepV vL .x22 = i := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eL
    generalize hvR : recordBlock.foldl stepV vL = vR at wR eR24 eR25 eR26 eR23 eR22
    have frR : ∀ r, r ∉ mainWrites → vR r = vM r := fun r hr => by
      rw [← hvR, foldl_stepV_within recordBlock mainWrites (by decide) _ r hr]; exact frL r hr
    have memR : ∀ a, sR.getByte a = mainMem input (i+1) a := fun a => by
      rw [getByte_of_mem mR, setPC_getByte]; exact memL a
    have g2 := bgeu_step sR vR wR 442 .x25 .x23 12 (by decide) pR rfl 445 rfl
    rw [eR25, eR23] at g2
    have R15 : vR .x15 = proofBase := (frR .x15 (by decide)).trans mv.x15
    by_cases hd : i%498 < 48
    · -- record head byte
      rw [if_pos hd] at g2
      have w2 := view_pc_only sR vR (BitVec.ofNat 64 (4096+4*(442+1))) wR
      obtain ⟨hH, wH, pH, mH⟩ := block_run _ 443 headBlock vR w2 (by decide) rfl
        (by intro j hj; simp only [headBlock, List.length] at hj; interval_cases j <;> rfl) rfl
      have eH := hb_x26 vR (483*(i/498)) (i%498) eR26 eR25 (by omega)
      have j3 := jal_step _ 444 108 (by decide) pH rfl 471 rfl
      have w3 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*471)) wH
      obtain ⟨hA, wA, pA, mA⟩ := block_run _ 471 addBase _ w3 (by decide) rfl
        (by intro j hj; simp only [addBase, List.length] at hj; interval_cases j <;> rfl) rfl
      have eA := ab_x26 (headBlock.foldl stepV vR) (483*(i/498) + i%498) eH
        (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact R15) (by omega)
      obtain ⟨t, ht, at'⟩ := copy_tail input vM mv sz (i+1) (by omega) hl _ _ wA pA
        (by rw [foldl_stepV_notin _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), hm']; exact eR22)
        (fun r hr => by
          rw [foldl_stepV_within addBase mainWrites (by decide) _ r hr,
            foldl_stepV_within headBlock mainWrites (by decide) _ r hr]; exact frR r hr)
        (fun a => by rw [getByte_of_mem mA, setPC_getByte, getByte_of_mem mH, setPC_getByte]; exact memR a)
        _ eA (by omega) (by rw [hm', ub_head _ _ _ _ (hk ▸ rc) hd])
      rw [hm'] at at'
      refine ⟨t, ?_, at'⟩
      have e1 : iterSteps k i = 19 := by simp only [iterSteps, rc, hd, ite_true]
      have e2 : iterCycles k i = 28 := by simp only [iterCycles, rc, hd, ite_true]
      rw [e1, e2]
      exact (((((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hH).thenDo j3).thenDo hA).thenDo ht
    · -- record digest byte
      rw [if_neg hd] at g2
      have w2 := view_pc_only sR vR (BitVec.ofNat 64 (4096+4*445)) wR
      obtain ⟨hD, wD, pD, mD⟩ := block_run _ 445 digestBlock vR w2 (by decide) rfl
        (by intro j hj; simp only [digestBlock, List.length] at hj; interval_cases j <;> rfl) rfl
      have R0 : vR .x0 = 0 := view_x0 wR
      have eD25 := dg_x25 vR (i%498) R0 eR25 eR23 (by omega) (by omega)
      have eD27 := dg_x27 vR (i%498) R0 eR25 eR23 (by omega) (by omega)
      have eD30 := dg_x30 vR (i%498) (i/498) R0 eR25 eR23 eR24 (by omega) (by omega) (by omega)
      have eD26 : digestBlock.foldl stepV vR .x26 = 483*(i/498) := by
        rw [foldl_stepV_notin _ _ _ (by decide)]; exact eR26
      have j3 := jal_step _ 453 48 (by decide) pD rfl 465 rfl
      obtain ⟨t, ht, at'⟩ := digit_tail input vM mv sz (i+1) (by omega) hl _ _ (view_pc_only _ _ _ wD) rfl
        (by rw [foldl_stepV_notin _ _ _ (by decide), hm']; exact eR22)
        (fun r hr => by rw [foldl_stepV_within digestBlock mainWrites (by decide) _ r hr]; exact frR r hr)
        (fun a => by rw [setPC_getByte, getByte_of_mem mD, setPC_getByte]; exact memR a)
        ((i%498-48)%30) ((i%498-48)/30) (15*(i/498) + (i%498-48)/30)
        (483*(i/498) + 48 + 29*((i%498-48)/30) + (i%498-48)%30)
        eD25 eD27 eD30 (by omega) (by omega) (by rw [eD26]; vmod)
        (by omega)
        (fun c29 => ⟨by omega, by rw [hm', ub_rec29 _ _ _ _ (hk ▸ rc) hd c29, hk]⟩)
        (fun c29 => by rw [hm', ub_rec _ _ _ _ (hk ▸ rc) hd c29])
      rw [hm'] at at'
      refine ⟨t, ?_, at'⟩
      by_cases c29 : (i%498-48)%30 = 29
      · have e1 : iterSteps k i = 27 := by simp only [iterSteps, rc, hd, c29, ite_true, ite_false]
        have e2 : iterCycles k i = 45 := by simp only [iterCycles, rc, hd, c29, ite_true, ite_false]
        rw [e1, e2]
        rw [if_pos c29, if_pos c29] at ht
        exact (((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hD).thenDo j3 |>.thenDo ht
      · have e1 : iterSteps k i = 32 := by simp only [iterSteps, rc, hd, c29, ite_true, ite_false]
        have e2 : iterCycles k i = 53 := by simp only [iterCycles, rc, hd, c29, ite_true, ite_false]
        rw [e1, e2]
        rw [if_neg c29, if_neg c29] at ht
        exact (((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hD).thenDo j3 |>.thenDo ht
  · -- footer digest byte
    rw [if_neg rc] at g1
    have w1 := view_pc_only sL vL (BitVec.ofNat 64 (4096+4*454)) wL
    obtain ⟨hF, wF, pF, mF⟩ := block_run _ 454 footBlock vL w1 (by decide) rfl
      (by intro j hj; simp only [footBlock, List.length] at hj; interval_cases j <;> rfl) rfl
    have eF25 := ft_x25 vL i k L0 eL L29 (by omega) (by omega)
    have eF27 := ft_x27 vL i k L0 eL L29 (by omega) (by omega)
    have eF30 := ft_x30 vL i k L0 eL L29 L16 (by omega) (by omega) kb
    have eF26 := ft_x26 vL k L0 L16 kb
    have ilen : i < 48*k + 30*countOf input := by omega
    obtain ⟨t, ht, at'⟩ := digit_tail input vM mv sz (i+1) (by omega) hl _ _ wF pF
      (by rw [foldl_stepV_notin _ _ _ (by decide), hm']; exact eL)
      (fun r hr => by rw [foldl_stepV_within footBlock mainWrites (by decide) _ r hr]; exact frL r hr)
      (fun a => by rw [getByte_of_mem mF, setPC_getByte]; exact memL a)
      ((i-498*k)%30) ((i-498*k)/30) (15*k + (i-498*k)/30) (483*k + 29*((i-498*k)/30) + (i-498*k)%30)
      eF25 eF27 eF30 (by omega) (by omega) (by rw [eF26]; simp only [Nat.reducePow]; omega)
      (by omega)
      (fun c29 => ⟨by omega, by rw [hm', ub_foot29 _ _ _ _ (hk ▸ rc) (hk ▸ c29), hk]⟩)
      (fun c29 => by rw [hm', ub_foot _ _ _ _ (hk ▸ rc) (hk ▸ c29), hk])
    rw [hm'] at at'
    refine ⟨t, ?_, at'⟩
    by_cases c29 : (i-498*k)%30 = 29
    · have e1 : iterSteps k i = 21 := by simp only [iterSteps, rc, c29, ite_true, ite_false]
      have e2 : iterCycles k i = 33 := by simp only [iterCycles, rc, c29, ite_true, ite_false]
      rw [e1, e2]
      rw [if_pos c29, if_pos c29] at ht
      exact (((g0.thenDo hL).thenDo g1).thenDo hF).thenDo ht
    · have e1 : iterSteps k i = 26 := by simp only [iterSteps, rc, c29, ite_true, ite_false]
      have e2 : iterCycles k i = 41 := by simp only [iterCycles, rc, c29, ite_true, ite_false]
      rw [e1, e2]
      rw [if_neg c29, if_neg c29] at ht
      exact (((g0.thenDo hL).thenDo g1).thenDo hF).thenDo ht

theorem main_loop (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input) :
    ∀ m s, m ≤ lenOf input → MainAt input vM m s →
      ∃ t, Hop s t (∑ i ∈ Finset.range m, iterSteps input.positions.card i)
        (∑ i ∈ Finset.range m, iterCycles input.positions.card i) ∧ MainAt input vM 0 t := by
  intro m
  induction m with
  | zero => intro s _ h; exact ⟨s, by simpa using Hop.refl s, h⟩
  | succ m ih =>
    intro s hl h
    obtain ⟨t, ht, at'⟩ := main_step input vM mv sz m hl s h
    obtain ⟨u, hu, au⟩ := ih t (by omega) at'
    refine ⟨u, ?_, au⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_comm _ (iterSteps _ m),
      Nat.add_comm _ (iterCycles _ m)]
    exact ht.thenDo hu

end TwoPermutationPrototype.Packed.Checker
