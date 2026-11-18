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
  if i < 498*k then
    (if i%498 < 15 then 21 else if i%498 = 15 then 21 else if i%498 < 46 then 25
     else if i%498 = 46 then 24 else if i%498 < 48 then 22
     else if (i%498-48)%30 = 29 then 31 else 33)
  else if (i-498*k)%30 = 29 then 23 else 25

def iterCycles (k i : Nat) : Nat :=
  if i < 498*k then
    (if i%498 < 15 then 30 else if i%498 = 15 then 30 else if i%498 < 46 then 34
     else if i%498 = 46 then 33 else if i%498 < 48 then 31
     else if (i%498-48)%30 = 29 then 52 else 54)
  else if (i-498*k)%30 = 29 then 38 else 40

theorem iter_steps_le (k i : Nat) : iterSteps k i ≤ 33 := by
  unfold iterSteps; split_ifs <;> omega

set_option maxHeartbeats 4000000 in
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
  have g0 := beq_step s v hv 445 .x22 .x0 276 (by decide) pc rfl 514 rfl
  rw [if_neg (by rw [h22, h0]; omega)] at g0
  have w0 := view_pc_only s v (BitVec.ofNat 64 (4096+4*(445+1))) hv
  obtain ⟨hL, wL, pL, mL⟩ := block_run _ 446 loopStep v w0 (by decide) rfl
    (by intro j hj; simp only [loopStep, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hsL : loopStep.foldl execInstrBr (s.setPC (BitVec.ofNat 64 (4096+4*(445+1)))) = sL at hL wL pL mL
  have eL := ls_x22' v (i+1) h22 (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at eL
  generalize hvL : loopStep.foldl stepV v = vL at wL eL
  have frL : ∀ r, r ∉ mainWrites → vL r = vM r := fun r hr => by
    rw [← hvL, foldl_stepV_within loopStep mainWrites (by decide) _ r hr]; exact fr r hr
  have memL : ∀ a, sL.getByte a = mainMem input (i+1) a := fun a => by rw [getByte_of_mem mL]; exact mem a
  have L0 : vL .x0 = 0 := view_x0 wL
  have L29 : vL .x29 = 498*k := by rw [← hvL, foldl_stepV_notin _ _ _ (by decide)]; exact x29
  have L16 : vL .x16 = k := by rw [← hvL, foldl_stepV_notin _ _ _ (by decide)]; exact x16
  have g1 := bgeu_step sL vL wL 447 .x22 .x29 172 (by decide) pL rfl 490 rfl
  rw [eL, L29] at g1
  have hm' : (i+1) - 1 = i := by omega
  by_cases rc : i < 498*k
  · rw [if_pos rc] at g1
    have w1 := view_pc_only sL vL (BitVec.ofNat 64 (4096+4*(447+1))) wL
    obtain ⟨hR, wR, pR, mR⟩ := block_run _ 448 recordBlock vL w1 (by decide) rfl
      (by intro j hj; simp only [recordBlock, List.length] at hj; interval_cases j <;> rfl) rfl
    generalize hsR : recordBlock.foldl execInstrBr (sL.setPC (BitVec.ofNat 64 (4096+4*(447+1)))) = sR
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
    have g2 := bgeu_step sR vR wR 455 .x25 .x23 88 (by decide) pR rfl 477 rfl
    rw [eR25, eR23] at g2
    have R15 : vR .x15 = proofBase := (frR .x15 (by decide)).trans mv.x15
    have R0 : vR .x0 = 0 := view_x0 wR
    have hr : i/498 < k := by omega
    by_cases hd : i%498 < 48
    · -- record head byte
      rw [if_pos hd] at g2
      have w2 := view_pc_only sR vR (BitVec.ofNat 64 (4096+4*(455+1))) wR
      obtain ⟨hT, wT, pT, mT⟩ := block_run _ 456 set15 vR w2 (by decide) rfl
        (by intro j hj; simp only [set15, List.length] at hj; interval_cases j <;> rfl) rfl
      generalize hsT : set15.foldl execInstrBr (sR.setPC (BitVec.ofNat 64 (4096+4*(455+1)))) = sT at hT wT pT mT
      have eT23 := s15_x23 vR R0
      have eT25 : set15.foldl stepV vR .x25 = i%498 := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eR25
      have eT26 : set15.foldl stepV vR .x26 = 481*(i/498) := by
        rw [foldl_stepV_notin _ _ _ (by decide)]; exact eR26
      have eT24 : set15.foldl stepV vR .x24 = i/498 := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eR24
      have eT22 : set15.foldl stepV vR .x22 = i := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eR22
      have eT15 : set15.foldl stepV vR .x15 = proofBase := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact R15
      generalize hvT : set15.foldl stepV vR = vT at wT eT23 eT25 eT26 eT24 eT22 eT15
      have frT : ∀ r, r ∉ mainWrites → vT r = vM r := fun r hr => by
        rw [← hvT, foldl_stepV_within set15 mainWrites (by decide) _ r hr]; exact frR r hr
      have memT : ∀ a, sT.getByte a = mainMem input (i+1) a := fun a => by
        rw [getByte_of_mem mT, setPC_getByte]; exact memR a
      have T0 : vT .x0 = 0 := view_x0 wT
      have g3 := bltu_step sT vT wT 457 .x25 .x23 28 (by decide) pT rfl 464 rfl
      rw [eT25, eT23] at g3
      have pre := ((((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hT).thenDo g3)
      by_cases o1 : i%498 < 15
      · -- salt bytes 0..14: copy packed byte 481r + o
        rw [if_pos o1] at g3 pre
        have w3 := view_pc_only sT vT (BitVec.ofNat 64 (4096+4*464)) wT
        obtain ⟨hS, wS, pS, mS⟩ := block_run _ 464 srcBlock vT w3 (by decide) rfl
          (by intro j hj; simp only [srcBlock, List.length] at hj; interval_cases j <;> rfl) rfl
        have eS := sb_x26 vT (481*(i/498)) (i%498) eT26 eT25 (by omega)
        have j4 := jal_step _ 465 164 (by decide) pS rfl 506 rfl
        have w4 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*506)) wS
        obtain ⟨hA, wA, pA, mA⟩ := block_run _ 506 addBase _ w4 (by decide) rfl
          (by intro j hj; simp only [addBase, List.length] at hj; interval_cases j <;> rfl) rfl
        have eA := ab_x26 (srcBlock.foldl stepV vT) (481*(i/498) + i%498) eS
          (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eT15) (by omega)
        obtain ⟨t, ht, at'⟩ := copy_tail input vM mv sz (i+1) (by omega) hl _ _ wA pA
          (by rw [foldl_stepV_notin _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), hm']; exact eT22)
          (fun r hr => by
            rw [foldl_stepV_within addBase mainWrites (by decide) _ r hr,
              foldl_stepV_within srcBlock mainWrites (by decide) _ r hr]; exact frT r hr)
          (fun a => by rw [getByte_of_mem mA, setPC_getByte, getByte_of_mem mS, setPC_getByte]; exact memT a)
          _ eA (by omega) (by rw [hm', ub_src _ _ _ _ (hk ▸ rc) o1])
        rw [hm'] at at'
        refine ⟨t, ?_, at'⟩
        have e1 : iterSteps k i = 21 := by simp only [iterSteps, rc, o1, ite_true]
        have e2 : iterCycles k i = 30 := by simp only [iterCycles, rc, o1, ite_true]
        rw [e1, e2]
        exact (((pre.thenDo hS).thenDo j4).thenDo hA).thenDo ht
      rw [if_neg o1] at g3 pre
      have w3 := view_pc_only sT vT (BitVec.ofNat 64 (4096+4*(457+1))) wT
      have g4 := beq_step _ vT w3 458 .x25 .x23 44 (by decide) rfl rfl 469 rfl
      rw [eT25, eT23] at g4
      by_cases o2 : i%498 = 15
      · -- salt byte 15: low bits of the stashed byte
        rw [if_pos o2] at g4
        obtain ⟨t, ht, at'⟩ := salt_tail input vM mv sz (i+1) (by omega) hl _ _ (view_pc_only _ _ _ w3) rfl
          (by rw [hm']; exact eT22) frT (fun a => by rw [setPC_getByte, setPC_getByte]; exact memT a)
          (i/498) eT24 (by omega) (by rw [hm', ub_salt _ _ _ _ (hk ▸ rc) o2])
        rw [hm'] at at'
        refine ⟨t, ?_, at'⟩
        have e1 : iterSteps k i = 21 := by simp [iterSteps, rc, o2]
        have e2 : iterCycles k i = 30 := by simp [iterCycles, rc, o2]
        rw [e1, e2]
        exact (pre.thenDo g4).thenDo ht
      rw [if_neg o2] at g4
      have w4 := view_pc_only sT vT (BitVec.ofNat 64 (4096+4*(458+1))) wT
      obtain ⟨hF, wF, pF, mF⟩ := block_run _ 459 set46 vT w4 (by decide) rfl
        (by intro j hj; simp only [set46, List.length] at hj; interval_cases j <;> rfl) rfl
      have eF23 := s46_x23 vT T0
      have eF25 : set46.foldl stepV vT .x25 = i%498 := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eT25
      have g5 := bltu_step _ _ wF 460 .x25 .x23 24 (by decide) pF rfl 466 rfl
      rw [eF25, eF23] at g5
      have frF : ∀ r, r ∉ mainWrites → set46.foldl stepV vT r = vM r := fun r hr => by
        rw [foldl_stepV_within set46 mainWrites (by decide) _ r hr]; exact frT r hr
      have memF : ∀ a, (set46.foldl execInstrBr (sT.setPC (BitVec.ofNat 64 (4096+4*(458+1))))).getByte a =
          mainMem input (i+1) a := fun a => by
        rw [getByte_of_mem mF, setPC_getByte]; exact memT a
      have eF22 : set46.foldl stepV vT .x22 = i := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eT22
      have eF24 : set46.foldl stepV vT .x24 = i/498 := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eT24
      have pre2 := ((pre.thenDo g4).thenDo hF).thenDo g5
      by_cases o3 : i%498 < 46
      · -- leaf bytes 0..29: copy packed byte 481r + o - 1
        rw [if_pos o3] at g5 pre2
        have w5 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*466)) wF
        obtain ⟨hS, wS, pS, mS⟩ := block_run _ 466 leafBlock _ w5 (by decide) rfl
          (by intro j hj; simp only [leafBlock, List.length] at hj; interval_cases j <;> rfl) rfl
        have eS := lb_x26 (set46.foldl stepV vT) (481*(i/498)) (i%498)
          (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact eT26) eF25 (by omega) (by omega)
        have j6 := jal_step _ 468 152 (by decide) pS rfl 506 rfl
        have w6 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*506)) wS
        obtain ⟨hA, wA, pA, mA⟩ := block_run _ 506 addBase _ w6 (by decide) rfl
          (by intro j hj; simp only [addBase, List.length] at hj; interval_cases j <;> rfl) rfl
        have eA := ab_x26 (leafBlock.foldl stepV (set46.foldl stepV vT)) (481*(i/498) + i%498 - 1) eS
          (by rw [foldl_stepV_notin _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide)]; exact eT15)
          (by omega)
        obtain ⟨t, ht, at'⟩ := copy_tail input vM mv sz (i+1) (by omega) hl _ _ wA pA
          (by rw [foldl_stepV_notin _ _ _ (by decide), foldl_stepV_notin _ _ _ (by decide), hm']; exact eF22)
          (fun r hr => by
            rw [foldl_stepV_within addBase mainWrites (by decide) _ r hr,
              foldl_stepV_within leafBlock mainWrites (by decide) _ r hr]; exact frF r hr)
          (fun a => by rw [getByte_of_mem mA, setPC_getByte, getByte_of_mem mS, setPC_getByte]; exact memF a)
          _ eA (by omega) (by rw [hm', ub_leaf _ _ _ _ (hk ▸ rc) (by omega) o3])
        rw [hm'] at at'
        refine ⟨t, ?_, at'⟩
        have e1 : iterSteps k i = 25 := by simp only [iterSteps, rc, o1, o2, o3, ite_true, ite_false]
        have e2 : iterCycles k i = 34 := by simp only [iterCycles, rc, o1, o2, o3, ite_true, ite_false]
        rw [e1, e2]
        exact (((pre2.thenDo hS).thenDo j6).thenDo hA).thenDo ht
      rw [if_neg o3] at g5 pre2
      have w5 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*(460+1))) wF
      have g6 := beq_step _ _ w5 461 .x25 .x23 48 (by decide) rfl rfl 473 rfl
      rw [eF25, eF23] at g6
      by_cases o4 : i%498 = 46
      · -- leaf byte 30: high bits of the stashed byte
        rw [if_pos o4] at g6
        obtain ⟨t, ht, at'⟩ := leaf_tail input vM mv sz (i+1) (by omega) hl _ _ (view_pc_only _ _ _ w5) rfl
          (by rw [hm']; exact eF22) frF (fun a => by rw [setPC_getByte, setPC_getByte]; exact memF a)
          (i/498) eF24 (by omega) (by rw [hm', ub_leaf30 _ _ _ _ (hk ▸ rc) o4])
        rw [hm'] at at'
        refine ⟨t, ?_, at'⟩
        have e1 : iterSteps k i = 24 := by simp [iterSteps, rc, o4]
        have e2 : iterCycles k i = 33 := by simp [iterCycles, rc, o4]
        rw [e1, e2]
        exact (pre2.thenDo g6).thenDo ht
      · -- leaf byte 31: zero
        rw [if_neg o4] at g6
        obtain ⟨t, ht, at'⟩ := zero_tail input vM mv sz (i+1) (by omega) hl _ _ (view_pc_only _ _ _ w5) rfl
          (by rw [hm']; exact eF22) frF (fun a => by rw [setPC_getByte, setPC_getByte]; exact memF a)
          (by rw [hm', ub_zero _ _ _ _ (hk ▸ rc) (by omega)])
        rw [hm'] at at'
        refine ⟨t, ?_, at'⟩
        have o5 : i%498 = 47 := by omega
        have e1 : iterSteps k i = 22 := by simp [iterSteps, rc, o5]
        have e2 : iterCycles k i = 31 := by simp [iterCycles, rc, o5]
        rw [e1, e2]
        exact (pre2.thenDo g6).thenDo ht
    · -- record digest byte
      rw [if_neg hd] at g2
      have w2 := view_pc_only sR vR (BitVec.ofNat 64 (4096+4*477)) wR
      obtain ⟨hD, wD, pD, mD⟩ := block_run _ 477 digestBlock vR w2 (by decide) rfl
        (by intro j hj; simp only [digestBlock, List.length] at hj; interval_cases j <;> rfl) rfl
      have eD25 := dg_x25 vR (i%498) R0 eR25 eR23 (by omega) (by omega)
      have eD26 := dg_x26 vR (i%498) (i/498) R0 eR25 eR23 eR26 (by omega) (by omega) (by omega)
      have eD30 := dg_x30 vR (i%498) (i/498) R0 eR25 eR23 eR24 (by omega) (by omega) (by omega)
      have j3 := jal_step _ 489 56 (by decide) pD rfl 503 rfl
      obtain ⟨t, ht, at'⟩ := digit_tail input vM mv sz (i+1) (by omega) hl _ _ (view_pc_only _ _ _ wD) rfl
        (by rw [foldl_stepV_notin _ _ _ (by decide), hm']; exact eR22)
        (fun r hr => by rw [foldl_stepV_within digestBlock mainWrites (by decide) _ r hr]; exact frR r hr)
        (fun a => by rw [setPC_getByte, getByte_of_mem mD, setPC_getByte]; exact memR a)
        ((i%498-48)%30) (15*(i/498) + (i%498-48)/30)
        (481*(i/498) + 46 + 29*((i%498-48)/30) + (i%498-48)%30)
        eD25 eD30 (by omega) (by rw [eD26]) (by omega)
        (fun c29 => ⟨by omega, by rw [hm', ub_rec29 _ _ _ _ (hk ▸ rc) hd c29, hk]⟩)
        (fun c29 => by rw [hm', ub_rec _ _ _ _ (hk ▸ rc) hd c29])
      rw [hm'] at at'
      refine ⟨t, ?_, at'⟩
      by_cases c29 : (i%498-48)%30 = 29
      · have e1 : iterSteps k i = 31 := by
          simp only [iterSteps, rc, hd, c29, ite_true, ite_false]; split_ifs <;> omega
        have e2 : iterCycles k i = 52 := by
          simp only [iterCycles, rc, hd, c29, ite_true, ite_false]; split_ifs <;> omega
        rw [e1, e2]
        rw [if_pos c29] at ht
        exact (((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hD).thenDo j3 |>.thenDo ht
      · have e1 : iterSteps k i = 33 := by
          simp only [iterSteps, rc, hd, c29, ite_true, ite_false]; split_ifs <;> omega
        have e2 : iterCycles k i = 54 := by
          simp only [iterCycles, rc, hd, c29, ite_true, ite_false]; split_ifs <;> omega
        rw [e1, e2]
        rw [if_neg c29] at ht
        exact (((((g0.thenDo hL).thenDo g1).thenDo hR).thenDo g2).thenDo hD).thenDo j3 |>.thenDo ht
  · -- footer digest byte
    rw [if_neg rc] at g1
    have w1 := view_pc_only sL vL (BitVec.ofNat 64 (4096+4*490)) wL
    obtain ⟨hF, wF, pF, mF⟩ := block_run _ 490 footBlock vL w1 (by decide) rfl
      (by intro j hj; simp only [footBlock, List.length] at hj; interval_cases j <;> rfl) rfl
    have eF25 := ft_x25 vL i k L0 eL L29 (by omega) (by omega)
    have eF26 := ft_x26 vL i k L0 eL L29 L16 (by omega) (by omega) kb
    have eF30 := ft_x30 vL i k L0 eL L29 L16 (by omega) (by omega) kb
    have ilen : i < 48*k + 30*countOf input := by omega
    obtain ⟨t, ht, at'⟩ := digit_tail input vM mv sz (i+1) (by omega) hl _ _ wF pF
      (by rw [foldl_stepV_notin _ _ _ (by decide), hm']; exact eL)
      (fun r hr => by rw [foldl_stepV_within footBlock mainWrites (by decide) _ r hr]; exact frL r hr)
      (fun a => by rw [getByte_of_mem mF, setPC_getByte]; exact memL a)
      ((i-498*k)%30) (15*k + (i-498*k)/30) (481*k + 29*((i-498*k)/30) + (i-498*k)%30)
      eF25 eF30 (by omega) (by rw [eF26]) (by omega)
      (fun c29 => ⟨by omega, by rw [hm', ub_foot29 _ _ _ _ (hk ▸ rc) (hk ▸ c29), hk]⟩)
      (fun c29 => by rw [hm', ub_foot _ _ _ _ (hk ▸ rc) (hk ▸ c29), hk])
    rw [hm'] at at'
    refine ⟨t, ?_, at'⟩
    by_cases c29 : (i-498*k)%30 = 29
    · have e1 : iterSteps k i = 23 := by simp only [iterSteps, rc, c29, ite_true, ite_false]
      have e2 : iterCycles k i = 38 := by simp only [iterCycles, rc, c29, ite_true, ite_false]
      rw [e1, e2]
      rw [if_pos c29] at ht
      exact (((g0.thenDo hL).thenDo g1).thenDo hF).thenDo ht
    · have e1 : iterSteps k i = 25 := by simp only [iterSteps, rc, c29, ite_true, ite_false]
      have e2 : iterCycles k i = 40 := by simp only [iterCycles, rc, c29, ite_true, ite_false]
      rw [e1, e2]
      rw [if_neg c29] at ht
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
