import CommitGolfCandidate.MoonCheckCapPair

/-! Symbolic execution of cap-level composition, full bottom-up cap walk, and epilogue (`pc[197..245]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_225_reject : pcWord 225 + signExtend13 72#13 = pcWord 243 := by decide
private theorem pc_226_reject : pcWord 226 + signExtend13 68#13 = pcWord 243 := by decide

/-- Complete cap-level step `l = 16 + step` (`step < 8`), sweeping `q = m - 1` down to `0`
(`m = levelSize (l + 1)`). -/
theorem step_cap_level (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sPos : MachineState) (step : Nat) (hstep : step < 8)
    (s : MachineState) (trPrev : List PublicRow)
    (hinv : CapWalkInv h512 oracle input sPos step s trPrev) :
    let l := 16 + step
    let pBase := 498 * input.positions.card
    let tBase := 10 * input.positions.card
    PhaseOutcome oracle s (225 * levelSize (l + 1)) input.positions.card
      (input.proof.length <
        pBase + 29 * capFrontierPrefix input.positions (step + 1) +
        tailBytes (tBase + capFrontierPrefix input.positions (step + 1)))
      (fun s' calls tr =>
        calls ≤ input.positions.card ∧
        CapWalkInv h512 oracle input sPos (step + 1) s' (trPrev ++ tr)) := by
  intro l pBase tBase
  have hl1 : 16 ≤ l := by omega
  have hl2 : l < 24 := by omega
  let s0 := submission.initialState .check input
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let m := levelSize (l + 1)
  have hm_pos : 0 < m := levelSize_pos (l + 1)
  have hls_dbl : levelSize l = 2 * m := levelSize_double l hl2
  have hls_le : levelSize l ≤ 256 := levelSize_cap_le256 l hl1 (by omega)
  have hpc_s : s.pc = pcWord 198 := by have := hinv.pc; rwa [if_neg (by omega : step ≠ 8)] at this
  let pLvl := pBase + 29 * capFrontierPrefix input.positions step
  let tLvl := tBase + capFrontierPrefix input.positions step
  -- Inner induction over n ≤ m (processing k = 0..n-1, q = m - 1 - k, h = 2*m - 1 - k)
  have hind : ∀ n ≤ m,
      PhaseOutcome oracle s (225 * n) (pairMarkedNextCountRev input.positions l n)
        (input.proof.length <
          pLvl + 29 * pairFrontierCountRev input.positions l n +
          tailBytes (tLvl + pairFrontierCountRev input.positions l n))
        (fun sn calls tr =>
          calls ≤ pairMarkedNextCountRev input.positions l n ∧
          sn.pc = (if step = 7 ∧ n = m then pcWord 225 else pcWord 198) ∧
          CheckFixedRegs sn ∧
          sn.getReg .x11 = 64#64 ∧
          sn.getReg .x13 = 0#64 ∧
          ProofCursor s0 input.proof.length
            (pLvl + 29 * pairFrontierCountRev input.positions l n)
            (tLvl + pairFrontierCountRev input.positions l n) sn ∧
          HighMemPreserved s0 sn ∧
          sn.getReg .x23 = BitVec.ofNat 64 (2 * m - 1 - n) ∧
          (∀ idx < levelSize l, sn.getByte (BitVec.ofNat 64 (8192 + heapIdx l idx)) =
            if capMark input.positions l idx then 1#8 else 0#8) ∧
          (∀ j < n, sn.getByte (BitVec.ofNat 64 (8192 + heapIdx (l + 1) (m - 1 - j))) =
            if capMark input.positions (l + 1) (m - 1 - j) then 1#8 else 0#8) ∧
          (∀ h' < 2 * m - n, sn.getByte (BitVec.ofNat 64 (8192 + h')) = 0#8) ∧
          (∀ a : Nat, a < 2 ^ 64 →
            (∀ j < n, a ≠ 8192 + heapIdx (l + 1) (m - 1 - j)) →
            (∀ j < n, ∀ idx, (idx = 2 * (m - 1 - j) ∨ idx = 2 * (m - 1 - j) + 1) →
              capMark input.positions l idx = false →
              a < 16384 + 32 * heapIdx l idx ∨ 16384 + 32 * heapIdx l idx + 32 ≤ a) →
            (∀ j < n, capMark input.positions (l + 1) (m - 1 - j) = true →
              a < 16384 + 32 * heapIdx (l + 1) (m - 1 - j) ∨
              16384 + 32 * heapIdx (l + 1) (m - 1 - j) + 32 ≤ a) →
            sn.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
          (∀ j < n, capMark input.positions (l + 1) (m - 1 - j) = true →
            let q := m - 1 - j
            let dL := readBuffer sn (16384 + 32 * heapIdx l (2 * q)) 32
            let dR := readBuffer sn (16384 + 32 * heapIdx l (2 * q + 1)) 32
            let pAt := pLvl + 29 * pairFrontierCountRev input.positions l j
            let tAt := tLvl + pairFrontierCountRev input.positions l j
            readBuffer sn (16384 + 32 * heapIdx (l + 1) q) 32 =
              (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
            InCompRows h512 oracle tr (binaryInput dL dR) ∧
            (capMark input.positions l (2 * q) = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pAt) tAt) ∧
            (capMark input.positions l (2 * q + 1) = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pAt) tAt))) := by
    intro n hn
    induction n with
    | zero =>
      refine .continued s 0 0 [] (Nat.zero_le _) (Nat.zero_le _) (StepsTo.refl oracle s) ?_
      refine ⟨Nat.zero_le _, by simp [Nat.ne_of_lt hm_pos, hpc_s], hinv.fixed, hinv.x11, hinv.x13,
        by simpa [pairFrontierCountRev_zero, pLvl, tLvl] using hinv.cursor,
        hinv.high, by rw [Nat.sub_zero, ← hls_dbl]; exact hinv.x23,
        hinv.mark_cur hstep,
        fun _ h => (Nat.not_lt_zero _ h).elim,
        fun h' hh' => hinv.mark_lo_zero hstep h' (by change h' < levelSize l; omega),
        fun _ _ _ _ _ => rfl,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      have hk_lt : k < m := by omega
      let q := m - 1 - k
      have hq_lt : q < m := by omega
      have hh_eq : heapIdx (l + 1) q = 2 * m - 1 - k := by unfold heapIdx; dsimp only [m, q]; omega
      have hcm_succ : capMark input.positions (l + 1) q =
          (capMark input.positions l (2 * q) || capMark input.positions l (2 * q + 1)) :=
        capMark_succ input.positions l q hl1 hq_lt
      have hrej_mono : input.proof.length <
            pLvl + 29 * pairFrontierCountRev input.positions l k +
            tailBytes (tLvl + pairFrontierCountRev input.positions l k) →
          input.proof.length <
            pLvl + 29 * pairFrontierCountRev input.positions l (k + 1) +
            tailBytes (tLvl + pairFrontierCountRev input.positions l (k + 1)) := by
        have hfm := pairFrontierCountRev_mono input.positions l (show k ≤ k + 1 by omega)
        have htm := tailBytes_mono (show tLvl + pairFrontierCountRev input.positions l k ≤
          tLvl + pairFrontierCountRev input.positions l (k + 1) by omega)
        omega
      rw [show 225 * (k + 1) = 225 * k + 225 by omega, pairMarkedNextCountRev_succ]
      refine (ih (by omega)).bind_dep hrej_mono (fun sk calls1 tr1 ⟨hcalls1, hpc1, hfix1, h11_1, h13_1,
          hcur1, hhigh1, hx23_1, hmkL, hmkN, hmkLo, hpres1, hdone1⟩ => by
        have hpc_k : sk.pc = pcWord 198 := by
          have : ¬ (step = 7 ∧ k = m) := by omega
          rwa [if_neg this] at hpc1
        let pCur := pLvl + 29 * pairFrontierCountRev input.positions l k
        let tCur := tLvl + pairFrontierCountRev input.positions l k
        have hnode := step_cap_node h512 oracle input hvalid l q pCur tCur hl1 hl2 hq_lt
          sk hpc_k hfix1 h11_1 h13_1 hcur1 hhigh1 (by rw [hh_eq]; exact hx23_1)
          (hmkL (2 * q) (by omega)) (hmkL (2 * q + 1) (by omega))
          (hmkLo (heapIdx (l + 1) q) (by omega))
        have hcan_k : ((capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) = true ∧
            input.proof.length < pCur + 29 + tailBytes (tCur + 1)) →
            input.proof.length <
              pLvl + 29 * pairFrontierCountRev input.positions l (k + 1) +
              tailBytes (tLvl + pairFrontierCountRev input.positions l (k + 1)) := by
          rintro ⟨hbne, hlt⟩
          dsimp only [pCur, tCur] at hlt
          rw [pairFrontierCountRev_succ]
          change input.proof.length < pLvl + 29 * (pairFrontierCountRev input.positions l k +
            if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 1 else 0) +
            tailBytes (tLvl + (pairFrontierCountRev input.positions l k +
            if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 1 else 0))
          rw [if_pos hbne]
          simpa only [Nat.mul_add, Nat.add_assoc] using hlt
        have hpNext_eq : pCur + (if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 29 else 0) =
            pLvl + 29 * pairFrontierCountRev input.positions l (k + 1) := by
          dsimp only [pCur]; rw [pairFrontierCountRev_succ]
          change pLvl + 29 * pairFrontierCountRev input.positions l k +
            (if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 29 else 0) =
            pLvl + 29 * (pairFrontierCountRev input.positions l k +
            if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 1 else 0)
          split <;> omega
        have htNext_eq : tCur + (if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 1 else 0) =
            tLvl + pairFrontierCountRev input.positions l (k + 1) := by
          dsimp only [tCur]; rw [pairFrontierCountRev_succ]
          change tLvl + pairFrontierCountRev input.positions l k + _ =
            tLvl + (pairFrontierCountRev input.positions l k + _)
          split <;> omega
        refine hnode.weaken (le_refl _) (by change _ ≤ if capMark input.positions (l + 1) q then 1 else 0; rw [hcm_succ]) hcan_k ?_
        rintro sk1 calls2 tr2 ⟨hcalls2, hpc2, hfix2, h11_2, h13_2, hcur2, hx23_2, hmk_q, hval_q, hmeq_00, hout_q⟩
        rw [hpNext_eq, htNext_eq] at hcur2
        have hpres_step : ∀ a : Nat, a < 2 ^ 64 →
            a ≠ 8192 + heapIdx (l + 1) q →
            (∀ idx, (idx = 2 * q ∨ idx = 2 * q + 1) → capMark input.positions l idx = false →
              a < 16384 + 32 * heapIdx l idx ∨ 16384 + 32 * heapIdx l idx + 32 ≤ a) →
            (capMark input.positions (l + 1) q = true →
              a < 16384 + 32 * heapIdx (l + 1) q ∨ 16384 + 32 * heapIdx (l + 1) q + 32 ≤ a) →
            sk1.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a ha hne hunm_d hdst_d => by
          by_cases h00 : capMark input.positions l (2 * q) = false ∧ capMark input.positions l (2 * q + 1) = false
          · simp [MachineState.getByte, MachineState.getMem, hmeq_00 h00.1 h00.2]
          · have hcm_t : capMark input.positions (l + 1) q = true := by
              rw [hcm_succ]
              cases h1 : capMark input.positions l (2 * q) <;>
                cases h2 : capMark input.positions l (2 * q + 1) <;>
                  first | rfl | exact (h00 ⟨h1, h2⟩).elim
            refine hout_q a ha hne ?_ (hdst_d hcm_t)
            by_cases heq : capMark input.positions l (2 * q) = capMark input.positions l (2 * q + 1)
            · exact Or.inl heq
            · right
              cases h1 : capMark input.positions l (2 * q) with
              | false => simpa [h1] using hunm_d (2 * q) (Or.inl rfl) h1
              | true =>
                have h2 : capMark input.positions l (2 * q + 1) = false := by
                  cases h2' : capMark input.positions l (2 * q + 1)
                  · rfl
                  · exfalso; apply heq; rw [h1, h2']
                simpa [h1] using hunm_d (2 * q + 1) (Or.inr rfl) h2
        have hhigh2 : HighMemPreserved s0 sk1 := fun a ha hreg =>
          (hpres_step a ha (by omega)
            (fun idx hi _ => Or.inr (by have := heapIdx_cap_lt512 l idx hl1 (by omega) (by omega); omega))
            (fun _ => Or.inr (by omega))).trans (hhigh1 a ha hreg)
        have hpc2' : sk1.pc = if step = 7 ∧ k + 1 = m then pcWord 225 else pcWord 198 := by
          rw [hpc2]
          have hzero_iff : heapIdx (l + 1) q - 1 = 0 ↔ step = 7 ∧ k + 1 = m := by
            have hm1_iff : m = 1 ↔ step = 7 := by
              dsimp only [m, l]
              interval_cases step <;> decide
            omega
          by_cases hdone : step = 7 ∧ k + 1 = m
          · rw [if_pos hdone, if_pos (hzero_iff.mpr hdone)]
          · rw [if_neg hdone, if_neg (fun h => hdone (hzero_iff.mp h))]
        refine ⟨by rw [← hcm_succ] at hcalls2; change calls1 + calls2 ≤ pairMarkedNextCountRev input.positions l k +
            if capMark input.positions (l + 1) q then 1 else 0; omega,
          hpc2', hfix2, h11_2, h13_2, hcur2, hhigh2,
          by rw [hx23_2, hh_eq]; congr 1, ?_, ?_, ?_, ?_, ?_⟩
        · intro idx hidx
          have hlt512 := heapIdx_cap_lt512 l idx hl1 (by omega) hidx
          have hgt := heapIdx_lt_of_gt (l1 := l) (l2 := l + 1) (idx1 := idx) (idx2 := q) (by omega) (by omega) hq_lt
          exact (hpres_step _ (by omega) (by omega)
            (fun _ _ _ => Or.inl (by omega)) (fun _ => Or.inl (by omega))).trans (hmkL idx hidx)
        · intro j hj
          by_cases hlt : j < k
          · have hlt512 := heapIdx_cap_lt512 (l + 1) (m - 1 - j) (by omega) (by omega) (by omega)
            have hneq : heapIdx (l + 1) (m - 1 - j) ≠ heapIdx (l + 1) q := by unfold heapIdx; dsimp only [q]; omega
            exact (hpres_step _ (by omega) (by omega) (fun _ _ _ => Or.inl (by omega))
              (fun _ => Or.inl (by omega))).trans (hmkN j hlt)
          · have : j = k := by omega
            subst this; simpa only [q, hcm_succ] using hmk_q
        · intro h' hh'
          exact (hpres_step _ (by omega) (by omega) (fun _ _ _ => Or.inl (by omega))
            (fun _ => Or.inl (by omega))).trans (hmkLo h' (by omega))
        · intro a ha hmk_out hunm_out hdst_out
          have h1 := hpres_step a ha (hmk_out k (by omega))
            (fun idx hi hm => hunm_out k (by omega) idx hi hm)
            (fun hcm => hdst_out k (by omega) hcm)
          have h2 := hpres1 a ha (fun j hj => hmk_out j (by omega))
            (fun j hj idx hi hm => hunm_out j (by omega) idx hi hm)
            (fun j hj hcm => hdst_out j (by omega) hcm)
          exact h1.trans h2
        · intro j hj hcm'
          by_cases hlt : j < k
          · obtain ⟨hv, htr, hfrL, hfrR⟩ := hdone1 j hlt hcm'
            let q' := m - 1 - j
            have hq'_ne : q' ≠ q := by dsimp only [q', q]; omega
            have hpres_slot : ∀ idx, (idx = 2 * q' ∨ idx = 2 * q' + 1) →
                readBuffer sk1 (16384 + 32 * heapIdx l idx) 32 =
                readBuffer sk (16384 + 32 * heapIdx l idx) 32 := fun idx hi => by
              apply readBuffer_congr2; intro b hb
              have hlt512 := heapIdx_cap_lt512 l idx hl1 (by omega) (by omega)
              have hgt := heapIdx_lt_of_gt (l1 := l) (l2 := l + 1) (idx1 := idx) (idx2 := q) (by omega) (by omega) hq_lt
              refine hpres_step _ (by omega) (by omega) ?_ (fun _ => Or.inr (by omega))
              intro idx2 hi2 _
              have hne_i : idx ≠ idx2 := by omega
              unfold heapIdx; omega
            have hpres_dst : readBuffer sk1 (16384 + 32 * heapIdx (l + 1) q') 32 =
                readBuffer sk (16384 + 32 * heapIdx (l + 1) q') 32 := by
              apply readBuffer_congr2; intro b hb
              have hlt_q' := heapIdx_cap_lt512 (l + 1) q' (by omega) (by omega) (by omega)
              refine hpres_step _ (by omega) (by omega)
                (fun idx2 hi2 _ => by
                  have hgt := heapIdx_lt_of_gt (l1 := l) (l2 := l + 1) (idx1 := idx2) (idx2 := q') (by omega) (by omega) (by omega)
                  exact Or.inl (by omega))
                (fun _ => by unfold heapIdx; omega)
            dsimp only
            rw [show m - 1 - j = q' from rfl, hpres_slot (2 * q') (Or.inl rfl),
              hpres_slot (2 * q' + 1) (Or.inr rfl), hpres_dst]
            exact ⟨hv, htr.append_left, hfrL, hfrR⟩
          · have : j = k := by omega
            subst this
            change capMark input.positions (l + 1) q = true at hcm'
            rw [hcm_succ] at hcm'
            obtain ⟨hv, htr, hfrL, hfrR⟩ := hval_q hcm'
            exact ⟨hv, htr.append_right, hfrL, hfrR⟩)
  -- Specialize n = m and rebuild CapWalkInv (step + 1)
  have hfull := hind m (le_refl m)
  have hp_eq : pLvl + 29 * pairFrontierCountRev input.positions l m =
      pBase + 29 * capFrontierPrefix input.positions (step + 1) := by
    rw [pairFrontierCountRev_full input.positions l hl2, capFrontierPrefix_succ]
    dsimp only [pLvl, l, m]; omega
  have ht_eq : tLvl + pairFrontierCountRev input.positions l m =
      tBase + capFrontierPrefix input.positions (step + 1) := by
    rw [pairFrontierCountRev_full input.positions l hl2, capFrontierPrefix_succ]
    dsimp only [tLvl, l, m]; omega
  refine hfull.weaken (le_refl _) (pairMarkedNextCountRev_le_card input.positions l hl1 hl2)
    (by rw [hp_eq, ht_eq]; exact id) ?_
  rintro s' calls tr ⟨hcalls, hpc', hfix', h11', h13', hcur', hhigh', hx23', _, hmkN, hmkLo, hpres, hdone⟩
  rw [hp_eq, ht_eq] at hcur'
  refine ⟨hcalls.trans (pairMarkedNextCountRev_le_card input.positions l hl1 hl2), ?_⟩
  refine ⟨hfix', h11', h13', hcur', hhigh', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc']; by_cases h7 : step = 7 <;> simp [h7]
  · rw [hx23']; congr 1; dsimp only [m, l]; rw [show 16 + (step + 1) = 16 + step + 1 by omega]; omega
  · intro hlt1 idx hidx
    have hstep_eq : 16 + (step + 1) = l + 1 := by dsimp only [l]; omega
    have hidx_m : idx < m := by dsimp only [m]; rwa [← hstep_eq]
    have hj : m - 1 - idx < m := by omega
    have hsub : m - 1 - (m - 1 - idx) = idx := by omega
    rw [hstep_eq]
    have h := hmkN (m - 1 - idx) hj
    rwa [hsub] at h
  · intro hlt1 h' hh'
    exact hmkLo h' (by dsimp only [m, l] at *; rw [show 16 + (step + 1) = 16 + step + 1 by omega] at hh'; omega)
  · intro c hc hcm16
    rw [← hinv.val16_marked c hc hcm16]
    apply readBuffer_congr2; intro b hb
    refine hpres _ (by omega)
      (fun j hj => by have := heapIdx_cap_lt512 (l + 1) (m - 1 - j) (by omega) (by omega) (by omega); omega) ?_ ?_
    · intro j hj idx hi hunm
      by_cases hstep0 : step = 0
      · subst hstep0
        have hne : idx ≠ c := by intro heq; subst heq; rw [hcm16] at hunm; cases hunm
        change _ < 16384 + 32 * (256 + idx) ∨ 16384 + 32 * (256 + idx) + 32 ≤ _
        omega
      · have hgt : heapIdx l idx < 256 + c := by
          have := heapIdx_lt_of_gt (l1 := 16) (l2 := l) (idx1 := c) (idx2 := idx) (by omega) (by omega) (by omega)
          rwa [heapIdx_16] at this
        exact Or.inr (by omega)
    · intro j hj _
      have hgt : heapIdx (l + 1) (m - 1 - j) < 256 + c := by
        have := heapIdx_lt_of_gt (l1 := 16) (l2 := l + 1) (idx1 := c) (idx2 := m - 1 - j) (by omega) (by omega) (by omega)
        rwa [heapIdx_16] at this
      exact Or.inr (by omega)
  · intro d hd
    dsimp only
    intro q hq_d hcm_d
    by_cases hlt : d < step
    · obtain ⟨hv, htr, hfrL, hfrR⟩ := hinv.levels_done d hlt q hq_d hcm_d
      let ld := 16 + d
      have hpres_ge : ∀ l' idx', 16 ≤ l' → l' ≤ ld + 1 → idx' < levelSize l' →
          (l' = ld + 1 → capMark input.positions (ld + 1) idx' = true) →
          readBuffer s' (16384 + 32 * heapIdx l' idx') 32 =
          readBuffer s (16384 + 32 * heapIdx l' idx') 32 := fun l' idx' hge16 hle' hidx' hmk' => by
        apply readBuffer_congr2; intro b hb
        have hlt512 := heapIdx_cap_lt512 l' idx' hge16 (by omega) hidx'
        refine hpres _ (by omega)
          (fun j hj => by have := heapIdx_cap_lt512 (l + 1) (m - 1 - j) (by omega) (by omega) (by omega); omega) ?_ ?_
        · intro j hj idx2 hi2 hunm2
          by_cases heq_l : l' = l
          · have hld1 : l' = ld + 1 := by omega
            have hmk_t : capMark input.positions l idx' = true := by rw [← heq_l, hld1]; exact hmk' hld1
            have hne : idx' ≠ idx2 := by intro h; subst h; rw [hmk_t] at hunm2; cases hunm2
            rw [heq_l]; unfold heapIdx; omega
          · have hgt := heapIdx_lt_of_gt (l1 := l') (l2 := l) (idx1 := idx') (idx2 := idx2) (by omega) (by omega) (by omega)
            exact Or.inr (by omega)
        · intro j hj _
          have hgt := heapIdx_lt_of_gt (l1 := l') (l2 := l + 1) (idx1 := idx') (idx2 := m - 1 - j) (by omega) (by omega) (by omega)
          exact Or.inr (by omega)
      have hq_ld : q < levelSize (ld + 1) := hq_d
      have hL_eq := hpres_ge ld (2 * q) (by omega) (by omega) (by have := levelSize_double ld (by omega); omega) (by omega)
      have hR_eq := hpres_ge ld (2 * q + 1) (by omega) (by omega) (by have := levelSize_double ld (by omega); omega) (by omega)
      have hP_eq := hpres_ge (ld + 1) q (by omega) (by omega) hq_ld (fun _ => hcm_d)
      rw [hL_eq, hR_eq, hP_eq]
      exact ⟨hv, htr.append_left, hfrL, hfrR⟩
    · have hd_eq : d = step := by omega
      subst hd_eq
      have hqm : q < m := hq_d
      have hj : m - 1 - q < m := by omega
      have hq_inv : m - 1 - (m - 1 - q) = q := by omega
      have h := hdone (m - 1 - q) hj (by rwa [hq_inv])
      simp only [hq_inv] at h
      have hpAt_eq : pLvl + 29 * pairFrontierCountRev input.positions l (m - 1 - q) =
          498 * input.positions.card + 29 * (capFrontierPrefix input.positions d +
            pairFrontierCountRev input.positions l (m - 1 - q)) := by
        dsimp only [pLvl, pBase]; ring
      have htAt_eq : tLvl + pairFrontierCountRev input.positions l (m - 1 - q) =
          10 * input.positions.card + (capFrontierPrefix input.positions d +
            pairFrontierCountRev input.positions l (m - 1 - q)) := by
        dsimp only [tLvl, tBase]; omega
      rw [hpAt_eq, htAt_eq] at h
      exact ⟨h.1, h.2.1.append_right, h.2.2.1, h.2.2.2⟩

/-- Full bottom-up cap walk from `pc[197]` to `pc[225]`, `≤ 60000` steps, `≤ 8 * positions.card` calls. -/
theorem step_cap_walk (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0)
    (sPos : MachineState) (trPos : List PublicRow)
    (hpos : PosLoopInv h512 oracle input input.positions.card sPos trPos) :
    let pTotal := 498 * input.positions.card + 29 * capFrontierCount input.positions
    let tTotal := 10 * input.positions.card + capFrontierCount input.positions
    PhaseOutcome oracle sPos 60000 (8 * input.positions.card)
      (input.proof.length < pTotal + tailBytes tTotal)
      (fun s' calls tr =>
        calls ≤ 8 * input.positions.card ∧
        CapWalkInv h512 oracle input sPos 8 s' (trPos ++ tr)) := by
  intro pTotal tTotal
  have hpos_n : 0 < input.positions.card := Nat.pos_of_ne_zero hne
  have hpc197 : sPos.pc = pcWord 197 := by have := hpos.pc; rwa [if_pos rfl] at this
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  -- pc[197]: ADDI x23, x0, 255
  have hst197 := step_ordinary oracle sPos 197 (.ADDI .x23 .x0 255#12) (by decide) hpc197 rfl (by intro h; cases h) rfl
  let s1 := execInstrBr sPos (.ADDI .x23 .x0 255#12)
  have hpc1 : s1.pc = pcWord 198 := by simp only [s1, execInstrBr, MachineState.setPC, hpc197, pcWord_add_four]
  have hmem1 : s1.mem = sPos.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x23 → s1.getReg r = sPos.getReg r := fun r h23 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h23.symm
  have hx23_1 : s1.getReg .x23 = BitVec.ofNat 64 (levelSize 16 - 1) := by
    rw [levelSize_16]
    simp only [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hinv0 : CapWalkInv h512 oracle input sPos 0 s1 trPos := by
    refine ⟨hpos.fixed.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
      (hreg1 .x11 (by decide)).trans (hpos.x11 hpos_n),
      (hreg1 .x13 (by decide)).trans (hpos.x13 hpos_n),
      by simpa [capFrontierPrefix_zero] using hpos.cursor.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
      (hpos.inp.toHigh hcard_bd).trans_mem_eq hmem1,
      by simp [hpc1], hx23_1, ?_, ?_, ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    · intro _ idx hidx
      rw [levelSize_16] at hidx
      have h16 : s1.getByte (BitVec.ofNat 64 (8192 + (256 + idx))) =
          sPos.getByte (BitVec.ofNat 64 (8192 + (256 + idx))) := by
        simp only [MachineState.getByte, MachineState.getMem, hmem1]
      rw [Nat.add_zero, heapIdx_16, h16, hpos.mark16 idx hidx, posMarked16_card_eq_capMark]
    · intro _ h hh
      rw [levelSize_16] at hh
      simp only [MachineState.getByte, MachineState.getMem, hmem1]
      exact hpos.mark_lo_zero h hh
    · intro c _ _
      exact readBuffer_congr2 _ _ _ _ _ (fun _ _ => by simp [MachineState.getByte, MachineState.getMem, hmem1])
  -- Induction over step ≤ 8
  have hind : ∀ step ≤ 8,
      PhaseOutcome oracle s1
        (∑ d ∈ Finset.range step, 225 * levelSize (16 + d + 1))
        (step * input.positions.card)
        (input.proof.length <
          498 * input.positions.card + 29 * capFrontierPrefix input.positions step +
          tailBytes (10 * input.positions.card + capFrontierPrefix input.positions step))
        (fun s' calls tr =>
          calls ≤ step * input.positions.card ∧
          CapWalkInv h512 oracle input sPos step s' (trPos ++ tr)) := by
    intro step hstep
    induction step with
    | zero =>
      exact .continued s1 0 0 [] (Nat.zero_le _) (Nat.zero_le _) (StepsTo.refl oracle s1) ⟨Nat.zero_le _, by simpa using hinv0⟩
    | succ d ih =>
      have hrej_mono : input.proof.length <
            498 * input.positions.card + 29 * capFrontierPrefix input.positions d +
            tailBytes (10 * input.positions.card + capFrontierPrefix input.positions d) →
          input.proof.length <
            498 * input.positions.card + 29 * capFrontierPrefix input.positions (d + 1) +
            tailBytes (10 * input.positions.card + capFrontierPrefix input.positions (d + 1)) := by
        have hfm := capFrontierPrefix_mono input.positions (show d ≤ d + 1 by omega)
        have htm := tailBytes_mono (show 10 * input.positions.card + capFrontierPrefix input.positions d ≤
          10 * input.positions.card + capFrontierPrefix input.positions (d + 1) by omega)
        omega
      rw [Finset.sum_range_succ, show (d + 1) * input.positions.card = d * input.positions.card + input.positions.card by ring]
      refine (ih (by omega)).bind_dep hrej_mono (fun sd q1 tr1 ⟨hq1, hinv_d⟩ => by
        have hstep_d := step_cap_level h512 oracle input hvalid sPos d (by omega) sd (trPos ++ tr1) hinv_d
        refine hstep_d.weaken (le_refl _) (le_refl _) id ?_
        rintro s' q2 tr2 ⟨hq2, hinv_next⟩
        exact ⟨by omega, by simpa only [List.append_assoc] using hinv_next⟩)
  refine (hst197.prepend_pure (hind 8 (le_refl 8))).weaken
    (by have := cap_level_steps_sum; omega) (le_refl _)
    (by simpa only [capFrontierPrefix_8, pTotal, tTotal] using id)
    (fun _ _ _ h => h)

/-! #### Epilogue (`pc[225..245]`) -/

/-- Final epilogue: check `pLo == pHi` (`x25 == x31`), `cBuf == 0` (`x3 == 0`), and
4-dword root equality (`val[1]` at `16416` vs `input.commitment` at `4294971392`), `≤ 25` steps. -/
theorem step_epilogue (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (pTotal tTotal : Nat) (s : MachineState) (hpc : s.pc = pcWord 225)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pTotal tTotal s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s) :
    let s0 := submission.initialState .check input
    HaltsWith oracle s 25 0
      (if pTotal + tailBytes tTotal == input.proof.length &&
          tailBuf s0 input.proof.length tTotal == 0 &&
          readBuffer s 16416 32 == (input.commitment : BitVec (8 * 32))
       then .success else .failure) [] := by
  intro s0
  have hplen_bd : input.proof.length ≤ 8480886496 := hvalid
  have hle : pTotal + tailBytes tTotal ≤ input.proof.length := hcur.le
  have htb_lt := tailBuf_lt256 s0 input.proof.length tTotal
  -- pc[225]: BNE x25, x31, pc[243]
  have hst225 := step_ordinary oracle s 225 (.BNE .x25 .x31 72#13) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.BNE .x25 .x31 72#13)
  have hne1 : (s.getReg .x25 != s.getReg .x31) = decide (pTotal + tailBytes tTotal ≠ input.proof.length) := by
    rw [hcur.x25, hcur.x31, bv64_bne_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hlen_eq : pTotal + tailBytes tTotal = input.proof.length
  · have hbeq_len : (pTotal + tailBytes tTotal == input.proof.length) = true := beq_iff_eq.mpr hlen_eq
    have hpc1 : s1.pc = pcWord 226 := by
      simp only [s1, execInstrBr, hne1, hlen_eq, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc, pcWord_add_four]
    have hmem1 : s1.mem = s.mem := by
      simp only [s1, execInstrBr, hne1, hlen_eq, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, mem_setPC]
    have hreg1 : ∀ r, s1.getReg r = s.getReg r := fun r => by
      simp only [s1, execInstrBr, hne1, hlen_eq, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
    -- pc[226]: BNE x3, x0, pc[243]
    have hst226 := step_ordinary oracle s1 226 (.BNE .x3 .x0 68#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
    let s2 := execInstrBr s1 (.BNE .x3 .x0 68#13)
    have hne2 : (s1.getReg .x3 != s1.getReg .x0) = decide (tailBuf s0 input.proof.length tTotal ≠ 0) := by
      rw [hreg1 .x3, hcur.x3, getReg_x0]
      exact bv64_bne_eq _ 0 (Nat.lt_trans htb_lt (by omega)) (by omega)
    by_cases hbuf0 : tailBuf s0 input.proof.length tTotal = 0
    · have hbeq_buf : (tailBuf s0 input.proof.length tTotal == 0) = true := beq_iff_eq.mpr hbuf0
      have hpc2 : s2.pc = pcWord 227 := by
        simp only [s2, execInstrBr, hne2, hbuf0, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc1, pcWord_add_four]
      have hmem2 : s2.mem = s.mem := by
        simpa only [s2, execInstrBr, hne2, hbuf0, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, mem_setPC] using hmem1
      have hreg2 : ∀ r, s2.getReg r = s.getReg r := fun r => by
        simpa only [s2, execInstrBr, hne2, hbuf0, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC] using hreg1 r
      -- pc[227]: ADDI x10, x19, 32 -> x10 = 16416
      have hst227 := step_ordinary oracle s2 227 (.ADDI .x10 .x19 32#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
      let s3 := execInstrBr s2 (.ADDI .x10 .x19 32#12)
      have hpc3 : s3.pc = pcWord 228 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
      have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
      have hx10_3 : s3.getReg .x10 = BitVec.ofNat 64 16416 := by
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x19, hfix.x19, se12_32]; decide
      have hx26_3 : s3.getReg .x26 = BitVec.ofNat 64 4294971392 := by
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x26), hreg2 .x26, hfix.x26]
      have hcmp := step_compare4 oracle 228 .x10 .x26 s3 16416 4294971392
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl, rfl⟩) hpc3
        hx10_3 hx26_3 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      have hrbA : readBuffer s3 16416 32 = readBuffer s 16416 32 :=
        (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)
      have hrbB : readBuffer s3 4294971392 32 = input.commitment := by
        rw [(MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega),
          hhigh.readBuffer_eq (by omega) (Or.inl (by omega)), check_initial_commitment]
      have hpre3 : StepsTo oracle s s3 3 0 [] :=
        ((hst225.trans hst226).trans hst227).eq_of rfl (by decide) (by decide) (by simp)
      cases hcmp with
      | rejected k q tr hr hk hq hh =>
        rw [hrbA, hrbB] at hr
        have hbeq_f : (readBuffer s 16416 32 == (input.commitment : BitVec (8 * 32))) = false :=
          beq_eq_false_iff_ne.mpr hr
        simp only [hbeq_len, hbeq_buf, hbeq_f, Bool.and_false, Bool.false_eq_true, ite_false]
        have hq0 : q = 0 := by omega
        subst hq0
        have htr0 : tr = [] := by
          have := hh.2 0
          have hnil := detExec_trace_nil_of_zero_calls oracle (submission.image .check) (k + 0) s3 (by rw [this.2.1])
          exact this.2.2.symm.trans hnil
        subst htr0
        exact (by simpa using hpre3.halt hh : HaltsWith oracle s (3 + k) 0 .failure []).mono (by omega)
      | continued s4 k q tr hk hq hs4 hp4 =>
        obtain ⟨rfl, rfl, heq_dig, hpc4, _, _⟩ := hp4
        rw [hrbA, hrbB] at heq_dig
        have hbeq_t : (readBuffer s 16416 32 == (input.commitment : BitVec (8 * 32))) = true :=
          beq_iff_eq.mpr heq_dig
        simp only [hbeq_len, hbeq_buf, hbeq_t, Bool.and_self, ite_true]
        exact (by simpa [Nat.add_assoc] using (hpre3.trans hs4).halt (halt_accept oracle s4 hpc4) :
          HaltsWith oracle s (3 + k + 3) 0 .success []).mono (by omega)
    · have hbeq_buf : (tailBuf s0 input.proof.length tTotal == 0) = false := beq_eq_false_iff_ne.mpr hbuf0
      simp only [hbeq_len, hbeq_buf, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
      have hpc2 : s2.pc = pcWord 243 := by
        simp only [s2, execInstrBr, hne2, hbuf0, ne_eq, not_false_eq_true, decide_true,
          ite_true, MachineState.setPC, hpc1]
        exact pc_226_reject
      exact (by simpa using (hst225.trans hst226).halt (halt_reject oracle s2 hpc2) :
        HaltsWith oracle s 5 0 .failure []).mono (by decide)
  · have hbeq_len : (pTotal + tailBytes tTotal == input.proof.length) = false := beq_eq_false_iff_ne.mpr hlen_eq
    simp only [hbeq_len, Bool.false_and, Bool.false_eq_true, ite_false]
    have hpc1 : s1.pc = pcWord 243 := by
      simp only [s1, execInstrBr, hne1, hlen_eq, ne_eq, not_false_eq_true, decide_true,
        ite_true, MachineState.setPC, hpc]
      exact pc_225_reject
    exact (by simpa using hst225.halt (halt_reject oracle s1 hpc1) :
      HaltsWith oracle s 4 0 .failure []).mono (by decide)

end CommitGolfCandidate
