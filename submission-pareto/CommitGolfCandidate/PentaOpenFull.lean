import CommitGolfCandidate.PentaOpenHeader
import CommitGolfCandidate.QuadOpeningProofBytes

/-! Hybrid penta3 + binary counter-mode opener end to end:
- empty opening (`p.card = 0`): 6 cycles, 0 oracle calls, 0 bytes.
- non-empty opening: 29-cycle header -> salt-materializing loop (`≤ 20*k + 1 + 13*k` cycles, `k` calls)
  -> jump and setup, records (346 cycles each), the level-9 table copy and the exit
  (`346*k + 1910` cycles, no calls, `816*k + 7168` bytes).
For `k = 128`: `≤ 29 + 4225 + 57435 = 61,689` cycles, `128` calls, `98,368` bytes. -/
namespace TwoPermutationPrototype.PentaOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open QOpening (OpeningLayout trapdoorBase proofBase indicesBase nonceBase trapdoorSalt)
open QuadOpening (OpeningABI OpenPhysical EntryAt scheduledCycles proofLength proofFromTrapdoor
  empty_physical body_from_record_at opening_success read_opening_proof opening_proof_size)
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem record_at_end (sub : Submission) (layout : OpeningLayout sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (p0 : 0 < p.card) (r : Ready sub td p k s p.card) :
    EntryAt (sub.initialState .opening (virtualTd sub s, p)) s p := by
  have inv := virtual_inv sub layout td p s (by
    intro a lo hi alg
    let w := a / 8
    have ea : a = 8 * w := by dsimp [w]; omega
    have wlo : 796918788 ≤ w := by
      dsimp [trapdoorBase, QOpening.trapdoorBytes, LENGTH, LOG_LENGTH] at lo; omega
    have wlim : w < 2^33 := by
      have lim : proofBase < 2^36 := by decide
      omega
    have h := r.frame w wlim (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr wlo)
    rw [ea]; exact h)
  have start : s.pc = BitVec.ofNat 64 (4096 + 4 * 11) := by simpa [passPC, address] using r.pc
  refine ⟨start,
    by simpa using r.indices, r.heap, by simpa using r.count, r.five,
    r.begin, by simpa using r.dest, r.salts, r.groupWidth, r.table, inv⟩

/-- Every group slot in `virtualTd` matches the original trapdoor (the prefix only writes salts). -/
theorem kept_slot (sub : Submission) (layout : OpeningLayout sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready sub td p k s p.card) (level g t : Nat) (hl : level < PENTA_LEVELS) (hg : g < pentaCount (level + 1))
    (ht : t < 5) :
    pentaTrapdoorSlot (virtualTd sub s) level g t = pentaTrapdoorSlot td level g t := by
  have below := Quad.Commit.group_below_salts level g (by unfold PENTA_LEVELS at hl; omega) hg 0
  have low := Quad.Commit.trapdoor_below_levels level g (by unfold PENTA_LEVELS at hl; omega)
  have baseW := Quad.Commit.penta_base_word level (by unfold PENTA_LEVELS at hl; omega)
  have offBound : pentaGroupSlotOffset level g t + 32 ≤ QOpening.trapdoorBytes := by
    unfold Quad.Commit.saltWord Quad.Commit.pentaGroupWord at below; unfold QOpening.trapdoorBytes pentaGroupSlotOffset
    omega
  unfold pentaTrapdoorSlot
  rw [virtual_slice sub s (pentaGroupSlotOffset level g t) 32 (by rwa [layout.trapdoorSize]),
    ← QOpening.input_trapdoor_slice sub layout td p (pentaGroupSlotOffset level g t) 32 offBound]
  apply QOpening.copied_buffer (sub.initialState .opening (td, p)) s
    (trapdoorBase + pentaGroupSlotOffset level g t) (trapdoorBase + pentaGroupSlotOffset level g t) 4
    (by change (4294971424 + pentaGroupSlotOffset level g t) % 8 = 0; unfold pentaGroupSlotOffset
        unfold Quad.Commit.pentaGroupWord at low; omega)
    (by change (4294971424 + pentaGroupSlotOffset level g t) % 8 = 0; unfold pentaGroupSlotOffset
        unfold Quad.Commit.pentaGroupWord at low; omega) (by decide)
  intro i hi
  let w := Quad.Commit.pentaGroupWord level g + 5 + 4*t + i
  have ea : trapdoorBase + pentaGroupSlotOffset level g t + 8 * i = 8 * w := by
    dsimp [w]; change 4294971424 + pentaGroupSlotOffset level g t + 8 * i = _
    unfold Quad.Commit.pentaGroupWord pentaGroupSlotOffset; omega
  have lower : 217 ≤ w := by dsimp [w]; unfold Quad.Commit.pentaGroupWord at *; omega
  have upper : w < 763364356 := by dsimp [w]; unfold Quad.Commit.saltWord at below; omega
  rw [ea]
  exact r.frame w (by omega) (Or.inr (by omega)) (Or.inr lower) (Or.inl upper)

theorem selected_salt (o : Oracle) (sub : Submission) (layout : OpeningLayout sub)
    (k : BitVec 192) (p : Positions) (s : MachineState)
    (seen : Seen o k p s p.card) (idx : Index) (member : idx ∈ p) :
    trapdoorSalt (s := sub) (virtualTd sub s) idx = salts o.permutation k idx := by
  have iBound : idx.val < 16777216 := idx.isLt
  have inList : idx ∈ p.sort (· ≤ ·) := by simpa using member
  obtain ⟨j, hj, hx⟩ := List.mem_iff_getElem.mp inList
  have size : j < p.card := by simpa using hj
  have who : pos p j = idx := (pos_present p j size).trans hx
  unfold trapdoorSalt
  rw [virtual_slice sub s _ 16 (by rw [layout.trapdoorSize]; change 1811943424 + 16 * idx.val + 16 ≤ 2080378880; omega)]
  rw [show trapdoorBase + (0x6C001000 + 16 * idx.val) = 8 * (763364356 + 2 * idx.val) by
    unfold trapdoorBase LENGTH LOG_LENGTH; omega]
  apply aligned_buffer_eq _ _ 16 (by decide)
  intro b hb
  have h := seen j size (⟨b, hb⟩ : Fin 2)
  dsimp only at h; rw [who] at h
  have addr : destAt idx + BitVec.ofNat 64 (8 * b) = wordAddress (763364356 + 2 * idx.val + b) := by
    unfold destAt wordAddress; rw [← BitVec.ofNat_add]; congr 1 <;> omega
  rw [addr] at h; exact h

private def leftOver (sub : Submission) (p : Positions) :=
  sub.steps .opening - (29 + passSteps p p.card 0 + (283 * p.card + 1910))

private def recordsFuel (sub : Submission) (p : Positions) :=
  283 * p.card + 1910 + leftOver sub p

private theorem allowance (sub : Submission) (abi : OpeningABI sub) (p : Positions) :
    sub.steps .opening = 29 + (passSteps p p.card 0 + recordsFuel sub p) := by
  have card : p.card ≤ 16777216 := by change p.card ≤ LENGTH; simpa [Index] using Finset.card_le_univ p
  have b := pass_steps_bound p p.card 0 (by omega)
  have hf := abi.fuel
  unfold recordsFuel leftOver
  omega

private theorem run_from (s : Submission) (td : BitVec (8 * s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening = im) (hf : s.steps .opening = n) :
    s.run .opening (td, p) = execute im n (s.initialState .opening (td, p)) true := by
  unfold Submission.run
  simp only [hi, hf, ite_true]; rfl

attribute [local irreducible] execute passTrace passSteps header scheduledCycles fixedPass

theorem machine_run (sub : Submission) (abi : OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (nz : 0 < p.card) :
    let initial := sub.initialState .opening (td, p)
    sub.run .opening (td, p) = (do
      let s ← passTrace p p.card 0 (header initial)
      let z ← execute openingImage (recordsFuel sub p) s true
      return z.charge (29 + passSteps p p.card 0 + 13 * p.card) p.card) := by
  let init := sub.initialState .opening (td, p)
  rw [run_from sub td p openingImage _ abi.image (allowance sub abi p),
    header_run sub abi td p nz,
    pass_run sub abi.toOpeningLayout td p (keyOf td) (header init) p.card 0 _ (header_valid sub abi td p nz).2 (by omega)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro s; apply bind_congr; intro z; apply congrArg Pure.pure; cases z
  simp [Execution.charge, Nat.add_assoc]

theorem body_result (sub : Submission) (abi : OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (nz : 0 < p.card)
    (s : MachineState) (r : Ready sub td p (keyOf td) s p.card) :
    ∃ final : MachineState,
      execute openingImage (recordsFuel sub p) s true = pure ⟨.success, final, 346*p.card+1910, 0⟩ ∧
      OpenPhysical sub (virtualTd sub s) p ⟨.success, final, scheduledCycles p, 0⟩ :=
  body_from_record_at sub abi (virtualTd sub s) p s (Nat.ne_of_gt nz)
    (record_at_end sub abi.toOpeningLayout td p _ s nz r) (leftOver sub p)

theorem all_resources (sub : Submission) (abi : OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z ∈ support (sub.run .opening (td, p))) :
    z.exit = .success ∧ sub.openingSucceeded z = true ∧
      (p.card = BATCH → z.cycles ≤ 50452 ∧ (sub.readProof z).length ≤ 111616) ∧
      z.oracleCalls ≤ 100 * p.card := by
  by_cases empty : p.card = 0
  · obtain ⟨out, run, phys⟩ := empty_physical sub abi td p empty
    rw [run, support_pure, Set.mem_singleton_iff] at hit; subst z
    exact ⟨phys.success, opening_success sub abi td p out phys,
      fun h => False.elim (by change p.card = 128 at h; omega), by rw [phys.noCalls]; omega⟩
  · have nz : 0 < p.card := by omega
    rw [machine_run sub abi td p nz] at hit
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
    obtain ⟨s, pass, out, ran, rfl⟩ := hit
    have rd := pass_post sub abi.toOpeningLayout td p _ _ _ p.card 0 (header_valid sub abi td p nz).2 (by omega) pass
    obtain ⟨final, body, phys⟩ := body_result sub abi td p nz s (by simpa using rd)
    rw [body, support_pure, Set.mem_singleton_iff] at ran
    subst ran
    have len := phys.length
    let charged : Execution := Execution.charge ⟨.success, final, 346 * p.card + 1910, 0⟩
      (29 + passSteps p p.card 0 + 13 * p.card) p.card
    have ok : sub.openingSucceeded charged = true :=
      QuadOpening.opening_success_of sub abi p charged rfl len
    refine ⟨rfl, ok, ?_, by simp only [charged, Execution.charge]; omega⟩
    intro batch
    have cap := pass_steps_bound p p.card 0 (by omega)
    have k : p.card = 128 := batch
    refine ⟨by simp only [charged, Execution.charge]; omega, ?_⟩
    have lenEq : (sub.readProof charged).length = (final.getReg .x11).toNat := by
      unfold Submission.readProof
      rw [ok]
      simp only [ite_true, List.length_map, List.length_range, charged, Execution.charge]
    rw [lenEq, len, proofLength, capLength, k]
    decide

noncomputable def virtualFor (o : Oracle) (sub : Submission) (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) :=
  if p.card = 0 then td else virtualTd sub (fixedPass o p (keyOf td) p.card 0 (header (sub.initialState .opening (td, p))))

theorem fixed_open (sub : Submission) (abi : OpeningABI sub) (o : Oracle)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) :
    fixedOracleRun o (sub.scheme.opening td p) =
      Pure.pure (proofFromTrapdoor (s := sub) (virtualFor o sub td p) p) := by
  change fixedOracleRun o (sub.readProof <$> sub.run .opening (td, p)) = _
  rw [fixed_oracle_run_map]
  by_cases empty : p.card = 0
  · obtain ⟨z, run, phys⟩ := empty_physical sub abi td p empty
    rw [run, fixed_oracle_run_pure, map_pure, virtualFor, ite_eq_left empty]
    exact congrArg Pure.pure (read_opening_proof sub abi td p z phys)
  · have nz : 0 < p.card := by omega
    let begin := header (sub.initialState .opening (td, p))
    let st := fixedPass o p (keyOf td) p.card 0 begin
    have start := (header_valid sub abi td p nz).2
    have fixed := pass_fixed o sub abi.toOpeningLayout td p (keyOf td) begin 0 p.card (by omega) start
    have seen : st ∈ support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st, p.card)
      change (_, _) ∈ support (o.run (passTrace p p.card 0 begin)); rw [fixed]; simp [st]
    have rd := pass_post sub abi.toOpeningLayout td p (keyOf td) begin st p.card 0 start (by omega) seen
    obtain ⟨fin, body, phys⟩ := body_result sub abi td p nz st (by simpa using rd)
    rw [machine_run sub abi td p nz, fixed_oracle_run_bind]
    have proj : fixedOracleRun o (passTrace p p.card 0 begin) = Pure.pure st := by
      unfold fixedOracleRun; rw [fixed]; rfl
    rw [proj, pure_bind, fixed_oracle_run_bind, body, fixed_oracle_run_pure, pure_bind,
      fixed_oracle_run_pure, map_pure]
    rw [virtualFor, ite_eq_right empty]
    have readEq : sub.readProof (Execution.charge ⟨.success, fin, 346 * p.card + 1910, 0⟩
          (29 + passSteps p p.card 0 + 13 * p.card) p.card) =
        sub.readProof ⟨.success, fin, scheduledCycles p, 0⟩ := rfl
    rw [readEq]
    exact congrArg Pure.pure
      (read_opening_proof sub abi (virtualTd sub st) p ⟨.success, fin, scheduledCycles p, 0⟩ phys)

/-- For any trapdoor produced by commit (storing `key` and honest penta nodes), `proofFromTrapdoor`
of `virtualFor` equals the honest cap proof under `CounterSalt.salts o.permutation key`. -/
theorem virtual_proof_eq (sub : Submission) (abi : OpeningABI sub) (o : Oracle)
    (msg : Message) (k : BitVec 192) (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions)
    (hKey : keyOf td = k)
    (hSlots : ∀ level g (t : Fin 5), level < PENTA_LEVELS → g < pentaCount (level + 1) →
      pentaTrapdoorSlot td level g t.val =
        pentaGroup (pentaFunction o.permutation) (quadPublicLeaves o msg (salts o.permutation k)) level g t) :
    proofFromTrapdoor (s := sub) (virtualFor o sub td p) p =
      (pentaHonestView capTranscriptBuilder (BiPermutation.equiv Block o.permutation)
        msg p (salts o.permutation k)).2 := by
  by_cases empty : p.card = 0
  · have pe : p = ∅ := Finset.card_eq_zero.mp empty
    subst pe
    simp [proofFromTrapdoor, pentaHonestView, capTranscriptBuilder]
  · have nz : 0 < p.card := by omega
    let begin := header (sub.initialState .opening (td, p))
    let st := fixedPass o p (keyOf td) p.card 0 begin
    have start := (header_valid sub abi td p nz).2
    have fixed := pass_fixed o sub abi.toOpeningLayout td p (keyOf td) begin 0 p.card (by omega) start
    have hitSt : st ∈ support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st, p.card)
      change (_, _) ∈ support (o.run (passTrace p p.card 0 begin)); rw [fixed]; simp [st]
    have rd := pass_post sub abi.toOpeningLayout td p (keyOf td) begin st p.card 0 start (by omega) hitSt
    have seen0 : Seen o (keyOf td) p begin 0 := fun a ha => absurd ha (Nat.not_lt_zero a)
    have seenEnd : Seen o (keyOf td) p st p.card := by
      simpa only [Nat.zero_add] using seen_pass o sub abi.toOpeningLayout td p (keyOf td) begin 0 p.card (by omega) start seen0
    rw [virtualFor, ite_eq_right empty]
    apply QuadOpening.proof_from_trapdoor_matches_opened sub (virtualTd sub st) p
      (pentaFunction o.permutation) (quadPublicLeaves o msg (salts o.permutation k)) (salts o.permutation k)
    · intro level g t hl hg
      exact (kept_slot sub abi.toOpeningLayout td p (keyOf td) st (by simpa using rd) level g t.val hl hg t.isLt).trans
        (hSlots level g t hl hg)
    · intro i hi
      rw [← hKey]
      exact selected_salt o sub abi.toOpeningLayout (keyOf td) p st seenEnd i hi

end TwoPermutationPrototype.PentaOpening
