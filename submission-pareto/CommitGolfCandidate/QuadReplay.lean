import CommitGolfCandidate.TwoPermutationPinnedStoredLeaf
import CommitGolfCandidate.TwoPermutationPinnedPeerMargin
import CommitGolfCandidate.K3GQModel

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling Finset
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2050
set_option maxHeartbeats 1100000

/-- The quartet call of group `g`: the record window `0^72 ‖ d0 d1 d2 d3`, truncated to the
parity node (`quartetNode g`: reply bytes `168..200` for even `g`, `0..32` for odd `g`). -/
def quadNodeCall (group : Nat) : SingleCall S3State (BitVec 1024) (BitVec 256) where
  enc := quartetEncode
  enc_inj := quartet_encode_injective
  trunc := quartetNode group

/-- Two different payloads with one quartet node in some group. -/
def QuadWitness (rows : List PublicRow) : Prop :=
  ∃ (group : Nat) (x y : BitVec 1024), x ≠ y ∧ ∃ dx dy : Block,
    PublicRow.permutation (quartetEncode x) dx ∈ rows ∧
    PublicRow.permutation (quartetEncode y) dy ∈ rows ∧
    quartetNode group dx = quartetNode group dy

/-- A quartet collision under the node truncation of group `g`. -/
def QuadWitnessAt (group : Nat) (rows : List PublicRow) : Prop :=
  ∃ x y : BitVec 1024, x ≠ y ∧ ∃ dx dy : Block,
    PublicRow.permutation (quartetEncode x) dx ∈ rows ∧
    PublicRow.permutation (quartetEncode y) dy ∈ rows ∧
    quartetNode group dx = quartetNode group dy

/-- Only the parity of the group matters: a witness is a collision under one of two truncations. -/
theorem quad_witness_split {rows : List PublicRow} (hit : QuadWitness rows) :
    QuadWitnessAt 0 rows ∨ QuadWitnessAt 1 rows := by
  obtain ⟨group, x, y, distinct, dx, dy, rx, ry, same⟩ := hit
  rw [← quartet_node_parity group dx, ← quartet_node_parity group dy] at same
  rcases Nat.mod_two_eq_zero_or_one group with even | odd
  · rw [even] at same
    exact Or.inl ⟨x, y, distinct, dx, dy, rx, ry, same⟩
  · rw [odd] at same
    exact Or.inr ⟨x, y, distinct, dx, dy, rx, ry, same⟩

theorem QuadWitnessAt.witness {group : Nat} {rows : List PublicRow} (hit : QuadWitnessAt group rows) :
    QuadWitness rows := by
  obtain ⟨x, y, distinct, dx, dy, rx, ry, same⟩ := hit
  exact ⟨group, x, y, distinct, dx, dy, rx, ry, same⟩

theorem quad_witness_bad {group : Nat} {rows : List PublicRow} {trace : Trace PermState}
    (stored : PinnedRowsStored rows trace) (hit : QuadWitnessAt group rows) :
    ¬ (quadNodeCall group).badSpec.Good trace := by
  obtain ⟨x,y,distinct,dx,dy,rx,ry,same⟩ := hit
  obtain ⟨a, ha, ax, ad⟩ := stored _ _ rx
  obtain ⟨b, hb, bx, bd⟩ := stored _ _ ry
  apply ((quadNodeCall group).not_good_iff trace).2
  exact (quadNodeCall group).collision_imp_bad distinct
    ⟨a, ha, ax, congrArg (quadNodeCall group).trunc ad⟩
    ⟨b, hb, bx, (congrArg (quadNodeCall group).trunc bd).trans same.symm⟩

private theorem high_node_pin (s : Block) : s.extractLsb' 1344 256 = s3PinCall.pin s := by
  apply BitVec.eq_of_toNat_eq
  change (s.extractLsb' 1344 256).toNat = (BitVec.ofNat 256 (s.toNat / 2 ^ 1344)).toNat
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]

private theorem low_node_trunc (s : Block) : s.extractLsb' 0 256 = s3PinCall.trunc s := by
  apply BitVec.eq_of_toNat_eq
  change (s.extractLsb' 0 256).toNat = (BitVec.ofNat 256 s.toNat).toNat
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  simp

/-- Every quartet node value has at most `2^1344` preimage states, for either parity. -/
theorem quad_node_fiber (group : Nat) (d : BitVec 256) :
    (univ.filter fun s : S3State => (quadNodeCall group).trunc s = d).card ≤ 2^1344 := by
  by_cases even : group % 2 = 0
  · refine (Finset.card_le_card ?_).trans (s3_pin_fiber d)
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [← hs]
    change s3PinCall.pin s = quartetNode group s
    simp only [quartetNode, even, ite_true]
    exact (high_node_pin s).symm
  · refine (Finset.card_le_card ?_).trans (s3_trunc_fiber d)
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [← hs]
    change s3PinCall.trunc s = quartetNode group s
    simp only [quartetNode, even, ite_false]
    exact (low_node_trunc s).symm

theorem quad_bad_trace_bound {α : Type} (group : Nat) (st : Strat PermState α) (calls : Nat)
    (fits : calls < Fintype.card S3State) :
    st.prob PState.init (fun _ finish => ¬ (quadNodeCall group).badSpec.Good finish.trace ∧ finish.count ≤ calls) ≤
      unionBound (Fintype.card S3State) (2^1344) (2^1024) calls := by
  apply prob_not_good_le (quadNodeCall group).badSpec _ _ calls fits
  · intro x old
    exact ⟨univ.filter fun s => (quadNodeCall group).trunc s = (quadNodeCall group).trunc old.out,
      quad_node_fiber group _, fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.2⟩⟩
  · intro x
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [SingleCall.badSpec] at hy⟩
  · intro y old
    exact ⟨∅, Nat.zero_le _, fun x hx => by simp [SingleCall.badSpec] at hx⟩
  · intro y
    refine ⟨univ.image (quadNodeCall group).enc, Finset.card_image_le.trans ?_, fun x hx => ?_⟩
    · rw [Finset.card_univ, s3_card_bitvec]
    · obtain ⟨value, eq⟩ := hx.2
      exact Finset.mem_image.2 ⟨value, Finset.mem_univ _, eq⟩

/-- Margin of a union bound on the full 1600-bit state at `q/2^124` (unary count up to `2^1400`). -/
theorem replay_extra_margin (q calls k v : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (kBound : k ≤ 2^1346) (vBound : v ≤ 2^1400) :
    unionBound (2^1600) k v calls ≤ (q : ℝ)/2^124 := by
  have one : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have limit : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have replayLimit : (calls : ℝ) ≤ (q : ℝ) + 2^31 := by exact_mod_cast replayed
  have nonneg : (0 : ℝ) ≤ calls := by positivity
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have K : (k : ℝ) ≤ 2^1346 := by exact_mod_cast kBound
  have V : (v : ℝ) ≤ 2^1400 := by exact_mod_cast vBound
  have callUpper : (calls : ℝ) ≤ 2^121 := by
    linarith [show (2 : ℝ)^120 + 2^31 ≤ 2^121 by norm_num]
  have denom : (2 : ℝ)^1599 ≤ 2^1600 - (calls : ℝ) := by
    linarith [show (2 : ℝ)^1599 + 2^121 ≤ 2^1600 by norm_num]
  have denomPos : 0 < (2 : ℝ)^1600 - calls :=
    lt_of_lt_of_le (by positivity : 0 < (2 : ℝ)^1599) denom
  have squareBound : (calls : ℝ)^2 ≤ (q : ℝ)*2^122 := by
    let extra : ℝ := 2^31
    have leSum : (calls : ℝ) ≤ q + extra := replayLimit
    have sq := mul_nonneg (sub_nonneg.mpr leSum) (by positivity : 0 ≤ (q : ℝ) + extra + calls)
    have qsq := mul_le_mul_of_nonneg_right limit qNonneg
    have esq : 2*extra^2 ≤ 2^65 := by norm_num [extra]
    have nq := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^65)
    have slack : (2 : ℝ)^121 + 2^65 ≤ 2^122 := by norm_num
    have pad := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith [sq_nonneg ((q : ℝ) - extra)]
  have linearBound : (calls : ℝ) ≤ (q : ℝ)*2^32 := by
    have scale := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^31)
    have slack : (1 : ℝ)+2^31 ≤ 2^32 := by norm_num
    have envelope := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith
  have pair : ((calls : ℝ) * ((calls : ℝ)-1)/2) * (k : ℝ) ≤ (calls : ℝ)^2 * 2^1346 := by
    have factor : (calls : ℝ) * ((calls : ℝ)-1)/2 ≤ (calls : ℝ)^2 := by
      nlinarith [sq_nonneg (calls : ℝ)]
    exact (mul_le_mul_of_nonneg_right factor (by positivity : 0 ≤ (k : ℝ))).trans
      (mul_le_mul_of_nonneg_left K (by positivity))
  have tail : (calls : ℝ) * (v : ℝ) ≤ (calls : ℝ) * 2^1400 :=
    mul_le_mul_of_nonneg_left V nonneg
  have pairBound := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ 2^1346)
  have tailBound := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^1400)
  have lower := mul_le_mul_of_nonneg_left denom (by positivity : (0 : ℝ) ≤ (q : ℝ)/2^124)
  have unified : (2 : ℝ)^122*2^1346 + 2^32*2^1400 ≤ 2^1599/2^124 := by norm_num
  have scale := mul_le_mul_of_nonneg_left unified qNonneg
  simp only [unionBound, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_iff₀ denomPos).2
  nlinarith

private theorem fixed_compression_replayed_event {α : Type} (compress : Compression) (program : OracleComp World α)
    (witness : List PublicRow → Prop) (bad : BadSpec PermState) (q calls : Nat)
    (bounded : PublicQueryBound (recordRows program) calls)
    (extract : ∀ trace rows, PinnedRowsStored rows trace → witness rows → ¬ bad.Good trace)
    (prob : (toStrat compress (recordRows program)).prob PState.init
      (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) ≤ (q : ℝ)/2^124) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      witness result.2] ≤ (q : ENNReal)/2^124 := by
  classical
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have records := pinned_recorded_table compress program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => witness result.2) ≤
      st.prob PState.init (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨extract finish.trace result.2 facts.1.2 hit, by simpa [PState.init] using facts.2.2⟩
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal (evidence.trans prob)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

theorem fixed_compression_quad_bound_at {α : Type} (group : Nat) (compress : Compression)
    (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      QuadWitnessAt group result.2] ≤ (q : ENNReal)/2^124 := by
  refine fixed_compression_replayed_event compress program (QuadWitnessAt group) (quadNodeCall group).badSpec
    q calls bounded (fun _ _ => quad_witness_bad) ?_
  have fits : calls < Fintype.card S3State := by rw [s3_card_state]; omega
  refine (quad_bad_trace_bound group (toStrat compress (recordRows program)) calls fits).trans ?_
  rw [s3_card_state]
  exact replay_extra_margin q calls _ _ positive small replayed (by norm_num) (by norm_num)

/-- The quartet collision bound over both node truncations (even and odd groups). -/
theorem fixed_compression_quad_bound {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      QuadWitness result.2] ≤ (q : ENNReal)/2^123 := by
  let execution := (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))
  change Pr{let result ← execution}[QuadWitness result.2] ≤ _
  have split := prEvent_mono execution (fun result => QuadWitness result.2)
    (fun result => QuadWitnessAt 0 result.2 ∨ QuadWitnessAt 1 result.2)
    (fun _ hit => quad_witness_split hit)
  refine split.trans ((prEvent_or_le execution (fun result => QuadWitnessAt 0 result.2)
    (fun result => QuadWitnessAt 1 result.2)).trans ?_)
  have even := fixed_compression_quad_bound_at 0 compress program q calls positive small replayed bounded
  have odd := fixed_compression_quad_bound_at 1 compress program q calls positive small replayed bounded
  refine (add_le_add even odd).trans_eq ?_
  rw [← ENNReal.add_div, ← two_mul,
    show (2 : ENNReal)^124 = 2 * 2^123 by rw [show (124 : Nat) = 1+123 by decide, pow_add]; norm_num]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

theorem fixed_compression_pinned_leaf_bound_small {α : Type} (layout : PeerLeafLayout)
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitness result.2] ≤ (q : ENNReal)/2^123 :=
  layout.bound compress program q calls positive small replayed bounded

/-- The trace-level route to a fixed-compression replay bound: a witness in the stored rows forces
a bad trace, whose probability is `q / 2^124`. (Exposed for per-kind leaf binding.) -/
theorem fixed_compression_witness_bound {α : Type} (compress : Compression) (program : OracleComp World α)
    (witness : List PublicRow → Prop) (bad : BadSpec PermState) (q calls : Nat)
    (bounded : PublicQueryBound (recordRows program) calls)
    (extract : ∀ trace rows, PinnedRowsStored rows trace → witness rows → ¬ bad.Good trace)
    (prob : (toStrat compress (recordRows program)).prob PState.init
      (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) ≤ (q : ℝ)/2^124) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      witness result.2] ≤ (q : ENNReal)/2^124 :=
  fixed_compression_replayed_event compress program witness bad q calls bounded extract prob

/-- The salt-first half of leaf binding, as in the record (`s3PinCall`). -/
theorem fixed_compression_pinned_leaf_bound_sf {α : Type} (layout : SaltFirstPeerLayout)
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitnessOf false result.2] ≤ (q : ENNReal)/2^124 := by
  refine fixed_compression_replayed_event compress program (PinnedLeafWitnessOf false) s3PinCall.badSpec q calls bounded
    (pinned_witness_bad_sf layout) ?_
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have fits : calls < Fintype.card S3State := by rw [s3_card_state]; omega
  have raw := s3PinCall.prob_bad_le_inv (2^1344) (2^896) (2^1344) (2^896) (2^1345+2^897)
    calls fits s3_trunc_fiber s3_chop_fiber s3_pin_fiber s3_second_inputs (by norm_num) (by norm_num)
    st calls budget.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  have margin := replay_extra_margin q calls (2^1345+2^897) (2^896) positive small replayed (by norm_num) (by norm_num)
  norm_num [unionBound] at margin ⊢
  exact margin

def QuadReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ PinnedLeafWitness rows ∨ QuadWitness rows

theorem quad_replay_bound_of_layout {α : Type} (layout : PeerLeafLayout) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      QuadReplayEvidence result.2] ≤ (q : ENNReal)/2^120 := by
  let execution := Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program)
  let A : (α × List PublicRow) → Prop := fun result => CompressionWitness result.2
  let B : (α × List PublicRow) → Prop := fun result => PinnedLeafWitness result.2
  let C : (α × List PublicRow) → Prop := fun result => QuadWitness result.2
  change Pr{let result ← execution}[A result ∨ B result ∨ C result] ≤ _
  have termA : Pr{let result ← execution}[A result] ≤ 3 * (q : ENNReal) / (4 * 2^120) := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq A]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small replayed bounded
  have termB : Pr{let result ← execution}[B result] ≤ (q : ENNReal)/2^123 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_pinned_leaf_bound_small layout compress program q calls positive small replayed bounded
  have termC : Pr{let result ← execution}[C result] ≤ (q : ENNReal)/2^123 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_quad_bound compress program q calls positive small replayed bounded
  have margin : (q : ENNReal)/2^123 + (q : ENNReal)/2^123 ≤ (q : ENNReal)/2^122 := by
    rw [← ENNReal.add_div, ← two_mul,
      show (2 : ENNReal)^123 = 2 * 2^122 by rw [show (123 : Nat) = 1+122 by decide, pow_add]; norm_num]
    exact (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)).le
  exact (prEvent_or_le execution A (fun r => B r ∨ C r)).trans
    ((add_le_add termA ((prEvent_or_le execution B C).trans ((add_le_add termB termC).trans margin))).trans_eq
      (event_budget_sum q))

def quadDomain : Set Block := Set.range quartetEncode

theorem quad_domain_size : quadDomain.encard ≤ ((2^1024 : Nat) : ℕ∞) := by
  unfold quadDomain
  rw [← Set.image_univ]
  refine (Set.encard_image_le quartetEncode Set.univ).trans_eq ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, s3_card_bitvec]

theorem quad_domain_disjoint_private (index : Index) (salt : Words 2)
    (first : BitVec 1600) (entry : Words 32) :
    packBuffer (pinnedSecondInput index salt (replyWords first) entry) ∉ quadDomain := by
  rintro ⟨payload, hit⟩
  have zero : (quartetEncode payload).extractLsb' 128 64 = 0 := by
    change (payload ++ (0 : BitVec 576)).extractLsb' 128 64 = 0
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 128 + 64 ≤ 576)]
    decide
  have hit' : quartetEncode payload = packBuffer (pinnedSecondInput index salt (replyWords first) entry) := hit
  have tag := pinned_second_tag index salt first entry
  change (packBuffer (pinnedSecondInput index salt (replyWords first) entry)).extractLsb' 128 64 =
    pinnedPositionTag index at tag
  have zeroTag : pinnedPositionTag index = 0 :=
    tag.symm.trans ((congrArg (fun x : BitVec 1600 => x.extractLsb' 128 64) hit').symm.trans zero)
  have numerical : (pinnedPositionTag index).toNat = 0 := by rw [zeroTag]; rfl
  rw [pinned_position_tag_toNat] at numerical
  split at numerical <;> omega

theorem quad_fresh_inverse_prob (cache : Cache) (target : Block)
    (unused : UnusedOutput cache.entries target) (room : cache.entries.length ≤ 2^121) :
    Pr{let a ← @uniformSample _ (cache.inverseSampler target unused)}[a.val ∈ quadDomain] ≤
      (1 : ENNReal) / 2^575 := by
  have raw := inverse_fresh_event_le cache target unused quadDomain (2^1024) quad_domain_size
  rw [show Fintype.card Block = 2^1600 from s3_card_state] at raw
  have remaining : 2^1599 ≤ (2^1600 : Nat) - cache.entries.length := by omega
  have reduced := raw.trans (ENNReal.div_le_div (le_refl _) (show (2^1599 : ENNReal) ≤
    ((2^1600 : Nat) - cache.entries.length : Nat) by exact_mod_cast remaining))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at reduced
  exact reduced.trans_eq (by
    rw [show (2 : ENNReal)^1599 = 2^575 * 2^1024 from pow_add (2 : ENNReal) 575 1024]
    simpa only [one_mul] using
      ENNReal.mul_div_mul_right (c := (2 : ENNReal)^1024) 1 (2^575) (by positivity) (by finiteness))

theorem quad_cached_completion_inverse_prob (cache : Cache) (target : Block)
    (unused : UnusedOutput cache.entries target) (room : cache.entries.length ≤ 2^121) :
    Pr{let p ← cache.sample}[p.val.inverse target ∈ quadDomain] ≤ (1 : ENNReal)/2^575 := by
  have step := cache.inverse_step_eq target (fun answer _ => (pure answer : ProbComp Block))
  calc
    _ = Pr{let a ← (cache.sample >>= fun p => pure (p.val.inverse target))}[a ∈ quadDomain] := by
      simp only [bind_pure_comp, prEvent_map]
    _ = Pr{let a ← (do let (answer, next) ← cache.inverse target; let _ ← next.sample; pure answer)}[a ∈ quadDomain] :=
      step.prEvent_eq (· ∈ quadDomain)
    _ ≤ _ := by
      classical
      simp only [PermutationCache.inverse, unused, dite_true, bind_assoc, pure_bind]
      let draw := @uniformSample _ (cache.inverseSampler target unused)
      let next (a : RemainingInputs cache.entries) :=
        (cache.extendInverse target unused a).sample >>= fun _ => (pure a.val : ProbComp Block)
      change Pr{let a ← draw >>= next}[a ∈ quadDomain] ≤ _
      calc
        _ = Pr{let a ← draw >>= fun a => pure a.val}[a ∈ quadDomain] := by
          rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
          congr 1
          funext a
          congr 1
          rw [prEvent_pure]
          have fixed (value : Block) (reached : value ∈ support (next a)) : value = a.val := by
            unfold next at reached
            obtain ⟨_, _, equal⟩ := (mem_support_bind_iff _ _ _).1 reached
            simpa only [support_pure, Set.mem_singleton_iff] using equal
          by_cases member : a.val ∈ quadDomain
          · rw [ite_eq_left member]
            exact (prEvent_eq_one_iff _ _).2 (fun value reached => by rw [fixed value reached]; exact member)
          · rw [ite_eq_right member]
            exact (prEvent_eq_zero_iff _ _).2 (fun value reached => by rw [fixed value reached]; exact member)
        _ = Pr{let a ← draw}[a.val ∈ quadDomain] := by simp only [bind_pure_comp, prEvent_map]
        _ ≤ _ := quad_fresh_inverse_prob cache target unused room

theorem quad_fresh_variant_preimage_prob (cache : Cache) (high : BitVec 1344)
    (room : cache.entries.length ≤ 2^121) :
    Pr{let p ← cache.sample}[∃ low : BitVec 256,
      UnusedOutput cache.entries (high ++ low) ∧ p.val.inverse (high ++ low) ∈ quadDomain] ≤
      (1 : ENNReal)/2^319 := by
  let event (low : BitVec 256) (p : Completion cache.entries) :=
    UnusedOutput cache.entries (high ++ low) ∧ p.val.inverse (high ++ low) ∈ quadDomain
  have each (low : BitVec 256) : Pr{let p ← cache.sample}[event low p] ≤ (1 : ENNReal)/2^575 := by
    by_cases unused : UnusedOutput cache.entries (high ++ low)
    · simpa only [event, unused, true_and] using
        quad_cached_completion_inverse_prob cache (high ++ low) unused room
    · have zero : Pr{let p ← cache.sample}[event low p] = 0 := by
        apply (prEvent_eq_zero_iff _ _).2
        intro p _ hit
        exact unused hit.1
      rw [zero]
      positivity
  change Pr{let p ← cache.sample}[∃ low, event low p] ≤ _
  calc
    _ = Pr{let p ← cache.sample}[∃ low ∈ (Finset.univ : Finset (BitVec 256)), event low p] := by simp
    _ ≤ ∑ low : BitVec 256, Pr{let p ← cache.sample}[event low p] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _low : BitVec 256, (1 : ENNReal) / 2^575 := Finset.sum_le_sum fun low _ => each low
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, s3_card_bitvec]
      simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul]
      rw [show (2 : ENNReal)^575 = 2^319 * 2^256 from pow_add (2 : ENNReal) 319 256]
      simpa only [div_eq_mul_inv, one_mul] using
        ENNReal.mul_div_mul_right (c := (2 : ENNReal)^256) 1 (2^319) (by positivity) (by finiteness)

theorem quad_known_high_preimage_prob (cache : Cache) (highs : List (BitVec 1344))
    (room : cache.entries.length ≤ 2^121) (listBound : highs.length ≤ 2^26) :
    Pr{let p ← cache.sample}[∃ high ∈ highs, ∃ low : BitVec 256,
      UnusedOutput cache.entries (high ++ low) ∧ p.val.inverse (high ++ low) ∈ quadDomain] ≤
      (1 : ENNReal)/2^293 := by
  have each := prEvent_list_le highs cache.sample
    (fun high p => ∃ low : BitVec 256, UnusedOutput cache.entries (high ++ low) ∧
      p.val.inverse (high ++ low) ∈ quadDomain) (1/2^319)
    (fun high _ => quad_fresh_variant_preimage_prob cache high room)
  have count : (highs.length : ENNReal) ≤ (2 : ENNReal)^26 := by exact_mod_cast listBound
  refine each.trans ((mul_le_mul_of_nonneg_right count (by positivity : (0 : ENNReal) ≤ 1/2^319)).trans ?_)
  have same : (2 : ENNReal)^319 = (2 : ENNReal)^293 * 2^26 := pow_add _ 293 26
  apply le_of_eq
  rw [same]
  simpa only [div_eq_mul_inv, one_mul] using
    ENNReal.mul_div_mul_right (c := (2 : ENNReal)^26) 1 (2^293) (by positivity) (by finiteness)

end TwoPermutationPrototype.Sampling
