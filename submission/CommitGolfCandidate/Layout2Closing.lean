import CommitGolfCandidate.GroupedPhysical
import CommitGolfCandidate.GroupedChecks
import CommitGolfCandidate.K3GRBridge
import CommitGolfCandidate.TwoPermutationPackedHonestInput
import CommitGolfCandidate.Layout2Full
import CommitGolfCandidate.Layout2V2Bridge
import CommitGolfCandidate.Layout2Abstract
import CommitGolfCandidate.Layout2OneByteCheckerFacts
import CommitGolfCandidate.Layout2CapOpenerSpec
import CommitGolfCandidate.Layout2CapLoaded
import CommitGolfCandidate.Layout2CapBridge
import CommitGolfCandidate.CapBHonest

/-! Layout 2 V2 closing assembly, with the fused opener (Increment 4b) and the one-byte search. The commitment is
today's (honest Quartet view with linked generator salts). The opener outputs `obProofFromPass capRaw` of the trapdoor
and the reference pass state `passEnd` (`Layout2F.fusedPass`): V2a's record blocks and flush, then the cap stage's raw
cap bytes, less the final byte when `k = f = 128`. V2a's records are
Astra's quartet transform of V1's proof of the reference trapdoor (`pass_proof_eq`), so on an honest stash the V2a
proof is `Quartet.encoder p` of today's honest proof (`l2_proof_eq`); with the cap stage's honest relation and
`Cap.encoder_of_blocks` the V2b proof is `Cap.encoder p` of it (`l2b_proof_eq`), and the opener's proof is `obEnc p`
of it (`ob_proof_eq`). `certificate_of_linked_enc` with the checker's `CheckerFactsEnc obEnc` gives the certificate
at 72,159 proof bytes, 504,585,244 commit cycles and 68,563 worst opening cycles. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open Sampling
open CommitGolfCandidate.Layout2 (convert encTables decTables)
open CommitGolfCandidate.Layout2CapStage (CapStage frontierDigests)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
local instance groupedFullSpace {α : Type} : MeasurableSpace α := ⊤

/-- The claim: proof bytes, commit cycles and worst opening cycles. -/
abbrev claimProofBytes : Nat := 72159
abbrev claimCommitCycles : Nat := 504585243
abbrev claimOpeningCycles : Nat := 68563

/-- V2a's encoding of an honest proof (V1's bit tables, then the quartet transform), the reference of the bridge. -/
abbrev l2Enc : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Quartet.encoder
/-- The V2b opener's encoding (V2a's, then the cap transform) and the checker's decoding (Astra's `Layout2.Cap`). -/
abbrev l2bEnc : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Cap.encoder
abbrev l2bDec : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Cap.decoder
/-- The one-byte search's encoding (`Cap.obEnc`): `Cap.encoder`, less the final byte when `k = 128` and the encoded
proof has 72,160 bytes. -/
abbrev obEnc : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Cap.obEnc

noncomputable def committed (o : Oracle) (m : Message) (k : Grouped.Key) :=
  actual.readCommit (Grouped.packedOutput o (Grouped.seededLeaves o m k))
noncomputable def stash (o : Oracle) (m : Message) (k : Grouped.Key) := (committed o m k).2

theorem recovered_key (o : Oracle) (m : Message) (k : Grouped.Key) : keyOf (stash o m k)=k := by
  have fixed := (Grouped.physical_results o m k).2.2.2
  apply BitVec.eq_of_getLsbD_eq;intro bit hb
  let j : Fin 3:=⟨bit/64,by omega⟩
  have slim : (keyOf (stash o m k)).extractLsb' (64*j.val) 64=k.extractLsb' (64*j.val) 64 := by
    unfold keyOf
    rw [nested_slice _ (show 64*j.val+64≤192 by have:=j.isLt;omega)]
    have word:=fixed j
    change (stash o m k).extractLsb' (8*(4831838216+8*j.val)) 64=_ at word
    simpa only [Nat.mul_add,←Nat.mul_assoc] using word
  have eq:=congrArg (fun w : Word => w.getLsbD (bit%64)) slim
  simpa only [BitVec.getLsbD_extractLsb',Nat.mod_lt bit (by decide : 0<64),decide_true,Bool.true_and,
    j,Fin.val_mk,Nat.div_add_mod] using eq

theorem commit_distribution (o : Oracle) (m : Message) :
    fixedOracleRun o (actual.scheme.commit m) =ᵈ (do
      let k ← $ᵗ Grouped.Key
      Pure.pure (QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1,stash o m k)) := by
  change fixedOracleRun o (actual.readCommit <$> actual.run .commit m)=ᵈ _
  rw [fixed_oracle_run_map];unfold fixedOracleRun;rw [Grouped.counted_commit]
  simp only [map_bind,map_pure]
  apply EvalDistEq.bind_right;intro k
  have eq : committed o m k=(QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1,stash o m k) :=
    Prod.ext (Grouped.physical_results o m k).1 rfl
  change Pure.pure (committed o m k) =ᵈ _
  rw [eq];rfl

theorem honest_proof (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    proofFromTrapdoor (s:=actual) (refTd o (stash o m k) p) p =
      (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  have orig := Grouped.physical_results o m k
  let d := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (Grouped.chainSalts o k)
  have proof := opened_proof o (stash o m k) p d (fun n pos hi => orig.2.1 n pos hi)
    (fun g hg => (group_reply_eq (stash o m k) g).symm.trans (orig.2.2.1 g hg))
  rw [proof, recovered_key]
  rfl

/-- The opened records of an honest stash have clean band-A and band-B digests (honest heap nodes). -/
theorem honest_clean (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    CleanRecords actual (refTd o (stash o m k) p) p := by
  have orig := Grouped.physical_results o m k
  let d := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (Grouped.chainSalts o k)
  have heap (n : Nat) (pos : 0<n) (hn : n<4194304) :
      Opening.trapdoorHeap (s:=actual) (refTd o (stash o m k) p) n=
        Quartet.upperHeap (Quartet.quartetLookup (BiPermutation.equiv Block o.permutation)) o.compression d n := by
    rw [ref_heap o _ p n hn]
    exact orig.2.1 n pos hn
  constructor
  · intro j hj a
    rw [record_fields actual _ p j hj]
    show (Opening.trapdoorHeap (s:=actual) _ (upperNode (posAt p j) (2+a.val) ^^^ 1)).extractLsb' 240 16=0
    have r := CommitGolfCandidate.Layout2.bandA_sibling_range (posAt p j) a
    rw [heap _ (by omega) (by omega)]
    exact CommitGolfCandidate.Layout2.upper_heap_high_240 _ _ _ _ r.1 r.2
  · intro j hj b
    rw [record_fields actual _ p j hj]
    show (Opening.trapdoorHeap (s:=actual) _ (upperNode (posAt p j) (6+b.val) ^^^ 1)).extractLsb' 238 18=0
    have r := CommitGolfCandidate.Layout2.bandB_sibling_range (posAt p j) b
    rw [heap _ r.1 (by omega)]
    exact upper_heap_high _ _ _ _ r.1 r.2

/-- What the pass leaves under a fixed oracle, for every position set (vacuous for the empty one). -/
theorem end_seen (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    Seen o (keyOf td) td p (passEnd o td p) p.card :=
  pass_end_facts o td p

/-- On an honest stash the opener's proof is the V2a encoding of the honest proof. -/
theorem l2_proof_eq (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    l2ProofFromPass (s:=actual) (stash o m k) (passEnd o (stash o m k) p) p =
      l2Enc p (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  rw [pass_proof_eq o _ p _ (end_seen o _ p), ← honest_proof o m k p,
    l2_proof_convert actual actual_layout _ p (honest_clean o m k p)]
  rfl

private theorem frontier_node_bounds (groups : List Nat) (node height : Nat)
    (span : Opening.CapSpan node height) (entry : Nat)
    (member : entry ∈ capFrontierNodes groups node height) : 0 < entry ∧ entry < 512 := by
  induction height generalizing node with
  | zero =>
    unfold capFrontierNodes at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span
  | succ height ih =>
    unfold capFrontierNodes at member
    split at member
    · obtain ⟨left,right⟩ := Opening.cap_span_children node height span
      rcases List.mem_append.mp member with child | child
      · exact ih _ left child
      · exact ih _ right child
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span

/-- The frontier digests of an honest stash have zero bits `238..255` (honest heap nodes). -/
theorem honest_digests (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    ∀ d ∈ frontierDigests (s:=actual) (stash o m k) p, d.extractLsb' 238 18=0 := by
  have orig := Grouped.physical_results o m k
  intro d hd
  unfold frontierDigests at hd
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hd
  have r : 0<n ∧ n<512 := by
    unfold Opening.openingNodes at hn
    split at hn
    · simp at hn
    · exact frontier_node_bounds _ 1 8 Opening.cap_span_root n hn
  change (Opening.trapdoorHeap (s:=actual) (stash o m k) n).extractLsb' 238 18=0
  have h : Opening.trapdoorHeap (s:=actual) (stash o m k) n=_ := orig.2.1 n r.1 (by omega)
  rw [h]
  exact upper_heap_high _ _ _ _ r.1 (by omega)

theorem records_length (loaded pass : MachineState) (p : Positions) (k : Nat) :
    ((List.range k).flatMap (physRecord2 loaded pass p)).length=destOf k-proofBase := by
  induction k with
  | zero => simp [dest_zero]
  | succ k ih =>
    have step := dest_next k
    have lo := (dest_bound k).1
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton]
    simp only [physRecord2, List.length_map, List.length_range]
    omega

/-- The V2a record part (records and flush) of a position set has `534 k` bytes. -/
theorem prefix_length (loaded pass : MachineState) (p : Positions) :
    ((List.range p.card).flatMap (physRecord2 loaded pass p) ++ physFlush loaded p).length=534*p.card := by
  have lo := (dest_bound p.card).1
  have e := dest_end p.card
  rw [List.length_append, records_length]
  simp only [physFlush, List.length_map, List.length_range]
  omega

/-- On an honest stash the V2b opener's proof is `Cap.encoder p` of today's honest proof. -/
theorem l2b_proof_eq (capRaw : List (BitVec 256) → List Byte) (cap : CapStage capRaw)
    (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    l2bProofFromPass (s:=actual) capRaw (stash o m k) (passEnd o (stash o m k) p) p =
      l2bEnc p (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  let H := (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2
  let td := stash o m k
  let ld := actual.initialState .opening (td,p)
  let pass := passEnd o td p
  let R := (List.range p.card).flatMap (physRecord2 ld pass p) ++ physFlush ld p
  let ds := frontierDigests (s:=actual) td p
  have rl : R.length=534*p.card := prefix_length ld pass p
  have v2b : l2bProofFromPass (s:=actual) capRaw td pass p=R ++ capRaw ds := rfl
  have v2a : l2ProofFromPass (s:=actual) td pass p=R ++ foldNodes ds := rfl
  have old : CommitGolfCandidate.Layout2.Quartet.encoder p H=R ++ foldNodes ds := by
    rw [← v2a]; exact (l2_proof_eq o m k p).symm
  have fl := fold_nodes_length ds
  have cl := cap.length ds
  have hlen : H.length=534*p.card+capOffset ds.length := by
    have := congrArg List.length old
    rw [CommitGolfCandidate.Layout2.Quartet.encoder_length, List.length_append, rl, fl] at this
    exact this
  have dsl : ds.length ≤ 128 := by
    show ((Opening.openingNodes p).map (fun n => td.extractLsb' (256*n) 256)).length ≤ 128
    rw [List.length_map]; exact Opening.opening_nodes_bound p
  show l2bProofFromPass (s:=actual) capRaw td pass p=_
  rw [v2b]
  apply CommitGolfCandidate.Layout2.Cap.encoder_of_blocks p H
  · rw [List.length_append, rl, cl, hlen]
  · intro j _ hj
    have hR : j<R.length := by omega
    rw [old, List.getElem?_append_left hR, List.getElem?_append_left hR]
  · intro g j hj hlt
    have hc : 952*g+j<capOffset ds.length := by omega
    have cap_at := cap.honest ds dsl (honest_digests o m k p) g j hj hc
    have lhs : (R ++ capRaw ds)[534*p.card+(952*g+j)]?.getD 0=(capRaw ds)[952*g+j]?.getD 0 := by
      rw [show 534*p.card+(952*g+j)=R.length+(952*g+j) by omega,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have src : ∀ z, (CommitGolfCandidate.Layout2.Quartet.encoder p H)[534*p.card+(952*g+z)]?.getD 0=
        (foldNodes ds)[952*g+z]?.getD 0 := by
      intro z
      rw [old, show 534*p.card+(952*g+z)=R.length+(952*g+z) by omega,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have nlen : H.length-534*p.card=capOffset ds.length := by omega
    rw [lhs, cap_at, nlen]
    simp only [src]

theorem cap_encoder_length (p : Positions) (P : Proof) : (l2bEnc p P).length=P.length := by
  simp [l2bEnc, CommitGolfCandidate.Layout2.Cap.encoder]

/-- An honest proof has `proofLength p` bytes. -/
theorem honest_length (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2.length=
      QuartetOpening.proofLength p := by
  let td := stash o m k
  let ld := actual.initialState .opening (td,p)
  let pass := passEnd o td p
  let ds := frontierDigests (s:=actual) td p
  have rl : ((List.range p.card).flatMap (physRecord2 ld pass p) ++ physFlush ld p).length=534*p.card :=
    prefix_length ld pass p
  have v2a : l2ProofFromPass (s:=actual) td pass p=
      ((List.range p.card).flatMap (physRecord2 ld pass p) ++ physFlush ld p) ++ foldNodes ds := rfl
  have e := congrArg List.length (l2_proof_eq o m k p)
  rw [v2a, CommitGolfCandidate.Layout2.Quartet.encoder_length, List.length_append, rl, fold_nodes_length] at e
  have dl : ds.length=(Opening.openingNodes p).length := by
    show ((Opening.openingNodes p).map (fun n => td.extractLsb' (256*n) 256)).length=_
    rw [List.length_map]
  rw [← e, dl, proof_length_split]

/-- On an honest stash the opener's proof is `obEnc p` of today's honest proof. -/
theorem ob_proof_eq (capRaw : List (BitVec 256) → List Byte) (cap : CapStage capRaw)
    (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    obProofFromPass capRaw (stash o m k) (passEnd o (stash o m k) p) p =
      obEnc p (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  have len := (cap_encoder_length p _).trans (honest_length o m k p)
  have split := proof_length_split p
  have nb := Opening.opening_nodes_bound p
  unfold obProofFromPass obEnc CommitGolfCandidate.Layout2.Cap.obEnc
  rw [l2b_proof_eq capRaw cap o m k p, len]
  unfold CommitGolfCandidate.Layout2CapStage.dropped
  by_cases hd : p.card=128 ∧ (Opening.openingNodes p).length=128
  · have L : QuartetOpening.proofLength p=72160 := by rw [split, hd.1, hd.2]; rfl
    rw [if_pos hd, if_pos ⟨hd.1, L⟩, L]
  · have nd : ¬(p.card=128 ∧ QuartetOpening.proofLength p=72160) := by
      rintro ⟨c, h⟩
      apply hd
      refine ⟨c, ?_⟩
      rw [split, c] at h
      unfold capOffset at h
      omega
    rw [if_neg hd, if_neg nd, Nat.sub_zero, List.take_of_length_le (by rw [len])]

theorem l2_refines (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) :
    Quartet.LinkedQuartetRefinesEnc QuartetCounterCertificate.linkedSchedule obEnc actual.scheme :=
  QuartetCounterCertificate.linked_refines_of_parts_enc actual.scheme obEnc
    (fun o m k => QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1) stash
    (fun o td p => obProofFromPass capRaw td (passEnd o td p) p)
    commit_distribution (fun o td p => fixed_open capRaw cap o td p) (fun _ _ _ _ => rfl)
    (fun o m k p => ob_proof_eq capRaw cap o m k p)

private theorem opening_runs (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤claimOpeningCycles ∧ (actual.readProof z).length≤claimProofBytes) ∧
      z.oracleCalls≤100*p.card :=
  all_resources capRaw cap td p z hit

/-- Lengths of an honest proof: `534 k` record bytes and at most 3,808 cap bytes. -/
theorem honest_lengths (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    534*positions.card ≤ (QuartetCertificate.honestCheckInput oracle message positions salts).proof.length ∧
      (QuartetCertificate.honestCheckInput oracle message positions salts).proof.length ≤ 534*positions.card+3808 := by
  rw [PackedHonest.honest_proof_parts, List.length_append,
    PackedHonest.fixed_flatmap_length _ 534 (fun _ => Quartet.opening_record_length _ _ _ _) _,
    PackedHonest.honest_order_length]
  have := Quartet.frontier_proof238_bound (PackedHonest.honestHeap oracle message salts)
    (Opening.groupsBefore positions positions.card)
  omega

theorem honest_fits (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (QuartetCertificate.honestCheckInput oracle message positions salts).proof.length ≤ actual.sizes.proof := by
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have room := l2abi.capacity
  have h := (honest_lengths oracle message positions salts).2
  unfold capacity recordBytes at room
  unfold LENGTH LOG_LENGTH at card room
  omega

/-- The certificate from the cap stage and the one-byte checker's facts for `obEnc` (the fused loop's facts, phase
writers included, are theorems of `Layout2FusedLoop`). -/
theorem l2_certificate (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (checks : QuartetCertificate.CheckerFactsEnc obEnc actual) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  QuartetCounterCertificate.certificate_of_linked_enc GroupedChecks.resources GroupedChecks.admitted
    ⟨opening_runs capRaw cap, l2_refines capRaw cap⟩ checks

theorem layout2_certificate_of (capRaw : List (BitVec 256) → List Byte) (cap : CapStage capRaw)
    (checks : QuartetCertificate.CheckerFactsEnc obEnc actual) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  l2_certificate capRaw cap checks

/-- The certificate with Astra's cap stage (`CapB.cap_stage`, with the one-byte guard) and its honest relation
(`CapB.cap_raw_honest`); the one-byte checker's facts are the remaining premise. -/
theorem layout2_certificate_of_checks (checks : QuartetCertificate.CheckerFactsEnc obEnc actual) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  layout2_certificate_of CommitGolfCandidate.CapB.capRaw
    (CommitGolfCandidate.Layout2CapStage.cap_stage_of (fun ds _ clean => CommitGolfCandidate.CapB.cap_raw_honest ds clean))
    checks

/-- The certificate: Astra's cap stage with the one-byte guard, and the one-byte checker's facts
(`K1Check.onebyte_checker_facts`). -/
theorem layout2_certificate : Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  layout2_certificate_of_checks CommitGolf.K1Check.onebyte_checker_facts

end TwoPermutationPrototype.GroupedOpening.Layout2V2
