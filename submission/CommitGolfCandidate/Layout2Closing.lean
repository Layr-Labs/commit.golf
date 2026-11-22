import CommitGolfCandidate.GroupedPhysical
import CommitGolfCandidate.GroupedChecks
import CommitGolfCandidate.K3GRBridge
import CommitGolfCandidate.TwoPermutationPackedHonestInput
import CommitGolfCandidate.Layout2Full
import CommitGolfCandidate.Layout2V2Bridge
import CommitGolfCandidate.Layout2Abstract
import CommitGolfCandidate.Layout2V2CheckerFacts
import CommitGolfCandidate.Layout2Writer2Facts

/-! Layout 2 V2a closing assembly. The commitment is today's (honest Quartet view with linked generator salts). The
opener outputs `l2ProofFromPass` of the trapdoor and the pass's end state, which is Astra's quartet transform of V1's
proof of the reference trapdoor (`pass_proof_eq`); on an honest stash that is `Quartet.encoder p` of today's honest
proof (`l2_proof_eq`). `certificate_of_dec` with the checker's `CheckerFactsDec` for `Quartet.decoder` gives the
certificate at 72,160 proof bytes, 504,585,244 commit cycles and 72,955 worst opening cycles. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open Sampling
open CommitGolfCandidate.Layout2Phase2 (PhaseFacts)
open CommitGolfCandidate.Layout2 (convert encTables decTables)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
local instance groupedFullSpace {α : Type} : MeasurableSpace α := ⊤

/-- The claim: proof bytes, commit cycles and worst opening cycles. -/
abbrev claimProofBytes : Nat := 72160
abbrev claimCommitCycles : Nat := 504585244
abbrev claimOpeningCycles : Nat := 72955

/-- The opener's encoding of an honest proof (V1's bit tables, then the quartet transform) and the checker's
decoding (Astra's `Layout2.Quartet`). -/
abbrev l2Enc : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Quartet.encoder
abbrev l2Dec : Positions → Proof → Proof := CommitGolfCandidate.Layout2.Quartet.decoder

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
    Seen o (keyOf td) td p (passEnd o td p) p.card := by
  by_cases empty : p.card=0
  · rw [empty]; exact seen_zero o _ td p _
  · exact (pass_end_facts o td p (by omega)).2

/-- On an honest stash the opener's proof is the V2a encoding of the honest proof. -/
theorem l2_proof_eq (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    l2ProofFromPass (s:=actual) (stash o m k) (passEnd o (stash o m k) p) p =
      l2Enc p (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  rw [pass_proof_eq o _ p _ (end_seen o _ p), ← honest_proof o m k p,
    l2_proof_convert actual actual_layout _ p (honest_clean o m k p)]
  rfl

theorem l2_refines (phases : ∀ p<4, PhaseFacts openingImage p) :
    Quartet.LinkedQuartetRefinesEnc QuartetCounterCertificate.linkedSchedule l2Enc actual.scheme :=
  QuartetCounterCertificate.linked_refines_of_parts_enc actual.scheme l2Enc
    (fun o m k => QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1) stash
    (fun o td p => l2ProofFromPass (s:=actual) td (passEnd o td p) p)
    commit_distribution (fun o td p => fixed_open phases o td p) (fun _ _ _ _ => rfl)
    (fun o m k p => l2_proof_eq o m k p)

private theorem opening_runs (phases : ∀ p<4, PhaseFacts openingImage p)
    (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤claimOpeningCycles ∧ (actual.readProof z).length≤claimProofBytes) ∧
      z.oracleCalls≤100*p.card :=
  all_resources phases td p z hit

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

/-- The V2a certificate from the phase writers and the checker's facts for `Quartet.decoder`. -/
theorem l2_certificate (phases : ∀ p<4, PhaseFacts openingImage p)
    (checks : QuartetCertificate.CheckerFactsDec l2Dec actual) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  QuartetCounterCertificate.certificate_of_dec GroupedChecks.resources GroupedChecks.admitted
    ⟨opening_runs phases, l2_refines phases⟩ checks
    (fun o m p s => CommitGolfCandidate.Layout2.Quartet.decode_encode p _ (honest_lengths o m p s).1)
    (fun o m p s => CommitGolfCandidate.Layout2.Quartet.encoder_length _ _)
    (fun o m p s => honest_fits o m p s)

/-- The V2a certificate: Astra's V2a phase writers (`layout2_writer2_facts`) and V2a checker
(`K1Check.v2a_checker_facts`). -/
theorem layout2_certificate : Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  l2_certificate layout2_writer2_facts CommitGolf.K1Check.v2a_checker_facts

end TwoPermutationPrototype.GroupedOpening.Layout2V2
