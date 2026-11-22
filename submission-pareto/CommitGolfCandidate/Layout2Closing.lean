import CommitGolfCandidate.GroupedPhysical
import CommitGolfCandidate.GroupedChecks
import CommitGolfCandidate.K3GRBridge
import CommitGolfCandidate.K3OpenFacts
import CommitGolfCandidate.TwoPermutationPackedHonestInput
import CommitGolfCandidate.Layout2Full
import CommitGolfCandidate.Layout2Area
import CommitGolfCandidate.Layout2Abstract
import CommitGolfCandidate.Layout2V1CheckerFacts
import CommitGolfCandidate.Layout2WriterFacts

/-! Layout 2 closing assembly. The commitment is today's (honest Quartet view with linked generator salts). The
opener outputs `l2ProofFromTrapdoor` of the virtual trapdoor, which on an honest stash is Neon's V1 encoding
`convert encTables k` of today's honest proof (`l2_proof_eq`, from clean honest digests). Neon's
`certificate_of_dec` with the checker's `CheckerFactsDec` for `convert decTables k` gives the certificate at
72,160 proof bytes, 504,585,244 commit cycles and 77,949 worst opening cycles. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Sampling
open CommitGolfCandidate.Layout2Phase (PhaseFacts)
open CommitGolfCandidate.Layout2 (convert encTables decTables)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
local instance groupedFullSpace {α : Type} : MeasurableSpace α := ⊤

/-- The claim: proof bytes, commit cycles and worst opening cycles. -/
abbrev claimProofBytes : Nat := 72160
abbrev claimCommitCycles : Nat := 504585244
abbrev claimOpeningCycles : Nat := 77949

/-- The opener's encoding of an honest proof (Neon's V1 layout) and the checker's decoding. -/
def l2Enc (p : Positions) (proof : Proof) : Proof := convert encTables p.card proof
def l2Dec (p : Positions) (proof : Proof) : Proof := convert decTables p.card proof

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

theorem honest_proof (hc : HeaderFacts) (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    proofFromTrapdoor (s:=actual) (virtualFor o (stash o m k) p) p =
      (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  have orig := Grouped.physical_results o m k
  let d := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (Grouped.chainSalts o k)
  have proof := opened_proof hc o (stash o m k) p d (fun n pos hi => orig.2.1 n pos hi)
    (fun g hg => (group_reply_eq (stash o m k) g).symm.trans (orig.2.2.1 g hg))
  rw [proof, recovered_key]
  rfl

/-- The opened records of an honest stash have clean band-A and band-B digests (honest heap nodes). -/
theorem honest_clean (hc : HeaderFacts) (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    CleanRecords actual (virtualFor o (stash o m k) p) p := by
  have orig := Grouped.physical_results o m k
  let d := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (Grouped.chainSalts o k)
  have heap (n : Nat) (pos : 0<n) (hn : n<4194304) (nz : 0<p.card) :
      Opening.trapdoorHeap (s:=actual) (virtualFor o (stash o m k) p) n=
        Quartet.upperHeap (Quartet.quartetLookup (BiPermutation.equiv Block o.permutation)) o.compression d n := by
    rw [virtual_end o _ p nz, (end_components hc o _ p nz).1 n hn]
    exact orig.2.1 n pos hn
  constructor
  · intro j hj a
    rw [record_fields actual _ p j hj]
    show (Opening.trapdoorHeap (s:=actual) _ (upperNode (posAt p j) (2+a.val) ^^^ 1)).extractLsb' 240 16=0
    have r := CommitGolfCandidate.Layout2.bandA_sibling_range (posAt p j) a
    rw [heap _ (by omega) (by omega) (by omega)]
    exact CommitGolfCandidate.Layout2.upper_heap_high_240 _ _ _ _ r.1 r.2
  · intro j hj b
    rw [record_fields actual _ p j hj]
    show (Opening.trapdoorHeap (s:=actual) _ (upperNode (posAt p j) (6+b.val) ^^^ 1)).extractLsb' 238 18=0
    have r := CommitGolfCandidate.Layout2.bandB_sibling_range (posAt p j) b
    rw [heap _ r.1 (by omega) (by omega)]
    exact upper_heap_high _ _ _ _ r.1 r.2

/-- On an honest stash the opener's proof is the V1 encoding of the honest proof. -/
theorem l2_proof_eq (hc : HeaderFacts) (o : Oracle) (m : Message) (k : Grouped.Key) (p : Positions) :
    l2ProofFromTrapdoor (s:=actual) (virtualFor o (stash o m k) p) p =
      l2Enc p (Quartet.honestView Quartet.builder o.compression (BiPermutation.equiv Block o.permutation) m p
        (Permutation.LinkedSalt.salts QuartetCounterCertificate.linkedSchedule o.permutation k)).2 := by
  rw [← honest_proof hc o m k p]
  exact l2_proof_convert actual actual_layout _ p (honest_clean hc o m k p)

theorem l2_refines (hc : HeaderFacts) (phases : ∀ p<4, PhaseFacts openingImage p) :
    Quartet.LinkedQuartetRefinesEnc QuartetCounterCertificate.linkedSchedule l2Enc actual.scheme :=
  QuartetCounterCertificate.linked_refines_of_parts_enc actual.scheme l2Enc
    (fun o m k => QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1) stash
    (fun o td p => l2ProofFromTrapdoor (s:=actual) (virtualFor o td p) p)
    commit_distribution (fun o td p => fixed_open hc phases o td p) (fun _ _ _ _ => rfl)
    (fun o m k p => l2_proof_eq hc o m k p)

private theorem opening_runs (hc : HeaderFacts) (phases : ∀ p<4, PhaseFacts openingImage p)
    (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤claimOpeningCycles ∧ (actual.readProof z).length≤claimProofBytes) ∧
      z.oracleCalls≤100*p.card :=
  all_resources hc phases td p z hit

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

/-- The Layout 2 certificate from the phase writers, today's pass facts and the checker's facts for
`convert decTables k`. -/
theorem l2_certificate (hc : HeaderFacts) (phases : ∀ p<4, PhaseFacts openingImage p)
    (checks : QuartetCertificate.CheckerFactsDec l2Dec actual) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  QuartetCounterCertificate.certificate_of_dec GroupedChecks.resources GroupedChecks.admitted
    ⟨opening_runs hc phases, l2_refines hc phases⟩ checks
    (fun o m p s => CommitGolfCandidate.Layout2.convert_dec_enc p.card _ (honest_lengths o m p s).1)
    (fun o m p s => CommitGolfCandidate.Layout2.convert_length _ _ _)
    (fun o m p s => honest_fits o m p s)

/-- The Layout 2 certificate: Astra's phase writers (`layout2_writer_facts`) and V1 checker
(`K1Check.v1_checker_facts`) with today's pass facts. -/
theorem layout2_certificate (hc : HeaderFacts) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  l2_certificate hc layout2_writer_facts CommitGolf.K1Check.v1_checker_facts

end TwoPermutationPrototype.GroupedOpening.Layout2
