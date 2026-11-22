import CommitGolfCandidate.GroupedPhysical
import CommitGolfCandidate.GroupedChecks
import CommitGolfCandidate.GroupOpenFull
import CommitGolfCandidate.QuartetCounterCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate
import CommitGolfCandidate.K3GRBridge
import CommitGolfCandidate.K3OpenFacts

/-! Closing assembly: the executable commitment is the honest Quartet view with linked generator
salts (CU's commit facts and O's opener facts), which gives the certificate with the claimed
proof size, commit cycles and worst opening cycles. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Sampling
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
local instance groupedFullSpace {α : Type} : MeasurableSpace α := ⊤

/-- The claim: proof bytes, commit cycles and worst opening cycles. -/
abbrev claimProofBytes : Nat := 72160
abbrev claimCommitCycles : Nat := 504585244
abbrev claimOpeningCycles : Nat := 97691

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

theorem grouped_refines (hc : HeaderFacts) :
    Quartet.LinkedQuartetRefines QuartetCounterCertificate.linkedSchedule actual.scheme :=
  QuartetCounterCertificate.linked_refines_of_parts actual.scheme
    (fun o m k => QuartetCommit.physicalHeap o m (Grouped.chainSalts o k) 1) stash
    (fun o td p => proofFromTrapdoor (s:=actual) (virtualFor o td p) p)
    commit_distribution (fun o td p => fixed_open hc o td p) (fun _ _ _ _ => rfl)
    (fun o m k p => honest_proof hc o m k p)

private theorem opening_runs (hc : HeaderFacts) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤claimOpeningCycles ∧ (actual.readProof z).length≤claimProofBytes) ∧
      z.oracleCalls≤100*p.card := by
  obtain ⟨exit, succeeded, bounds, calls⟩ := all_resources hc td p z hit
  exact ⟨exit, succeeded, fun batch => ⟨(bounds batch).1.trans (by norm_num),
    (bounds batch).2.trans (by norm_num)⟩, calls⟩

theorem grouped_certificate (hc : HeaderFacts) :
    Certificate actual claimProofBytes claimCommitCycles claimOpeningCycles :=
  QuartetCounterCertificate.certificate_of_facts
    GroupedChecks.resources GroupedChecks.admitted
    ⟨opening_runs hc, grouped_refines hc⟩ GroupedChecks.checker_facts
    (Quartet.scheme_hiding_of_linked QuartetCounterCertificate.linkedSchedule actual.scheme (grouped_refines hc))

end TwoPermutationPrototype.GroupedOpening
