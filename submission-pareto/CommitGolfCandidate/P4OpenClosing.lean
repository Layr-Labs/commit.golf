import CommitGolfCandidate.P4Results
import CommitGolfCandidate.P4OpenFull
import CommitGolfCandidate.BinaryCounterCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate

/-! P4 certificate. The opener's proof is `proofFromTrapdoor` of its virtual trapdoor (`fixed_open`). On an honest
trapdoor, that virtual trapdoor keeps every heap node and carries the counter-mode salt of the recovered key at every
opened position. So the executable transcript is the pinned honest view with counter-mode salts, which is what the
counter hiding theorem and 04680e02's unchanged checker facts need. Ported from dadon's 2a19be00 `GroupOpenClosing`. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
local instance p4FullSpace {α : Type} : MeasurableSpace α := ⊤

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
    rw [show 8*(80*LENGTH+8+8*j.val)=8*1342177288+64*j.val by unfold LENGTH LOG_LENGTH;omega] at word
    exact word
  have eq:=congrArg (fun w : Word => w.getLsbD (bit%64)) slim
  simpa only [BitVec.getLsbD_extractLsb',Nat.mod_lt bit (by decide : 0<64),decide_true,Bool.true_and,
    j,Fin.val_mk,Nat.div_add_mod] using eq

theorem virtual_components (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    (∀ n, n<2*LENGTH → Opening.trapdoorHeap (s:=actual) (virtualFor o td p) n=Opening.trapdoorHeap (s:=actual) td n) ∧
    (∀ i∈p, Opening.trapdoorSalt (s:=actual) (virtualFor o td p) i=salts o.permutation (keyOf td) i) := by
  by_cases empty : p.card=0
  · rw [virtualFor,if_pos empty]
    exact ⟨fun _ _=>rfl,fun i h => (by simpa [Finset.card_eq_zero.mp empty] using h : False).elim⟩
  · have nz : 0<p.card:=by omega
    let key:=keyOf td
    let init:=header (actual.initialState .opening (td,p))
    let last:=fixedPass o p key p.card 0 init
    have start:= (hc.ready td p nz)
    have sampled:=pass_fixed o td p key init 0 p.card (by omega) start
    have hit : last∈support (passTrace p p.card 0 init) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (last,p.card)
      change (_,_)∈support (o.run (passTrace p p.card 0 init));rw [sampled];simp [last]
    have live : Ready td p key last p.card := by
      simpa only [Nat.zero_add] using pass_post td p key init last p.card 0 start (by omega) hit
    have all : Seen o key p last p.card := by
      simpa only [Nat.zero_add] using
        seen_pass o td p key init 0 p.card (by omega) start (fun _ h => (Nat.not_lt_zero _ h).elim)
    rw [virtualFor,if_neg empty]
    exact ⟨kept_tree td p key last live,selected_salt o key p last all⟩

theorem commit_distribution (o : Oracle) (m : Message) :
    fixedOracleRun o (actual.scheme.commit m) =ᵈ (do
      let k ← $ᵗ Grouped.Key
      Pure.pure (Grouped.publicHeap o m k 1,stash o m k)) := by
  change fixedOracleRun o (actual.readCommit <$> actual.run .commit m)=ᵈ _
  rw [fixed_oracle_run_map];unfold fixedOracleRun;rw [Grouped.counted_commit]
  simp only [map_bind,map_pure]
  apply EvalDistEq.bind_right;intro k
  have eq : committed o m k=(Grouped.publicHeap o m k 1,stash o m k) :=
    Prod.ext (Grouped.physical_results o m k).1 rfl
  change Pure.pure (committed o m k) =ᵈ _
  rw [eq];rfl

theorem p4_refines (hc : HeaderFacts) : CounterTranscriptRefines actual.scheme mixedTranscriptBuilder := by
  intro o m p
  unfold executableTranscript;rw [fixed_oracle_run_bind]
  apply ((commit_distribution o m).bind_left _).trans
  simp only [bind_assoc,pure_bind];apply EvalDistEq.bind_right;intro k
  let td:=stash o m k
  let virtual:=virtualFor o td p
  let π:=BiPermutation.equiv Block o.permutation
  let arr:=salts o.permutation k
  let d:=pinnedFullLeafDigests π m arr
  have ⟨nodes,opened⟩:=virtual_components hc o td p
  have orig:=Grouped.physical_results o m k
  rw [fixed_oracle_run_bind,fixed_open hc,pure_bind,fixed_oracle_run_pure]
  have matchProof:=PackedOpening.proof_from_trapdoor_matches actual virtual p o.compression d
    (Opening.trapdoorSalt (s:=actual) virtual)
    (fun n pos hi => (nodes n hi).trans (orig.2.1 n pos hi)) (fun _=>rfl)
  have nonce : (fun i : {i // i∈p} => Opening.trapdoorSalt (s:=actual) virtual i.val)=(fun i => arr i.val) := by
    funext i;exact (opened i.val i.property).trans (by rw [show keyOf td=k from recovered_key o m k])
  rw [matchProof,nonce]
  rfl

theorem p4_admitted : actual.Admission := by
  intro program
  cases program <;>
    simp only [actual, Artifact.submission, Image.Valid, Image.byteSize, LayoutValid,
      dataBase, ArtifactEncoding.length_decode] <;> decide

theorem p4_commit_resources (m : Message) (result : Execution) (reachable : result∈support (actual.run .commit m)) :
    result.exit=.success ∧ result.cycles=598103075 ∧ result.oracleCalls≤COMMIT_BUDGET := by
  rw [Grouped.commit_run m] at reachable
  simp only [Grouped.commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨key,_,state,_,rfl⟩ := reachable
  exact ⟨rfl,rfl,by change 51859455≤COMMIT_BUDGET;decide⟩

theorem p4_certificate (hc : HeaderFacts) : Certificate actual 69632 598103075 91671 :=
  BinaryCounterCertificate.certificate_of_facts p4_commit_resources p4_admitted
    ⟨all_resources hc,p4_refines hc⟩ (Packed.Checker.executable_checker_facts pinned_replay_bound)
    (scheme_hiding_of_counter actual.scheme mixedTranscriptBuilder (p4_refines hc))

end TwoPermutationPrototype.GroupedOpening
