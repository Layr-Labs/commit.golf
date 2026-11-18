import CommitGolfCandidate.GroupedPhysical
import CommitGolfCandidate.GroupedChecks
import CommitGolfCandidate.GroupOpenFull
import CommitGolfCandidate.QuartetCounterCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
local instance groupedFullSpace {α : Type} : MeasurableSpace α := ⊤

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
    change (stash o m k).extractLsb' (8*(2684354568+8*j.val)) 64=_ at word
    simpa only [Nat.mul_add,←Nat.mul_assoc] using word
  have eq:=congrArg (fun w : Word => w.getLsbD (bit%64)) slim
  simpa only [BitVec.getLsbD_extractLsb',Nat.mod_lt bit (by decide : 0<64),decide_true,Bool.true_and,
    j,Fin.val_mk,Nat.div_add_mod] using eq

theorem virtual_components (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    let t:=virtualFor o td p
    (∀ n, n<8388608 → Opening.trapdoorHeap (s:=actual) t n=Opening.trapdoorHeap (s:=actual) td n) ∧
    (∀ i : Index, trapdoorLeaf (s:=actual) t i.val=trapdoorLeaf (s:=actual) td i.val) ∧
    (∀ i∈p, trapdoorSalt (s:=actual) t i=salts o.permutation (keyOf td) i) := by
  by_cases empty : p.card=0
  · rw [virtualFor,if_pos empty]
    exact ⟨fun _ _=>rfl,fun _=>rfl,fun i h => (by simpa [Finset.card_eq_zero.mp empty] using h : False).elim⟩
  · have nz : 0<p.card:=by omega
    let key:=keyOf td
    let init:=header (actual.initialState .opening (td,p))
    let last:=fixedPass o p key p.card 0 init
    have start:= (hc.ready td p nz)
    have sampled:=pass_fixed o td p key init 0 p.card (by omega) start
    have hit : last∈support (passTrace p p.card 0 init) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (last,p.card)
      change (_,_)∈support (o.run (passTrace p p.card 0 init));rw [sampled];simp [last]
    have live : Ready td p key last p.card := by simpa only [Nat.zero_add] using pass_post td p key init last p.card 0 start (by omega) hit
    have all : Seen o key p last p.card := by simpa only [Nat.zero_add] using seen_pass o td p key init 0 p.card (by omega) start (fun _ h => (Nat.not_lt_zero _ h).elim)
    rw [virtualFor,if_neg empty]
    have keep:=kept_tree td p key last live
    exact ⟨keep.1,keep.2,selected_salt o key p last all⟩

theorem commit_distribution (o : Oracle) (m : Message) :
    fixedOracleRun o (actual.scheme.commit m) =ᵈ (do
      let k ← $ᵗ Grouped.Key
      Pure.pure (QuartetCommit.physicalHeap o m (salts o.permutation k) 1,stash o m k)) := by
  change fixedOracleRun o (actual.readCommit <$> actual.run .commit m)=ᵈ _
  rw [fixed_oracle_run_map];unfold fixedOracleRun;rw [Grouped.counted_commit]
  simp only [map_bind,map_pure]
  apply EvalDistEq.bind_right;intro k
  have eq : committed o m k=(QuartetCommit.physicalHeap o m (salts o.permutation k) 1,stash o m k) :=
    Prod.ext (Grouped.physical_results o m k).1 rfl
  change Pure.pure (committed o m k) =ᵈ _
  rw [eq];rfl

theorem grouped_refines (hc : HeaderFacts) : Quartet.CounterQuartetRefines actual.scheme := by
  intro o m p
  unfold executableTranscript;rw [fixed_oracle_run_bind]
  apply ((commit_distribution o m).bind_left _).trans
  simp only [bind_assoc,pure_bind];apply EvalDistEq.bind_right;intro k
  let td:=stash o m k
  let virtual:=virtualFor o td p
  let π:=BiPermutation.equiv Block o.permutation
  let arr:=salts o.permutation k
  let d:=pinnedFullLeafDigests π m arr
  have ⟨nodes,children,opened⟩:=virtual_components hc o td p
  have orig:=Grouped.physical_results o m k
  rw [fixed_oracle_run_bind,fixed_open hc,pure_bind,fixed_oracle_run_pure]
  have leaf (i : Index) : trapdoorLeaf (s:=actual) td i.val=d i := by
    have v:=orig.2.2.1 i
    change QuartetRV.trapdoorLeaf (s:=actual) td i.val=QuartetCommit.originalLeaf o m arr i.val at v
    unfold QuartetCommit.originalLeaf Quartet.leafAt at v
    rw [dif_pos i.isLt] at v
    exact v
  have matchProof:=proof_from_trapdoor_matches actual virtual p (Quartet.quartetLookup π) o.compression d
    (trapdoorSalt (s:=actual) virtual)
    (fun n pos hi => (nodes n hi).trans (orig.2.1 n pos hi))
    (fun i => (children i).trans (leaf i)) (fun _=>rfl)
  have nonce : (fun i : {i // i∈p} => trapdoorSalt (s:=actual) virtual i.val)=(fun i => arr i.val) := by
    funext i;exact (opened i.val i.property).trans (by rw [show keyOf td=k from recovered_key o m k])
  rw [matchProof,nonce]
  rfl

theorem grouped_certificate (hc : HeaderFacts) : Certificate actual 72192 518591774 78794 :=
  QuartetCounterCertificate.certificate_of_facts
    GroupedChecks.resources GroupedChecks.admitted
    ⟨all_resources hc,grouped_refines hc⟩ GroupedChecks.checker_facts
    (Quartet.scheme_hiding_of_counter actual.scheme (grouped_refines hc))

end TwoPermutationPrototype.GroupedOpening
