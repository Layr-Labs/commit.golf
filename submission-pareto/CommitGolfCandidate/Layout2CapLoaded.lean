import CommitGolfCandidate.Layout2CapInput
import CommitGolfCandidate.Layout2QuartetLoaded
import CommitGolfCandidate.TwoPermutationPackedHonestInput
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype
open CommitGolfCandidate.Layout2.Quartet (checkImage)
set_option maxHeartbeats 1400000

theorem honest_good (o : Oracle) (msg : Message) (p : Positions) (salts : Index → BitVec 128) :
    Good p.card (QuartetCertificate.honestCheckInput o msg p salts).proof.length := by
  rw [PackedHonest.honest_proof_length,←size_eq]
  apply good_shape
  intro empty;simp [Opening.openingNodes,empty]

theorem reserve (k len hc hr : Nat) (card : k≤16777216) (fits : len≤8959041024)
    (cap : hc≤200+108*(len-534*k)) (recs : hr≤9+65*k+prologueSteps k) :
    hc+hr+34359803904≤2^41 := by
  unfold prologueSteps tailSteps Layout2.dispatchCost at recs
  split_ifs at recs <;> omega

theorem prepare_run (τ : Tables) (wf : WellFormed τ)
    (physical : ∀ j,j<85440 → Layout2Helpers.pget K1Artifact.checkData j=tableByte τ j)
    (i : CheckInput) (fits : i.proof.length≤8959041024) :
    let k:=i.positions.card
    let s:=candidate.initialState .check i
    ∃ t h c, h+34359803904≤2^41 ∧ Runs checkImage s t h c ∧
      (if Good k i.proof.length then Normalized τ (candidate.initialState .check (Quartet.prepared (prepared i))) t k
       else t.pc=pc 364) := by
  dsimp only
  let s:=candidate.initialState .check i
  let k:=i.positions.card
  have args:=initial_args i fits
  obtain ⟨m,a,ca,limit,ra,done⟩:=pass s k _ args (Quartet.init_entry i).2 (initial_data i fits)
    (fun j h=>scratch_clean i j (by omega))
  by_cases legal : Good k i.proof.length
  · rw [if_pos legal] at done
    obtain ⟨pcM,wrote,kept⟩:=done
    have prev : Kept temps (candidate.initialState .check (prepared i)) m := by
      intro r free;exact (kept r free).trans (same_args candidate i r)
    obtain ⟨t,b,cb,le,rb,norm⟩:=Quartet.prepare_from τ wf physical (prepared i) (by simpa using fits)
      (by simpa only [prepared_len,show (prepared i).positions=i.positions from rfl] using legal.1)
      m pcM prev (prepared_mem i fits legal wrote)
    exact ⟨t,_,_,reserve k _ a b args.count fits limit le,ra.thenDo rb,by rwa [if_pos legal]⟩
  · exact ⟨m,a,ca,reserve k _ a 0 args.count fits limit (by omega),ra,by rw [if_neg legal];rwa [if_neg legal] at done⟩
end CommitGolfCandidate.Layout2.Cap
