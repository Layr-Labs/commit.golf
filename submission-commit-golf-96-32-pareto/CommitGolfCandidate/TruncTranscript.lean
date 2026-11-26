import CommitGolfCandidate.TruncOutputFormat
import CommitGolfCandidate.TruncDistribution
import CommitGolfCandidate.TruncHidingSecurity
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec OracleComp.DeferredSampling
local instance {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000
set_option maxHeartbeats 250000

def transcript (m : Message) (ps : Positions) : OracleComp World (Commitment×Proof) := do
  let pair←submission.scheme.commit m
  let proof←submission.scheme.opening pair.2 ps
  pure (pair.1,proof)

attribute [local irreducible] commitFinalResult readBuffer saltedHeap referenceOpening referenceTranscript publicProof

private theorem stateTranscript (bytes : Wire.PackedBytes) (o : Oracle) (m : Message) (s : MachineState) (salt : Index→Salt)
    (ok : CommittedState o m s) (salts : ∀ i,readBuffer s (5905584160+16*i.val) 16=salt i) (ps : Positions) :
    let td:=readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    let ref:=referenceTranscript o.compression m salt ps
    (readBuffer s submission.layout.commitment 32,submission.readProof (Open.openingResult td ps))=(ref.1,publicProof ps ref.2) := by
  unfold referenceTranscript
  apply Prod.ext
  · exact committed_root_reference o m s ok salt salts
  · exact (outputConversion bytes s ps).trans (congrArg (publicProof ps) (opening_reference_bytes o m s ok salt salts ps))

private theorem finalTranscript (bytes : Wire.PackedBytes) (o : Oracle) (m : Message) {bits : Nat}
    (a : BitVec bits) (width : bits=128*LENGTH) (ps : Positions) :
    let s:=(commitFinalResult o m a).1.state
    let td:=readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    let ref:=referenceTranscript o.compression m (fun i=>a.extractLsb' (128*i.val) 128) ps
    (readBuffer s submission.layout.commitment 32,submission.readProof (Open.openingResult td ps))=
      (ref.1,publicProof ps ref.2) := by
  have h:=commit_final_origin o m a width
  exact stateTranscript bytes o m (commitFinalResult o m a).1.state (fun i=>a.extractLsb' (128*i.val) 128) h.1 h.2 ps

private theorem afterMap (o : Oracle) {A B C : Type} (c : OracleComp World A) (f : A→B) (g : B→ProbComp C) :
    (fixedOracleRun o (f <$> c) >>= g)=(o.run c >>= fun x=>g (f x.1)) := by
  rw [fixed_oracle_run_map,bind_map_left]
  unfold fixedOracleRun;rw [bind_map_left]

theorem transcriptRun (packRun : Wire.PackRun) (bytes : Wire.PackedBytes) (o : Oracle) (m : Message) (ps : Positions) :
    fixedOracleRun o (transcript m ps) =
      (commitSaltCoins m >>= fun a=>
        let ref:=referenceTranscript o.compression m (fun i=>a.extractLsb' (128*i.val) 128) ps
        pure (ref.1,publicProof ps ref.2)) := by
  have finish (root : Commitment) (td : submission.scheme.Trapdoor) :
      fixedOracleRun o (do let p←submission.scheme.opening td ps;pure (root,p))=
        pure (root,submission.readProof (Open.openingResult td ps)) := by
    erw [Open.opening_scheme_execution packRun,pure_bind,fixed_oracle_run_pure]
  unfold transcript;rw [fixed_oracle_run_bind];simp only [finish]
  let g (value : Commitment × BitVec (8*submission.sizes.trapdoor)) : ProbComp (Commitment×Proof) :=
    pure (value.1,submission.readProof (Open.openingResult value.2 ps))
  change (fixedOracleRun o (submission.readCommit <$> submission.run .commit (m : Input submission.sizes .commit)) >>= g)=_
  apply (afterMap o (submission.run .commit (m : Input submission.sizes .commit)) submission.readCommit g).trans
  rw [commit_run_distribution o m,bind_assoc]
  apply bind_congr;intro a;simp only [pure_bind]
  exact congrArg (fun pair : Commitment×Proof=>(pure pair : ProbComp _)) (finalTranscript bytes o m a (commit_salt_width m) ps)

end CommitGolfCandidate.Trunc
