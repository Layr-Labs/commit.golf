import CommitGolfCandidate.TruncOpenInput
import CommitGolfCandidate.PairPrivacy
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 220000
attribute [local irreducible] Wire.packedEnd PairCap.suffixState openingPositionState openingInitializedState

def publicProof (ps : Positions) (old : Proof) : Proof :=
  if ps.card=BATCH then pack (PairCap.convert ps old) else old

theorem stageState (td : BitVec (8*submission.sizes.trapdoor)) (ps : Positions) :
    (Open.openingResult td ps).state=(if ps.card=BATCH then Wire.packedEnd (PairCap.openingResult td ps).state
                                    else (PairCap.openingResult td ps).state) := by
  have init : submission.initialState .opening (td,ps)=PairCap.submission.initialState .opening (td,ps) := rfl
  by_cases hb : ps.card=BATCH
  · have ne : ps.card≠0 := by rw [hb];decide
    simp only [Open.openingResult,Open.openingFinalState,PairCap.openingResult,PairCap.openingFinalState,
      if_pos hb,if_neg ne,init]
  · simp only [Open.openingResult,Open.openingFinalState,PairCap.openingResult,PairCap.openingFinalState,if_neg hb,init]

private theorem readValid (c : Submission) (x : Execution) (ok : c.openingSucceeded x=true) :
    c.readProof x=(List.range (x.state.getReg .x11).toNat).map (fun j=>x.state.getByte (BitVec.ofNat 64 (c.layout.proof+j))) := by
  unfold Submission.readProof;rw [if_pos ok]

theorem packedProof (law : Wire.PackedBytes) (td : BitVec (8*submission.sizes.trapdoor)) (ps : Positions)
    (hb : ps.card=BATCH) :
    submission.readProof (Open.openingResult td ps)=pack (PairCap.submission.readProof (PairCap.openingResult td ps)) := by
  let x:=PairCap.openingResult td ps
  have oldN : (x.state.getReg .x11).toNat=71680 := (PairCap.opening_result_length td ps).trans (by simp [PairCap.proofBytes,hb])
  have newN : ((Open.openingResult td ps).state.getReg .x11).toNat=68096 := (Open.opening_result_length td ps).trans (by simp [Open.proofBytes,hb])
  have states:=(stageState td ps);rw [if_pos hb] at states
  rw [readValid _ _ (Open.opening_result_succeeded td ps),readValid _ _ (PairCap.opening_result_succeeded td ps)]
  unfold pack
  rw [newN,show ((PairCap.openingResult td ps).state.getReg .x11).toNat=71680 from oldN]
  apply List.map_congr_left
  intro i hi
  have bi:=List.mem_range.mp hi
  have inside:=(widen_narrow i bi).1
  rw [List.getElem?_eq_getElem (by simpa using inside),Option.getD_some]
  simp only [List.getElem_map,List.getElem_range,states]
  exact law x.state i bi

theorem outputConversion (law : Wire.PackedBytes) (s : MachineState) (ps : Positions) :
    let td:=readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (Open.openingResult td ps)=publicProof ps
      (CommitGolfCandidate.submission.readProof (CommitGolfCandidate.openingResult td ps)) := by
  dsimp only
  let td:=readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
  have baseEq : PairCap.submission.readProof (PairCap.openingResult td ps)=PairCap.convert ps
      (CommitGolfCandidate.submission.readProof (CommitGolfCandidate.openingResult td ps)) := PairCap.honestConversion s ps
  by_cases hb : ps.card=BATCH
  · rw [publicProof,if_pos hb,packedProof law td ps hb,baseEq]
  · rw [publicProof,if_neg hb,PairCap.convert_normal hb] at *
    trans PairCap.submission.readProof (PairCap.openingResult td ps)
    · have state:=stageState td ps;rw [if_neg hb] at state
      change submission.readProof (Open.openingResult td ps)=PairCap.submission.readProof (PairCap.openingResult td ps)
      rw [readValid _ _ (Open.opening_result_succeeded td ps),readValid _ _ (PairCap.opening_result_succeeded td ps),state]
      rfl
    · exact baseEq
end CommitGolfCandidate.Trunc
