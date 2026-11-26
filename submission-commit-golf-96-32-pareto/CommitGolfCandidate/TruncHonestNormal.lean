import CommitGolfCandidate.TruncCommitTruth
import CommitGolfCandidate.TruncAuthentication
import CommitGolfCandidate.TruncOutputFormat
import CommitGolfCandidate.HonestRecords
import CommitGolfCandidate.PairHonestRead
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 150000
attribute [local irreducible] readBuffer commitRootCopyState

def normalInput (s : MachineState) (m : Message) (ps : Positions) : CheckInput :=
  let base:=CommitGolfCandidate.submission
  let td:=readBuffer s base.layout.trapdoor base.sizes.trapdoor
  ⟨readBuffer s base.layout.commitment 32,ps,m.restrict ps,base.readProof (CommitGolfCandidate.openingResult td ps)⟩

theorem honestNormal (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s) (ps : Positions)
    (mode : ps.card≠BATCH) (n : Nat) (hn : n<ps.card) :
    let i:=normalInput s m ps
    recordRoot o.compression (recordValue i n) (recordSalt i n) (recordIndex i n) (normalSibling i n)=i.commitment := by
  let i:=normalInput s m ps
  let ix:=recordIndex i n
  let td:=readBuffer s CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor
  let root:=readBuffer s CommitGolfCandidate.submission.layout.commitment 32
  have val : recordValue i n=m ix := by
    unfold recordValue;rw [dif_pos (show n < i.positions.card from hn)]
    apply congrArg m;apply Fin.ext;exact sorted_value_index ps n hn
  have len : openingProofBytes ps.card=784*ps.card:=if_neg mode
  have rs:=opening_output_records s ps mode n hn
  have salt : recordSalt i n=readBuffer s (5905584160+16*ix.val) 16 := by
    unfold recordSalt
    rw [if_neg (show i.positions.card≠BATCH from mode)]
    exact (check_opening_proof_salt td ps root (m.restrict ps) (784*n) (by rw [len];omega)).trans rs.1
  have path : recordPath ix (normalSibling i n)=heapPath (PairCap.hnode s) (LENGTH+ix.val) 24 := by
    apply List.ext_getElem
    · rw [record_path_length,heap_path_length]
    · intro j h1 h2
      have bound : j<24:=by simpa only [record_path_length] using h1
      rw [heap_path_get _ _ _ _ bound]
      simp only [recordPath,recordPathPrefix,List.getElem_map,List.getElem_range]
      apply Prod.ext ((heap_leaf_direction 24 ix.val j ix.isLt bound).symm)
      have parsed:=check_opening_proof_digest td ps root (m.restrict ps) (784*n+16+32*j) (by rw [len];omega)
      have addr : CommitGolfCandidate.submission.layout.proof+(784*n+16+32*j)=10871640096+784*n+16+32*j := by change 10871640096+_=_;omega
      rw [addr] at parsed
      exact parsed.trans (rs.2 j bound)
  change recordRoot _ _ _ ix _=_
  unfold recordRoot
  rw [val,salt,path,←ok.2.2 ix]
  exact (reconstruct_heap_root o.compression (PairCap.hnode s) 24 ix.val ix.isLt ok.2.1).trans ok.1.symm

end CommitGolfCandidate.Trunc
