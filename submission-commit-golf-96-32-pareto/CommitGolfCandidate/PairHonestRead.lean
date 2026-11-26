import CommitGolfCandidate.PairPayload
import CommitGolfCandidate.PairBatchModel
import CommitGolfCandidate.HonestRecords
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 300000
attribute [local irreducible] readBuffer openingResult

abbrev saved (s : MachineState) := readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
def honestInput (s : MachineState) (m : Message) (ps : Positions) : CheckInput :=
  ⟨readBuffer s submission.layout.commitment 32,ps,m.restrict ps,submission.readProof (openingResult (saved s) ps)⟩

theorem parsedBlock (s : MachineState) (m : Message) (ps : Positions) (hb : ps.card=BATCH)
    (off : Nat) (inside : off+32≤71680) :
    readBuffer (CommitGolfCandidate.submission.initialState .check (honestInput s m ps)) (10871640096+off) 32 =
      readBuffer (openingResult (saved s) ps).state (10871640096+off) 32 := by
  let input := honestInput s m ps
  have len : input.proof.length=71680 :=
    (opening_proof_length (saved s) ps).trans (by simp [proofBytes,hb])
  have v : input.proof.length ≤ CommitGolfCandidate.submission.sizes.proof := by rw [len]; decide
  have load := check_input_proof_digest input v off (by omega)
  change readBuffer (CommitGolfCandidate.submission.initialState .check input)
    (CommitGolfCandidate.submission.layout.proof+off) 32 = _
  rw [load]
  unfold readBuffer
  apply congrArg (BitVec.ofNat 256)
  apply Finset.sum_congr rfl
  intro j hj
  have b : off+j < input.proof.length := by have := Finset.mem_range.mp hj; omega
  rw [List.getElem?_eq_getElem b,Option.getD_some]
  simp only [input,honestInput,Submission.readProof,opening_result_succeeded (saved s) ps,if_true,
    List.getElem_map,List.getElem_range]
  rw [Nat.add_assoc]; rfl

theorem parsedSalt (s : MachineState) (m : Message) (ps : Positions) (hb : ps.card=BATCH)
    (off : Nat) (inside : off+16≤71680) :
    readBuffer (CommitGolfCandidate.submission.initialState .check (honestInput s m ps)) (10871640096+off) 16 =
      readBuffer (openingResult (saved s) ps).state (10871640096+off) 16 := by
  let input := honestInput s m ps
  have len : input.proof.length=71680 :=
    (opening_proof_length (saved s) ps).trans (by simp [proofBytes,hb])
  have v : input.proof.length ≤ CommitGolfCandidate.submission.sizes.proof := by rw [len]; decide
  have load := check_input_proof_salt input v off (by omega)
  change readBuffer (CommitGolfCandidate.submission.initialState .check input)
    (CommitGolfCandidate.submission.layout.proof+off) 16 = _
  rw [load]
  unfold readBuffer
  apply congrArg (BitVec.ofNat 128)
  apply Finset.sum_congr rfl
  intro j hj
  have b : off+j < input.proof.length := by have := Finset.mem_range.mp hj; omega
  rw [List.getElem?_eq_getElem b,Option.getD_some]
  simp only [input,honestInput,Submission.readProof,opening_result_succeeded (saved s) ps,if_true,
    List.getElem_map,List.getElem_range]
  rw [Nat.add_assoc]; rfl

abbrev hnode (s : MachineState) (i : Nat) := readBuffer s (4294971424+heapOffset i) 32

theorem honestLower (o : Oracle) (s : MachineState) (m : Message) (ps : Positions) (ok : CommittedState o m s)
    (hb : ps.card=BATCH) (r : Nat) (hr : r<128) :
    lowerHash o.compression (honestInput s m ps) r = hnode s (256+openingIndex ps r/65536) := by
  let input := honestInput s m ps
  let i := recordIndex input r
  have present : r<ps.card := by rw [hb]; exact hr
  have vv : recordValue input r = m i := by
    unfold recordValue
    rw [dif_pos (show r < input.positions.card from present)]
    apply congrArg m
    apply Fin.ext
    exact sorted_value_index ps r present
  have raw := batchRecords s ps hb r hr
  have salt : batchSalt input r = readBuffer s (5905584160+16*i.val) 16 := by
    unfold batchSalt
    rw [parsedSalt s m ps hb (528*r) (by omega)]
    exact raw.1
  have sib (l : Nat) (bl : l<16) :
      lowerSibling input r l = hnode s (((LENGTH+i.val)/2^l) ^^^ 1) := by
    unfold lowerSibling
    rw [show 10871640096+528*r+16+32*l=10871640096+(528*r+16+32*l) by omega,
      parsedBlock s m ps hb _ (by omega)]
    rw [show 10871640096+(528*r+16+32*l) = 10871640096+528*r+16+32*l by omega]
    exact raw.2 l bl
  have pp : recordPathPrefix 16 i (lowerSibling input r) = heapPath (hnode s) (LENGTH+i.val) 16 := by
    apply List.ext_getElem
    · rw [record_path_prefix_length,heap_path_length]
    · intro l h1 h2
      have bl : l<16 := by simpa only [record_path_prefix_length] using h1
      rw [heap_path_get _ _ _ _ bl]
      simp only [recordPathPrefix,List.getElem_map,List.getElem_range]
      exact Prod.ext ((heap_leaf_direction 24 i.val l i.isLt (by omega)).symm) (sib l bl)
  change recordAncestor _ 16 _ _ i _ = _
  unfold recordAncestor
  rw [vv,salt,pp,← ok.2.2 i]
  have b : i.val<16777216 := i.isLt
  have calcHeap := reconstruct_heap_ancestor o.compression (hnode s) LENGTH ok.2.1 16 (LENGTH+i.val)
    (by change 16777216+i.val<2*16777216; omega) (by change 65536≤16777216+i.val; omega)
  apply calcHeap.trans; apply congrArg (hnode s)
  change (16777216+i.val)/65536=256+i.val/65536; omega

end CommitGolfCandidate.PairCap
