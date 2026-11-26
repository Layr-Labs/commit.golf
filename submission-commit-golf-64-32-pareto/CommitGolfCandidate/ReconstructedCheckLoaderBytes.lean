import CommitGolfCandidate.ReconstructedCheckLoader

namespace CommitGolfCandidate.Reconstruction.CheckLoader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 CheckRecordABI
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000
attribute [local irreducible] ArtifactEncoding.decode

private theorem digit (bs : Proof) (i : Nat) :
    (bs[i]?.getD 0).toNat=(Wire.unpackBytes bs/256^i)%256 := by
  induction bs generalizing i with
  | nil => simp [Wire.unpackBytes]
  | cons b bs ih =>
    cases i with
    | zero => simp [Wire.unpackBytes,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt b.isLt]
    | succ i =>
      rw [List.getElem?_cons_succ,ih,Wire.unpackBytes,pow_succ',←Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt b.isLt,Nat.zero_add]

private theorem proofWord (bs : Proof) (i : Nat) :
    (∑ b ∈ Finset.range 8, (bs[8*i+b]?.getD 0).toNat*2^(8*b))=HonestStream.word (Wire.unpackBytes bs) i := by
  let n := Wire.unpackBytes bs / 2^(64*i)
  have part (b : Nat) : (bs[8*i+b]?.getD 0).toNat=(n/2^(8*b))%256 := by
    rw [digit];unfold n;rw [Nat.div_div_eq_div_mul]
    have pw : 256^(8*i+b)=2^(64*i)*2^(8*b) := by
      rw [←pow_add,show 64*i+8*b=8*(8*i+b) by omega,pow_mul];rfl
    rw [pw]
  simp_rw [part]
  unfold HonestStream.word;rw [Nat.shiftRight_eq_div_pow]
  change _=n%2^64
  norm_num [Finset.sum_range_succ];omega

private theorem proofByte (input : CheckInput) (k : Nat) (small : k<8800000000) :
    inputByte Artifact.submission .check input (10334769248+k)=input.proof[k]?.getD 0 := by
  let n := input.positions.card
  have bound := positions_card_bound input.positions
  have outsideRoot : ¬(4294971392≤10334769248+k ∧ 10334769248+k<4294971424) := by omega
  have outsideIndices : ¬(5905584160≤10334769248+k ∧ 10334769248+k<5905584160+8*n) := by dsimp [n];omega
  have outsideValues : ¬(6039801952≤10334769248+k ∧ 10334769248+k<6039801952+256*n) := by dsimp [n];omega
  dsimp only [n] at outsideIndices outsideValues
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,valuesBuffer,
    Finset.length_sort,Finset.card_attach,show Artifact.submission.layout.commitment=4294971392 from rfl,
    show Artifact.submission.layout.indices=5905584160 from rfl,show Artifact.submission.layout.values=6039801952 from rfl,
    show Artifact.submission.layout.proof=10334769248 from rfl,show (DIGEST_BITS+7)/8=32 by decide,
    show LEAF_SIZE/8=256 by decide,show 4294971392+32=4294971424 by decide,
    outsideRoot,outsideIndices,outsideValues,decide_false]
  by_cases h : k < input.proof.length
  · have inside : 10334769248≤10334769248+k ∧ 10334769248+k<10334769248+input.proof.length := by omega
    simp only [inside,and_self,decide_true,ite_true];change input.proof[10334769248+k-10334769248]?.getD 0=_
    rw [Nat.add_sub_cancel_left]
  · have outside : ¬(10334769248≤10334769248+k ∧ 10334769248+k<10334769248+input.proof.length) := by omega
    simp only [outside,decide_false,List.find?_nil,image_base,ite_eq_right (by omega : ¬68719475728≤10334769248+k),
      List.getElem?_eq_none (by omega : input.proof.length≤k),Option.getD_none]

theorem stream (input : CheckInput) : CheckLayout.StreamMemory (initial input) (Wire.unpackBytes input.proof) := by
  intro i hi
  change (initial input).getMem (W (10334769248+8*i))=W _
  rw [initial,initial_input_word Artifact.submission .check input _ (by omega)]
  apply congrArg (BitVec.ofNat 64)
  rw [←proofWord]
  apply Finset.sum_congr rfl
  intro b hb
  have sm := Finset.mem_range.mp hb
  rw [Nat.add_assoc,proofByte _ _ (by omega)]

end CommitGolfCandidate.Reconstruction.CheckLoader
