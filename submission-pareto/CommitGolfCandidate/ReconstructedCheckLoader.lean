import CommitGolfCandidate.ReconstructedCheckRecordABI
import CommitGolfCandidate.ReconstructedHonestInputs

namespace CommitGolfCandidate.Reconstruction.CheckLoader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CheckRecordABI
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode

theorem positions_card_bound (ps : Positions) : ps.card≤16777216 := by
  change ps.card≤2^24
  simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ ps

def initial (input : CheckInput) := Artifact.submission.initialState .check input

theorem image_base : dataBase (Artifact.submission.image .check)=68719475728 := by
  change 16*((2^36-(ArtifactEncoding.decode 8 Artifact.checkData).length)/16)=_
  rw [ArtifactEncoding.length_decode];decide

theorem check_input_commitment (input : CheckInput) :
    readBuffer (Artifact.submission.initialState .check input) Artifact.submission.layout.commitment 32 =
      input.commitment := by
  have decoded := read_serialized_slice (Artifact.submission.initialState .check input) input.commitment
    Artifact.submission.layout.commitment 0 32 (by
      intro j hj
      rw [initial_input_byte Artifact.submission .check input _ (by change 4294971392+j < 2^64; omega)]
      have selected : Artifact.submission.layout.commitment ≤ Artifact.submission.layout.commitment+j ∧
          Artifact.submission.layout.commitment+j < Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8 := by
        change _ ≤ _ ∧ _ < Artifact.submission.layout.commitment+32
        omega
      simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
        selected, and_self, decide_true, Nat.add_sub_cancel_left, Nat.zero_add])
  exact decoded.trans BitVec.extractLsb'_eq_self


theorem check_input_value_byte (input : CheckInput) (ordinal offset : Nat)
    (present : ordinal < input.positions.card) (inside : offset < 256) :
    (Artifact.submission.initialState .check input).getByte
      (BitVec.ofNat 64 (Artifact.submission.layout.values+256*ordinal+offset)) =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))).extractLsb' (8*offset) 8 := by
  have cardinal := positions_card_bound input.positions
  rw [initial_input_byte Artifact.submission .check input _ (by
    change 6039801952+256*ordinal+offset < 2^64
    omega)]
  have outsideRoot : ¬ (Artifact.submission.layout.commitment ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 6039801952+256*ordinal+offset ∧ 6039801952+256*ordinal+offset < 4294971424)
    omega
  have outsideIndices : ¬ (Artifact.submission.layout.indices ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 6039801952+256*ordinal+offset ∧
      6039801952+256*ordinal+offset < 5905584160+8*input.positions.card)
    omega
  have selected : Artifact.submission.layout.values ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.values+(LEAF_SIZE/8)*input.positions.card := by
    change _ ≤ _ ∧ _ < Artifact.submission.layout.values+256*input.positions.card
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, decide_false, selected, and_self, decide_true]
  have quotient : (Artifact.submission.layout.values+256*ordinal+offset-Artifact.submission.layout.values)/(LEAF_SIZE/8) = ordinal := by
    change _ / 256 = _
    omega
  have remainder : (Artifact.submission.layout.values+256*ordinal+offset-Artifact.submission.layout.values)%(LEAF_SIZE/8) = offset := by
    change _ % 256 = _
    omega
  rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]


theorem root (input : CheckInput) (j : Fin 4) :
    (initial input).getMem (W (4294971392+8*j.val))=input.commitment.extractLsb' (64*j.val) 64 := by
  have h := read_digest_word (initial input) 4294971392 j.val (by decide) j.isLt
  have c : readBuffer (initial input) 4294971392 32=input.commitment := check_input_commitment input
  rw [c] at h;exact h.symm

private theorem readWord (s : MachineState) (a : Nat) (ha : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  have part := read_buffer_slice s a 32 0 8 (by decide)
  have word := read_digest_word s a 0 ha (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using part.symm.trans word

theorem value (input : CheckInput) (i : Fin input.positions.card) (j : Fin 32) :
    (initial input).getMem (wordAddress (CheckEntry.valuesBase+32*i.val+j.val))=entryWords (input.values (position input i)) j := by
  let a := 6039801952+256*i.val+8*j.val
  have eq : wordAddress (CheckEntry.valuesBase+32*i.val+j.val)=BitVec.ofNat 64 a := by
    unfold wordAddress a CheckEntry.valuesBase;congr 1;omega
  rw [eq,←readWord _ a (by unfold a;omega)]
  have word := read_serialized_slice (initial input) (input.values (position input i)) a (8*j.val) 8 (by
    intro b hb
    have sm := j.isLt
    have v := check_input_value_byte input i.val (8*j.val+b) i.isLt (by omega)
    change (initial input).getByte (W (6039801952+256*i.val+(8*j.val+b)))=_ at v
    exact (congrArg (fun x => (initial input).getByte (W x)) (by unfold a;omega : a+b=6039801952+256*i.val+(8*j.val+b))).trans v)
  change readBuffer _ a 8=(input.values (position input i)).extractLsb' (64*j.val) 64
  rw [show 64*j.val=8*(8*j.val) by omega];exact word

theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped


theorem sorted (input : CheckInput) (i : Fin input.positions.card) :
    (position input i).val=(input.positions.sort (·≤·))[i.val]'(by simpa using i.isLt) := by
  have same := congrArg (fun list : List Index => list[i.val]?) (sorted_value_indices input.positions)
  have ha : i.val<(input.positions.attach.sort (fun a b => a.val≤b.val)).length := by simpa using i.isLt
  have hb : i.val<(input.positions.sort (·≤·)).length := by simpa using i.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.map_some,Option.some.injEq] at same
  exact same

theorem index (input : CheckInput) (ord : Fin input.positions.card) :
    (initial input).getMem (wordAddress (CheckEntry.indexBase+ord.val))=W (position input ord).val.val := by
  let ps := input.positions
  let i := ord.val
  have hi : i<ps.card := ord.isLt
  have bound := positions_card_bound ps
  have eq : wordAddress (CheckEntry.indexBase+i)=W (5905584160+8*i) := by unfold wordAddress CheckEntry.indexBase;congr 1;omega
  change (initial input).getMem (wordAddress (CheckEntry.indexBase+i))=_
  rw [eq,sorted,initial,initial_input_word Artifact.submission .check input _ (by omega)]
  let value := (ps.sort (· ≤ ·))[i]'(by simpa using hi)
  have bytes (j : Nat) (hj : j < 8) : inputByte Artifact.submission .check input (5905584160+8*i+j) =
      BitVec.ofNat 8 (value.val/2^(8*j)) := by
    have tree : Artifact.submission.layout.commitment=4294971392 := rfl
    have idx : Artifact.submission.layout.indices=5905584160 := rfl
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,tree,idx,Finset.length_sort]
    simp only [show ¬(4294971392 ≤ 5905584160+8*i+j ∧ 5905584160+8*i+j < 4294971392+(DIGEST_BITS+7)/8) by change ¬(_ ≤ _ ∧ 5905584160+8*i+j < 4294971424);omega,
      show 5905584160 ≤ 5905584160+8*i+j ∧ 5905584160+8*i+j < 5905584160+8*input.positions.card by change _ ∧ _<5905584160+8*ps.card;omega,
      decide_false,decide_true,and_self]
    rw [show (5905584160+8*i+j-5905584160)/8 = i by omega, show (5905584160+8*i+j-5905584160)%8=j by omega,
      List.getElem?_eq_getElem (by simpa using hi)]
  have swapped : (∑ j ∈ Finset.range 8, (inputByte Artifact.submission .check input (5905584160+8*i+j)).toNat * 2^(8*j)) =
      ∑ j ∈ Finset.range 8, (BitVec.ofNat 8 (value.val/2^(8*j))).toNat*2^(8*j) := by
    apply Finset.sum_congr rfl
    intro j hj; rw [bytes j (Finset.mem_range.mp hj)]
  rw [swapped]
  change BitVec.ofNat 64 _ = BitVec.ofNat 64 value.val
  congr 1
  have small : value.val < 16777216 := value.isLt
  norm_num [Finset.sum_range_succ,BitVec.toNat_ofNat]
  omega

end CommitGolfCandidate.Reconstruction.CheckLoader
