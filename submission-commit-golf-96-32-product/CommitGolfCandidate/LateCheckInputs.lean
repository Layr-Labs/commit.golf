import CommitGolfCandidate.LateCheckSound
import CommitGolfCandidate.LateOpenWrites
import CommitGolfCandidate.LateOpenControl
import CommitGolfCandidate.LateMemoryStep

namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt indexBase proofBase)

def valueBase := 7784632352
def rootBase := 4294971392
def initial (input : CheckInput) := submission.initialState .check input
private def cb (x : CheckInput) := fixedBuffer rootBase x.commitment
private def ib (x : CheckInput) := positionsBuffer indexBase x.positions
private def vb (x : CheckInput) := valuesBuffer valueBase x.positions x.values
private def pb (x : CheckInput) : InputBuffer := ⟨proofBase,x.proof.length,fun j => x.proof[j]?.getD 0⟩

private def hits (a : Nat) (b : InputBuffer) := b.address≤a ∧ a<b.address+b.length
private instance (a : Nat) (b : InputBuffer) : Decidable (hits a b) := inferInstanceAs (Decidable (_ ∧ _))

private theorem byte_selected (x : CheckInput) (a : Nat) (b : InputBuffer) (hi : a<2^64)
    (found : [cb x,ib x,vb x,pb x].find? (fun b => decide (hits a b))=some b) :
    Open.byteAt (initial x) a=b.byteAt (a-b.address) := by
  apply (initial_input_byte submission .check x a hi).trans
  unfold inputByte
  change (match [cb x,ib x,vb x,pb x].find? (fun b => decide (hits a b)) with
    | some q => q.byteAt (a-q.address) | none => _) = _
  rw [found]

private theorem sizes (x : CheckInput) :
    (cb x).address+(cb x).length≤ indexBase ∧ (ib x).address+(ib x).length≤valueBase ∧
      (vb x).address+(vb x).length≤proofBase := by
  have n := Finset.card_le_univ x.positions
  have k : x.positions.card≤LENGTH := by simpa using n
  change x.positions.card≤16777216 at k
  constructor
  · change 4294971392+32≤7650414624;decide
  · simp only [ib,positionsBuffer,Finset.length_sort,vb,valuesBuffer,Finset.card_attach,LEAF_SIZE,
      indexBase,proofBase,valueBase];omega

private theorem ib_byte (x : CheckInput) (a : Nat) (inBuf : hits a (ib x)) (hi : a<2^64) :
    Open.byteAt (initial x) a=(ib x).byteAt (a-indexBase) := by
  have skip : ¬hits a (cb x) := by
    intro h;have := (sizes x).1;have lo : indexBase≤a := inBuf.1;have := h.2;omega
  exact byte_selected x a _ hi (by simp [List.find?_cons,skip,inBuf])

private theorem vb_byte (x : CheckInput) (a : Nat) (inBuf : hits a (vb x)) (hi : a<2^64) :
    Open.byteAt (initial x) a=(vb x).byteAt (a-valueBase) := by
  have lo : valueBase≤a := inBuf.1
  have skip : ¬hits a (cb x) := by
    intro h
    have e : indexBase≤valueBase := by decide
    exact (Nat.not_lt_of_ge ((sizes x).1.trans (e.trans lo))) h.2
  have skip' : ¬hits a (ib x) := by intro h;have := (sizes x).2.1;have := h.2;omega
  exact byte_selected x a _ hi (by simp [List.find?_cons,skip,skip',inBuf])

theorem proof_byte (x : CheckInput) (j : Nat) (lt : j<x.proof.length) (hi : proofBase+j<2^64) :
    Open.byteAt (initial x) (proofBase+j)=x.proof[j] := by
  let a := proofBase+j
  have lo : proofBase≤a := Nat.le_add_right .. 
  have bound1 : indexBase≤proofBase := by decide
  have bound2 : valueBase≤proofBase := by decide
  have skip : ¬hits a (cb x) := by intro h;have := (sizes x).1;have := h.2;omega
  have skip' : ¬hits a (ib x) := by intro h;have := (sizes x).2.1;have := h.2;omega
  have skip'' : ¬hits a (vb x) := by intro h;have := (sizes x).2.2;have := h.2;omega
  have yes : hits a (pb x) := ⟨lo, Nat.add_lt_add_left lt _⟩
  have e := byte_selected x a (pb x) hi (by simp [List.find?_cons,skip,skip',skip'',yes])
  simpa only [a,pb,Nat.add_sub_cancel_left,List.getElem?_eq_getElem lt,Option.getD_some] using e

theorem loaded_root (x : CheckInput) : readBuffer (initial x) rootBase 32=x.commitment := by
  have data (j : Nat) (hi : j<32) : (initial x).getByte (BitVec.ofNat 64 (rootBase+j))=x.commitment.extractLsb' (8*(0+j)) 8 := by
    have hit : hits (rootBase+j) (cb x) := ⟨Nat.le_add_right ..,Nat.add_lt_add_left hi _⟩
    have e := byte_selected x (rootBase+j) (cb x) (by unfold rootBase;omega) (by simp [List.find?_cons,hit])
    simpa only [Open.byteAt,cb,fixedBuffer,Nat.add_sub_cancel_left,Nat.zero_add] using e
  exact (read_serialized_slice _ _ _ 0 32 data).trans BitVec.extractLsb'_eq_self

theorem loaded_index (x : CheckInput) (r : Nat) (hr : r<x.positions.card) :
    wordAt (initial x) (indexBase+8*r) = W (recordIndex x.positions r).val := by
  let a := indexBase+8*r
  let i := recordIndex x.positions r
  have kh : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at kh
  have data (j : Nat) (hj : j<8) :
      (initial x).getByte (BitVec.ofNat 64 (a+j))=(W i.val).extractLsb' (8*(0+j)) 8 := by
    have inBuf : hits (a+j) (ib x) := by
      change indexBase≤a+j ∧ a+j< indexBase+8*(x.positions.sort (·≤·)).length
      rw [Finset.length_sort];unfold a;omega
    have read := ib_byte x (a+j) inBuf (by unfold a indexBase;omega)
    apply read.trans
    dsimp only [ib,positionsBuffer]
    rw [show (a+j-indexBase)/8=r by dsimp [a];omega,show (a+j-indexBase)%8=j by dsimp [a];omega]
    have fit : r<(x.positions.sort (·≤·)).length := by simpa using hr
    rw [List.getElem?_eq_getElem fit]
    have ix : i=(x.positions.sort (·≤·))[r] := by simp only [i,recordIndex,List.getElem?_eq_getElem fit,Option.getD_some]
    rw [ix]
    have small := ((x.positions.sort (·≤·))[r]).isLt
    change _ < 16777216 at small
    simp only [W,Nat.zero_add,BitVec.extractLsb',BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega :
      ((x.positions.sort (·≤·))[r]).val < 2^64),Nat.shiftRight_eq_div_pow]
  have read := (read_serialized_slice _ _ _ 0 8 data).trans BitVec.extractLsb'_eq_self
  have take := read_buffer_slice (initial x) a 32 0 8 (by decide)
  have w := read_digest_word (initial x) a 0 (by unfold a indexBase;omega) (by decide)
  exact w.symm.trans (take.trans read)

theorem loaded_value (x : CheckInput) (r : Nat) (hr : r<x.positions.card) :
    readBuffer (initial x) (valueBase+256*r) 256=recordValue x r := by
  let a := valueBase+256*r
  let xs := x.positions.attach.sort (fun i j => i.val ≤ j.val)
  have len : xs.length=x.positions.card := by simp [xs]
  have fit : r<xs.length := by omega
  have kh : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at kh
  have bytes (j : Nat) (hj : j<256) :
      (initial x).getByte (BitVec.ofNat 64 (a+j)) = (recordValue x r).extractLsb' (8*(0+j)) 8 := by
    have hit : hits (a+j) (vb x) := by
      change valueBase≤a+j ∧ a+j<valueBase+256*xs.length;unfold a;omega
    apply (vb_byte x (a+j) hit (by unfold a valueBase;omega)).trans
    dsimp only [vb,valuesBuffer]
    simp only [show LEAF_SIZE / 8 = 256 from rfl]
    rw [show (a+j-valueBase)/256=r by dsimp [a];omega,show (a+j-valueBase)%256=j by dsimp [a];omega]
    unfold recordValue
    rw [List.getElem?_eq_getElem fit];simp
  exact (read_serialized_slice _ _ _ 0 256 bytes).trans BitVec.extractLsb'_eq_self

end CommitGolfCandidate.Late.Check
