import CommitGolfCandidate.Layout2Records
import CommitGolfCandidate.GroupOpenModel
import CommitGolfCandidate.Layout2Bytes

/-! Layout 2 opener: the record sources as trapdoor fields. Source byte `k` of record `j` (read from the loaded
state) is a byte of the position's salt (`k < 16`), of a quartet mate leaf (`16 ≤ k < 112`), of the level-0
node `trapdoorQuad` (`112 ≤ k < 144`), or of the heap sibling of level `(k-112)/32` (`144 ≤ k < 560`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open CommitGolfCandidate.Layout2Phase (recordSource)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem read_one (st : MachineState) (a : Nat) : readBuffer st a 1=st.getByte (BitVec.ofNat 64 a) := by
  unfold readBuffer
  simp

theorem input_byte (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (off : Nat) (inside : off<trapdoorBytes) :
    (s.initialState .opening (t, positions)).getByte (BitVec.ofNat 64 (trapdoorBase+off))=t.extractLsb' (8*off) 8 := by
  rw [← read_one]
  exact input_trapdoor_slice s layout t positions off 1 (by omega)

private theorem xor_low (n j : Nat) (small : j<4) : n ^^^ j=4*(n/4)+(n%4 ^^^ j) := by
  have g : (n ^^^ j)/2^2=n/2^2 := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : j >>> 2=0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt small
    simp [zero]
  have p : (n ^^^ j)%2^2=n%2^2 ^^^ j := by
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (show j<2^2 by omega)]
  have split := Nat.div_add_mod (n ^^^ j) (2^2)
  rw [g, p] at split
  simp only [show (2:Nat)^2=4 from rfl] at split
  omega

private theorem mate_slot (r m : Nat) (hr : r<4) (hm : m<3) :
    (32*r) ^^^ (32*(m+1))=32*(r ^^^ (m+1)) ∧ r ^^^ (m+1)<4 := by
  interval_cases r <;> interval_cases m <;> decide

/-- Salt bytes. -/
theorem src_salt (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (j k : Nat) (hk : k<16) :
    srcAt (s.initialState .opening (t, positions)) positions j k=
      (trapdoorSalt (s:=s) t (posAt positions j)).extractLsb' (8*k) 8 := by
  have hp := pos_at_lt positions j
  unfold srcAt recordSource Layout2Phase.sourceAddress
  rw [if_pos hk, show Layout2Phase.saltBase+16*(posAt positions j).val+k=
      trapdoorBase+(288*LENGTH+16*(posAt positions j).val+k) by
    unfold Layout2Phase.saltBase trapdoorBase LENGTH LOG_LENGTH; omega,
    input_byte s layout t positions _ (by unfold trapdoorBytes LENGTH LOG_LENGTH at *; omega)]
  unfold trapdoorSalt
  rw [ext_ext _ _ _ _ _ (by omega)]
  congr 1; omega

/-- Mate bytes: mate `m = (k-16)/32` is the leaf `pos xor (m+1)`. -/
theorem src_mate (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (j k : Nat) (lo : 16 ≤ k) (hk : k<112) :
    srcAt (s.initialState .opening (t, positions)) positions j k=
      (trapdoorLeaf (s:=s) t ((posAt positions j).val ^^^ ((k-16)/32+1))).extractLsb' (8*((k-16)%32)) 8 := by
  have hp := pos_at_lt positions j
  generalize hq : (posAt positions j).val=pos at hp ⊢
  have hm : (k-16)/32<3 := by omega
  obtain ⟨slot, small⟩ := mate_slot (pos%4) ((k-16)/32) (Nat.mod_lt _ (by decide)) hm
  have split := xor_low pos ((k-16)/32+1) (by omega)
  have q : (pos ^^^ ((k-16)/32+1))/4=pos/4 := by omega
  have r : (pos ^^^ ((k-16)/32+1))%4=pos%4 ^^^ ((k-16)/32+1) := by omega
  unfold srcAt recordSource Layout2Phase.sourceAddress
  rw [hq, if_neg (by omega), if_pos hk, slot,
    show Layout2Phase.slotBase+584+1024*(pos/4)+32*(pos%4 ^^^ ((k-16)/32+1))+(k-16)%32=
      trapdoorBase+(32*LENGTH+512+1024*(pos/4)+72+32*(pos%4 ^^^ ((k-16)/32+1))+(k-16)%32) by
    unfold Layout2Phase.slotBase trapdoorBase LENGTH LOG_LENGTH; omega,
    input_byte s layout t positions _ (by unfold trapdoorBytes LENGTH LOG_LENGTH at *; omega)]
  unfold trapdoorLeaf
  rw [ext_ext _ _ _ _ _ (by omega), q, r]
  congr 1; omega

/-- Level-0 bytes: the quartet pointer's node. -/
theorem src_quad (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (j k : Nat) (lo : 112 ≤ k) (hk : k<144) :
    srcAt (s.initialState .opening (t, positions)) positions j k=
      (trapdoorQuad (s:=s) t (posAt positions j)).extractLsb' (8*(k-112)) 8 := by
  have hp := pos_at_lt positions j
  have quad := quad_address_inside (posAt positions j).val (by unfold LENGTH LOG_LENGTH; omega)
  unfold srcAt recordSource Layout2Phase.sourceAddress
  rw [if_neg (by omega), if_neg (by omega), if_pos hk,
    show quadAddress (posAt positions j).val+(k-112)=
      trapdoorBase+(quadAddress (posAt positions j).val-trapdoorBase+(k-112)) by omega,
    input_byte s layout t positions _ (by
      have : nonceBase+16*LENGTH=trapdoorBase+trapdoorBytes := by unfold nonceBase trapdoorBytes; omega
      unfold LENGTH LOG_LENGTH at this; omega)]
  unfold trapdoorQuad
  rw [ext_ext _ _ _ _ _ (by omega)]
  congr 1; omega

/-- Heap sibling bytes of levels `1..13`. -/
theorem src_heap (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (j k : Nat) (lo : 144 ≤ k) (hk : k<560) :
    srcAt (s.initialState .opening (t, positions)) positions j k=
      (Opening.trapdoorHeap (s:=s) t (upperNode (posAt positions j) ((k-112)/32) ^^^ 1)).extractLsb'
        (8*((k-112)%32)) 8 := by
  have hp := pos_at_lt positions j
  have node : ((4194304+(posAt positions j).val/4) >>> ((k-112)/32)) ^^^ 1<8388608 := by
    apply Nat.xor_lt_two_pow (n := 23) _ (by decide)
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have un : upperNode (posAt positions j) ((k-112)/32)=(4194304+(posAt positions j).val/4) >>> ((k-112)/32) := by
    rw [upper_node_heap_index, Nat.shiftRight_eq_div_pow]
  unfold srcAt recordSource Layout2Phase.sourceAddress
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show Layout2Phase.heapBase+32*(((4194304+(posAt positions j).val/4) >>> ((k-112)/32)) ^^^ 1)+(k-112)%32=
      trapdoorBase+(32*(((4194304+(posAt positions j).val/4) >>> ((k-112)/32)) ^^^ 1)+(k-112)%32) by
    unfold Layout2Phase.heapBase trapdoorBase LENGTH LOG_LENGTH; omega,
    input_byte s layout t positions _ (by unfold trapdoorBytes LENGTH LOG_LENGTH; omega)]
  unfold Opening.trapdoorHeap
  rw [ext_ext _ _ _ _ _ (by omega), un]
  congr 1; omega

end TwoPermutationPrototype.GroupedOpening.Layout2
