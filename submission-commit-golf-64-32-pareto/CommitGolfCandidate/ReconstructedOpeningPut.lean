import CommitGolfCandidate.ReconstructedOpeningStraight
import CommitGolfCandidate.ReconstructedWireBytes

namespace CommitGolfCandidate.Reconstruction.OpeningPut
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype (Memory writeWord)
set_option maxRecDepth 8192

abbrev base : Nat := 1291846156
abbrev capacity : Nat := 1044382656
def cell (cursor : Nat) := base+cursor/64
def value (n : Nat) (v : Word) := v.toNat%2^n

def first (m : Memory) (cursor : Nat) (v : Word) :=
  if cursor%64=0 then v else m (cell cursor) ||| (v <<< (cursor%64))

def put (m : Memory) (cursor width : Nat) (v : Word) : Memory :=
  let written := writeWord m (cell cursor) (first m cursor v)
  if cursor%64+width>64 then writeWord written (cell cursor+1) (v >>> (64-cursor%64)) else written

def Serialized (m : Memory) (stream : Nat) :=
  ∀ j < capacity, (m (base+j)).toNat=HonestStream.word stream j

private theorem first_word (m : Memory) (stream cursor : Nat) (v : Word)
    (same : Serialized m stream) (inside : cursor/64<capacity) (used : stream<2^cursor) :
    (first m cursor v).toNat=HonestStream.word (HonestStream.append stream cursor v.toNat) (cursor/64) := by
  rw [HonestStream.put_first]
  by_cases aligned : cursor%64=0
  · simp only [first,aligned,ite_true,HonestStream.empty_word_at_boundary stream cursor used aligned,Nat.zero_or,
      Nat.shiftLeft_zero,Nat.mod_eq_of_lt v.isLt]
  · simp only [first,aligned,ite_false,BitVec.toNat_or,BitVec.toNat_shiftLeft,cell,same _ inside]

private theorem empty_next (stream cursor : Nat) (used : stream<2^cursor) :
    HonestStream.word stream (cursor/64+1)=0 := by
  have high := Nat.pow_le_pow_right (n:=2) (by decide) (show cursor ≤ 64*(cursor/64+1) by omega)
  simp [HonestStream.word,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt (used.trans_le high)]

theorem serial_put (m : Memory) (stream cursor width : Nat) (v : Word) (same : Serialized m stream)
    (used : stream<2^cursor) (fits : v.toNat<2^width) (widthOk : width≤64) (inside : cursor/64<capacity) :
    Serialized (put m cursor width v) (HonestStream.append stream cursor v.toNat) := by
  intro j good
  by_cases atWord : j=cursor/64
  · subst j
    unfold put
    split <;> simp only [writeWord,cell,show base+cursor/64≠base+cursor/64+1 by omega,ite_false,ite_true]
    all_goals exact first_word m stream cursor v same inside used
  by_cases next : j=cursor/64+1
  · subst j
    have ne : base+(cursor/64+1)≠cell cursor := by unfold cell;omega
    rw [HonestStream.put_next _ _ _ used]
    unfold put
    split
    · simp only [writeWord,cell,←Nat.add_assoc,ite_true,BitVec.toNat_ushiftRight]
      exact (Nat.mod_eq_of_lt ((Nat.shiftRight_le v.toNat _).trans_lt v.isLt)).symm
    · rename_i off
      simp only [writeWord,ne,ite_false,same _ good,empty_next stream cursor used]
      exact (HonestStream.no_overflow v.toNat cursor width fits (by omega)).symm
  have ne : base+j≠cell cursor := by unfold cell;omega
  have ne2 : base+j≠cell cursor+1 := by unfold cell;omega
  rw [HonestStream.put_frame stream v.toNat cursor width j fits widthOk (by omega)]
  unfold put
  split <;> simp only [writeWord,ne,ne2,ite_false,same _ good]

theorem keep (m : Memory) (idx cursor n : Nat) (v : Word)
    (firstAddr : idx≠cell cursor) (nextAddr : idx≠cell cursor+1) :
    put m cursor n v idx = m idx := by
  unfold put
  split <;> simp only [writeWord,firstAddr,nextAddr,ite_false]

theorem append_field (fs : List Wire.Field) (f : Wire.Field) :
    HonestStream.append (Wire.pack fs) (Wire.bits fs) (Wire.clipped f) = Wire.pack (fs++[f]) := by
  rw [HonestStream.append,Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt (Wire.pack_bound fs),
    Nat.shiftLeft_eq,Wire.pack_append]
  simp only [Wire.pack,Nat.mul_zero,Nat.add_zero]
  ac_rfl

end CommitGolfCandidate.Reconstruction.OpeningPut
