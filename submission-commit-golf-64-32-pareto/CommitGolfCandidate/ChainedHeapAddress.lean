import CommitGolfCandidate.ChainedNodeMeaning

/-! Bounded word-address arithmetic for the delivered binary heap. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def heapBase : Nat := 4294971424
def heapAddress (node : Nat) : Word := BitVec.ofNat 64 (heapBase+32*node)

theorem heap_cursor32 (node index : Nat) (inside : index ≤ node) :
    cursorAt (heapAddress node) 32 index = heapAddress (node-index) := by
  have arithmetic : heapBase+32*node = heapBase+32*(node-index)+32*index := by omega
  unfold cursorAt heapAddress
  rw [arithmetic,BitVec.ofNat_add,BitVec.add_sub_cancel]

theorem heap_cursor64 (node index : Nat) (inside : 2*index ≤ node) :
    cursorAt (heapAddress node) 64 index = heapAddress (node-2*index) := by
  have arithmetic : heapBase+32*node = heapBase+32*(node-2*index)+64*index := by omega
  unfold cursorAt heapAddress
  rw [arithmetic,BitVec.ofNat_add,BitVec.add_sub_cancel]

theorem heap_word_numeric (node word : Nat) (small : node < 2^25) (short : word < 8) :
    (heapAddress node+BitVec.ofNat 64 (8*word)).toNat = heapBase+32*node+8*word := by
  have room : heapBase+32*node+8*word < 2^64 := by unfold heapBase; omega
  rw [heapAddress,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt room]

theorem heap_word_valid (node word : Nat) (small : node < 2^25) (short : word < 8) :
    accessValid (heapAddress node+BitVec.ofNat 64 (8*word)) 8 = true := by
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq,
    heap_word_numeric node word small short]
  unfold heapBase MEMORY_BYTES
  constructor <;> omega

theorem heap_word_outside (node word : Nat) (small : node < 2^25) (short : word < 8) :
    OutsideScratch (heapAddress node+BitVec.ofNat 64 (8*word)) := by
  have numeric := heap_word_numeric node word small short
  refine ⟨?_,?_,?_⟩ <;> rw [numeric] <;> unfold heapBase <;> omega

theorem heap_boundary (count : Nat) (positive : 0 < count) :
    BitVec.ofNat 64 heapBase+BitVec.ofNat 64 (32*count)-32 = heapAddress (count-1) := by
  have arithmetic : heapBase+32*count = heapBase+32*(count-1)+32 := by omega
  rw [←BitVec.ofNat_add,arithmetic,BitVec.ofNat_add,
    show BitVec.ofNat 64 32 = (32 : Word) from rfl,BitVec.add_sub_cancel]
  rfl

theorem heap_boundary_offset (count : Nat) (positive : 0 < count) :
    (BitVec.ofNat 64 heapBase+BitVec.ofNat 64 (32*count)-32)+BitVec.ofNat 64 (32*count) =
      heapAddress (2*count-1) := by
  rw [heap_boundary count positive]
  unfold heapAddress
  rw [←BitVec.ofNat_add]
  congr 1
  omega

end CommitGolfCandidate.Chained.Native
