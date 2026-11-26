import CommitGolfCandidate.ReconstructedCapOrder
import CommitGolfCandidate.ReconstructedOpeningStraight
import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.CheckCapSlots
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
abbrev W := BitVec.ofNat 64
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def cell (base j : Nat) := base/8+j/2
def half (j : Nat) := j%2
def address (base j : Nat) := W (base+4*j)
def read (m : Memory) (base j : Nat) := extractWord32 (m (cell base j)) (half j)
def write (m : Memory) (base j : Nat) (x : BitVec 32) :=
  writeWord m (cell base j) (replaceWord32 (m (cell base j)) (half j) x)

def Contains (m : Memory) (base : Nat) (xs : List Nat) :=
  ∀ j : Fin xs.length, read m base j.val=BitVec.ofNat 32 xs[j.val]

private theorem lane_position (base j : Nat) (align : base%8=0) :
    alignToDword (address base j)=wordAddress (cell base j) ∧ byteOffset (address base j)/4=half j := by
  constructor
  · change alignToDword (W (base+4*j))=W (8*(base/8+j/2))
    rw [OpeningCursor.aligned]
    congr 2
    omega
  · unfold address byteOffset half
    rw [BitVec.toNat_and,BitVec.toNat_ofNat]
    change ((base+4*j)%2^64 &&& (2^3-1))/4=j%2
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem load_id (s : MachineState) (base j : Nat) (align : base%8=0) :
    s.getWord32 (address base j)=read (memoryView s) base j := by
  unfold MachineState.getWord32
  rw [(lane_position base j align).1,(lane_position base j align).2];rfl

theorem valid (base j : Nat) (align : base%8=0) (room : base+4*j+4≤MEMORY_BYTES) :
    accessValid (address base j) 4=true := by
  unfold MEMORY_BYTES at room
  simp only [address,accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt
    (by omega : base+4*j<2^64),Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨room,by omega⟩

theorem store_id (s : MachineState) (base j : Nat) (x : BitVec 32) (align : base%8=0)
    (room : base+4*j+4≤MEMORY_BYTES) (i : Nat) (bound : i<2^33) :
    memoryView (s.setWord32 (address base j) x) i=write (memoryView s) base j x i := by
  unfold MachineState.setWord32
  rw [(lane_position base j align).1,(lane_position base j align).2]
  exact memory_at_store (by unfold cell;unfold MEMORY_BYTES at room;omega) (by omega)

private theorem same_lane (m : Word) (v : BitVec 32) (a : Fin 2) :
    extractWord32 (replaceWord32 m a.val v) a.val=v := by
  fin_cases a <;> ext i (hi : i<32) <;> simp [extractWord32,replaceWord32,BitVec.truncate,BitVec.zeroExtend] <;>
    nat_lt_cases i 32 <;> simp_all

private theorem other_lane (m : Word) (v : BitVec 32) (a b : Fin 2) (ne : a≠b) :
    extractWord32 (replaceWord32 m a.val v) b.val=extractWord32 m b.val := by
  fin_cases a <;> fin_cases b <;> simp_all only [ne_eq,not_true_eq_false,Fin.val_zero,Fin.val_one]
  all_goals ext i (hi : i<32); simp [extractWord32,replaceWord32,BitVec.truncate,BitVec.zeroExtend]; nat_lt_cases i 32 <;> simp_all

theorem read_write (m : Memory) (base j k : Nat) (x : BitVec 32) :
    read (write m base j x) base k = if k=j then x else read m base k := by
  classical
  by_cases eq : k=j
  · subst k
    simp only [read,write,writeWord,ite_true]
    exact same_lane _ _ (⟨half j,by unfold half;omega⟩ : Fin 2)
  · rw [ite_eq_right eq]
    unfold read write writeWord
    split
    · rename_i same
      change base/8+k/2=base/8+j/2 at same
      have apart : (⟨half j,by unfold half;omega⟩ : Fin 2)≠⟨half k,by unfold half;omega⟩ := by
        intro error
        have equal := congrArg Fin.val error
        change j%2=k%2 at equal
        omega
      have w : cell base k=cell base j := same
      rw [w]
      exact other_lane (m (cell base j)) x (⟨half j,by unfold half;omega⟩ : Fin 2) (⟨half k,by unfold half;omega⟩ : Fin 2) apart
    · rfl

theorem append (m : Memory) (base : Nat) (xs : List Nat) (x : Nat) (old : Contains m base xs) :
    Contains (write m base xs.length (BitVec.ofNat 32 x)) base (xs++[x]) := by
  intro j
  rw [read_write]
  by_cases endAt : j.val=xs.length
  · rw [ite_eq_left endAt]
    simp [List.getElem_append_right (by omega : xs.length≤j.val),endAt]
  · have jj := j.isLt
    simp only [List.length_append,List.length_singleton] at jj
    have oldSlot : j.val<xs.length := by omega
    rw [ite_eq_right endAt,List.getElem_append_left oldSlot]
    exact old ⟨j.val,oldSlot⟩

theorem unchanged (m : Memory) (base idx j : Nat) (x : BitVec 32) (other : idx≠cell base j) :
    write m base j x idx=m idx := by simp [write,writeWord,other]

end CommitGolfCandidate.Reconstruction.CheckCapSlots
