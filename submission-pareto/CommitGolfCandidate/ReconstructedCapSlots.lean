import CommitGolfCandidate.ReconstructedCapOrder
import CommitGolfCandidate.ReconstructedOpeningStraight
import CommitGolfCandidate.ReconstructedHonestCapTables

namespace CommitGolfCandidate.Reconstruction.CapSlots
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open HonestCapTables (scratch addrSlot w)
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

abbrev origin := scratch/8
def cell (j : Nat) := origin+j/2
def half (j : Nat) := j%2
def read (m : Memory) (j : Nat) := extractWord32 (m (cell j)) (half j)
def write (m : Memory) (j : Nat) (x : BitVec 32) := writeWord m (cell j) (replaceWord32 (m (cell j)) (half j) x)

def Contains (m : Memory) (xs : List Nat) := ∀ j : Fin xs.length, read m j.val=BitVec.ofNat 32 xs[j.val]

private theorem lane_position (j : Fin 512) :
    alignToDword (addrSlot j.val)=wordAddress (cell j.val) ∧ byteOffset (addrSlot j.val)/4=half j.val ∧ accessValid (addrSlot j.val) 4=true := by
  exact (by decide +kernel : ∀ i : Fin 512, alignToDword (addrSlot i.val)=wordAddress (cell i.val) ∧
    byteOffset (addrSlot i.val)/4=half i.val ∧ accessValid (addrSlot i.val) 4=true) j

theorem load_id (s : MachineState) (j : Fin 512) : s.getWord32 (addrSlot j.val)=read (memoryView s) j.val := by
  unfold MachineState.getWord32
  rw [(lane_position j).1,(lane_position j).2.1]; rfl

theorem valid (j : Fin 512) : accessValid (addrSlot j.val) 4=true := (lane_position j).2.2

theorem store_id (s : MachineState) (j : Fin 512) (x : BitVec 32) (i : Nat) (bound : i<2^33) :
    memoryView (s.setWord32 (addrSlot j.val) x) i=write (memoryView s) j.val x i := by
  unfold MachineState.setWord32
  rw [(lane_position j).1,(lane_position j).2.1]
  exact memory_at_store (by have hi := j.isLt; change 8589934272+j.val/2<2^61; omega) (by omega)

private theorem same_lane (m : Word) (v : BitVec 32) (a : Fin 2) :
    extractWord32 (replaceWord32 m a.val v) a.val=v := by
  fin_cases a <;> ext i (hi : i<32) <;> simp [extractWord32,replaceWord32,BitVec.truncate,BitVec.zeroExtend] <;>
    nat_lt_cases i 32 <;> simp_all

private theorem other_lane (m : Word) (v : BitVec 32) (a b : Fin 2) (ne : a≠b) :
    extractWord32 (replaceWord32 m a.val v) b.val=extractWord32 m b.val := by
  fin_cases a <;> fin_cases b <;> simp_all only [ne_eq,not_true_eq_false,Fin.val_zero,Fin.val_one]
  all_goals ext i (hi : i<32); simp [extractWord32,replaceWord32,BitVec.truncate,BitVec.zeroExtend]; nat_lt_cases i 32 <;> simp_all

theorem read_write (m : Memory) (j k : Nat) (x : BitVec 32) :
    read (write m j x) k = if k=j then x else read m k := by
  classical
  by_cases eq : k=j
  · subst k
    simp only [read,write,writeWord,ite_true]
    exact same_lane _ _ (⟨half j,by unfold half;omega⟩ : Fin 2)
  · rw [ite_eq_right eq]
    unfold read write writeWord
    split
    · rename_i same
      change origin+k/2=origin+j/2 at same
      have apart : (⟨half j,by unfold half;omega⟩ : Fin 2)≠⟨half k,by unfold half;omega⟩ := by
        intro error
        have equal := congrArg Fin.val error
        change j%2=k%2 at equal
        omega
      have w : cell k=cell j := same
      rw [w]
      exact other_lane (m (cell j)) x (⟨half j,by unfold half;omega⟩ : Fin 2) (⟨half k,by unfold half;omega⟩ : Fin 2) apart
    · rfl

theorem append (m : Memory) (xs : List Nat) (x : Nat) (old : Contains m xs) :
    Contains (write m xs.length (BitVec.ofNat 32 x)) (xs++[x]) := by
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

theorem unchanged (m : Memory) (idx j : Nat) (x : BitVec 32) (other : idx≠cell j) :
    write m j x idx=m idx := by simp [write,writeWord,other]

end CommitGolfCandidate.Reconstruction.CapSlots
