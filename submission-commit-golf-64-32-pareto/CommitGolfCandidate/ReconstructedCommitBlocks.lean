import CommitGolf.Artifact
import CommitGolfCandidate.ReconstructedFetch
import CommitGolfCandidate.ReconstructedCommitControl

namespace CommitGolfCandidate.Reconstruction.CommitBlocks
open CommitGolf CommitGolf.Riscv CommitGolf.ArtifactEncoding RiscvZkvm.Rv64 CommitControl

/-- Check an indexed predicate directly on the verifier's packed chunks. -/
def allWords {n : Nat} (packed : Packed n) (offset : Nat) (ok : Nat → BitVec 32 → Bool) : Bool :=
  match packed with
  | .chunk count payload =>
      (List.range count).all fun j => ok (offset+j) (BitVec.ofNat 32 (payload >>> (32*j)))
  | @Packed.join l _ left right => allWords left offset ok && allWords right (offset+l) ok

theorem checked_word {n : Nat} (packed : Packed n) (offset : Nat) (ok : Nat → BitVec 32 → Bool)
    (h : allWords packed offset ok = true) (i : Fin n) :
    ok (offset+i.val) (packed.get 32 i) = true := by
  induction packed generalizing offset with
  | chunk count payload =>
    simp only [allWords,List.all_eq_true,List.mem_range] at h
    exact h i.val i.isLt
  | @join l r left right ihl ihr =>
    simp only [allWords,Bool.and_eq_true] at h
    by_cases hi : i.val < l
    · rw [get_join_left _ _ _ _ hi]; exact ihl offset h.1 ⟨i.val,hi⟩
    · rw [get_join_right _ _ _ _ (by omega)]
      have eq : offset+i.val = (offset+l)+(i.val-l) := by omega
      rw [eq]; exact ihr (offset+l) h.2 ⟨i.val-l,by have := i.isLt; omega⟩

/-- Per-instruction oracle and arithmetic prices on a straight-line region
when x5 selects public calls and x20 is the loop counter. -/
def validStraight (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | some (.base .ECALL) => true
  | some (.base op) => ordinary op
  | _ => false

def cost (word : BitVec 32) : Nat :=
  match decodeInstruction word with
  | some (.base .ECALL) => 30
  | some op => instructionCycles op
  | none => 0

def calls (word : BitVec 32) : Nat :=
  match decodeInstruction word with
  | some (.base .ECALL) => 1
  | _ => 0

theorem step {im : Image} (pc counter : Word) (w : BitVec 32)
    (read : ∀ s : MachineState, s.pc = pc → fetch im s = decodeInstruction w)
    (ok : validStraight w = true) :
    Fragment im 1 (cost w) (calls w) (At pc counter) (At (pc+4) counter) := by
  cases dec : decodeInstruction w with
  | none => simp [validStraight,dec] at ok
  | some op =>
    have got := fun (s : MachineState) (h : s.pc = pc) => (read s h).trans dec
    cases op with
    | word op rd rs rt => simp [validStraight,dec] at ok
    | sraiw rd rs sh => simp [validStraight,dec] at ok
    | base op =>
      by_cases sys : op = .ECALL
      · subst op
        simpa only [cost,calls,dec] using public_step im pc counter got
      · have ordinaryOK : ordinary op = true := by
          cases op <;> simp_all [validStraight, ordinary]
        have cp : cost w = instructionCycles (.base op) := by cases op <;> simp_all [cost]
        have cq : calls w = 0 := by cases op <;> simp_all [calls]
        rw [cp,cq]; exact plain_step im pc counter op got ordinaryOK

def addr (index : Nat) := BitVec.ofNat 64 (4096+4*index)

theorem addr_next (i : Nat) : addr (i+1) = addr i + 4 := by
  unfold addr; rw [show 4096+4*(i+1) = (4096+4*i)+4 by omega, BitVec.ofNat_add]; rfl

/-- A closed interval sum, by induction on the number of instructions. -/
def rangeSum (f : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => rangeSum f start n + f (start+n)

theorem run_straight (im : Image) (word : Nat → BitVec 32) (start count : Nat) (c : Word)
    (fetched : ∀ j < count, ∀ s : MachineState, s.pc = addr (start+j) →
      fetch im s = decodeInstruction (word (start+j)))
    (checked : ∀ j < count, validStraight (word (start+j)) = true) :
    Fragment im count (rangeSum (cost ∘ word) start count) (rangeSum (calls ∘ word) start count)
      (At (addr start) c) (At (addr (start+count)) c) := by
  induction count with
  | zero => simpa [rangeSum] using empty im (At (addr start) c)
  | succ n ih =>
    have head := ih (fun j h => fetched j (by omega)) (fun j h => checked j (by omega))
    have last := step (addr (start+n)) c _ (fetched n (by omega)) (checked n (by omega))
    simpa only [rangeSum,Nat.add_succ,Function.comp_apply,addr_next] using compose head last

end CommitGolfCandidate.Reconstruction.CommitBlocks
