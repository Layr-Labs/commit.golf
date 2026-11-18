import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.GroupedSaltMap

/-!
# Pair-heads salt loop: Nat-level model of the opener's loop arithmetic

The register values of opening words 739-764 as Nat functions of the leaf index `i`, the branch flags of
`preRows`, and `loop_out : loopOut i = loopMap i` (the interface's model of the loop).
-/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate

/-- `r = (p mod 2048) mod 11` with `p = i>>1`. -/
def loopR (i : Nat) := (i/2%2048)%11
/-- Position in the group: `k = r` (group A, r<5) or `r-5` (group B). -/
def loopK (i : Nat) := if loopR i<5 then loopR i else loopR i-5
/-- Head pair (global): `p - k`. -/
def loopHead (i : Nat) := i/2-loopK i
/-- Copy offset `32k + 16par - 16`. -/
def copyOff (i : Nat) := 32*loopK i+16*(i%2)-16

def groupB (i : Nat) : Bool := !decide (loopR i<5)
def inPlace (i : Nat) : Bool := decide (loopK i=0)
def twelfth (i : Nat) : Bool := decide (copyOff i=160)

/-- (head pair, byte offset) as the loop computes it. -/
def loopOut (i : Nat) : Nat × Nat :=
  if loopK i=0 then (loopHead i,184*(i%2))
  else if copyOff i=160 then (loopHead i-5,144)
  else (loopHead i,copyOff i)

theorem loop_out (i : Nat) : loopOut i=Grouped.loopMap i := by
  unfold loopOut Grouped.loopMap Grouped.localLoop loopHead copyOff loopK loopR
  have e1 : i%4096/2=i/2%2048 := by omega
  have e2 : i%4096%2=i%2 := by omega
  simp only [e1,e2]
  by_cases a : i/2%2048%11<5
  · simp only [a,ite_true]
    by_cases z : i/2%2048%11=0
    · simp only [z,ite_true];ext <;> simp <;> omega
    · simp only [z,ite_false]
      by_cases t : 32*(i/2%2048%11)+16*(i%2)-16=160
      · simp only [t,ite_true];ext <;> simp <;> omega
      · simp only [t,ite_false];ext <;> simp <;> omega
  · simp only [a,ite_false]
    by_cases z : i/2%2048%11-5=0
    · simp only [z,ite_true];ext <;> simp <;> omega
    · simp only [z,ite_false]
      by_cases t : 32*(i/2%2048%11-5)+16*(i%2)-16=160
      · simp only [t,ite_true];ext <;> simp <;> omega
      · simp only [t,ite_false];ext <;> simp <;> omega

theorem loop_out_eq (i : Nat) (hi : i<16777216) :
    loopOut i=(Grouped.saltHead i,Grouped.sliceByte (CommitGolfCandidate.Permutation.CounterSalt.coord ⟨i,hi⟩).2.val) :=
  (loop_out i).trans (Grouped.loop_map_eq i hi)

theorem loop_r_lt (i : Nat) : loopR i<11 := by unfold loopR;omega
theorem loop_k_lt (i : Nat) : loopK i<6 := by unfold loopK loopR;split <;> omega
theorem loop_k_le (i : Nat) : loopK i ≤ i/2 := by unfold loopK loopR;split <;> omega
theorem twelfth_head (i : Nat) (k : loopK i≠0) (t : copyOff i=160) : 5≤loopHead i := by
  unfold copyOff at t;unfold loopHead;unfold loopK loopR at *
  by_cases a : i/2%2048%11<5
  · rw [if_pos a] at k t ⊢;omega
  · rw [if_neg a] at k t ⊢;omega

end TwoPermutationPrototype.GroupedOpening
