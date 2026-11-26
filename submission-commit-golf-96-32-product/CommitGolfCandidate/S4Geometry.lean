import CommitGolf.Statements

namespace CommitGolfCandidate.S4
open CommitGolf

inductive Profile | byte | packed deriving DecidableEq, Repr

def active : Profile := .packed

/-- Number of leaves covered by a node at the given height from the leaves. -/
def span : Nat → Nat
  | 0 => 1
  | k+1 => 3 * 2^k

def radix (h : Nat) : Nat := if h = 0 then 3 else 2
def width (h : Nat) := (LENGTH + span h - 1) / span h
def above (j : Nat) := width (j+1)
def rowCount (h : Nat) := (width h + radix h - 1) / radix h
def layerOffset : Nat → Nat
  | 0 => 0
  | h+1 => layerOffset h + 96 * rowCount h

def slotOffset (h i : Nat) := 96*(i/radix h)+32*(i%radix h)
def nodeAddr (h i : Nat) := 4294971424+layerOffset h+slotOffset h i
def nodeIndex (i h : Nat) := i / span h
def childPos (i h : Nat) := (nodeIndex i h) % radix h

def bits (profile : Profile) (h : Nat) : Nat :=
  if h<2 ∨ 24≤h then 256 else if profile=.packed ∧ 6≤h then 238 else 240

def capHeight : Nat := 15
def parentCost : Nat → Nat
  | 0 => 0
  | d+1 => width (23-d+1) + parentCost d

theorem span_succ (h : Nat) : span (h+1)=span h*radix h := by
  cases h with
  | zero=>decide
  | succ n=>simp [span,radix,Nat.pow_succ,Nat.mul_assoc]

theorem row_width : ∀ h : Fin 24,rowCount h.val=width (h.val+1) := by decide
theorem levels : (List.range 25).map width =
    [16777216,5592406,2796203,1398102,699051,349526,174763,87382,43691,21846,10923,5462,
      2731,1366,683,342,171,86,43,22,11,6,3,2,1] := by decide
theorem capSize : width capHeight=342 ∧ width (capHeight+1)=171 := by decide
theorem totalParents : parentCost 24=11184822 := by decide
theorem parentAllowance : parentCost 24≤LENGTH := by decide
theorem packedLevels : ∀ h : Fin 25,bits .packed h.val=238 → bits .byte h.val=240 := by decide
theorem bottomSlot (i : Nat) : slotOffset 0 i=32*i := by unfold slotOffset radix;simp;omega
theorem rowStart (h p : Nat) : slotOffset h (radix h*p)=96*p := by
  by_cases z : h=0 <;> simp [slotOffset,radix,z]
theorem addressValid : ∀ h : Fin 25,4294971424+layerOffset h.val+96*rowCount h.val≤5905584160 := by decide
theorem nextIndex (i h : Nat) : nodeIndex i (h+1)=nodeIndex i h / radix h := by rw [nodeIndex,nodeIndex,span_succ,Nat.div_div_eq_div_mul]
theorem lowerSiblings : ((List.range 15).map (fun h=>radix h-1)).sum=16 := by decide
theorem fullSiblings : ((List.range 24).map (fun h=>radix h-1)).sum=25 := by decide
end CommitGolfCandidate.S4
