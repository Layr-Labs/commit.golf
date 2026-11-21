import CommitGolfCandidate.GroupOpenAlignedCode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Section starts within the four 512-word pages, checked against the delivered image. -/
def row (c j : Nat) : Nat := match c with
  | 0 => ([4096, 4100, 4105, 4116, 4127, 4138, 4140, 4145, 4155, 4167, 4181, 4207, 4227, 4253, 4269, 4300, 4323, 4354, 4371, 4402, 4425, 4450, 4453])[j]?.getD 0
  | 1 => ([4608, 4620, 4625, 4652, 4679, 4706, 4708, 4713, 4739, 4767, 4793, 4807, 4833, 4853, 4883, 4900, 4931, 4954, 4985, 5002, 5033, 5050, 5053])[j]?.getD 0
  | 2 => ([5120, 5128, 5133, 5152, 5171, 5190, 5192, 5197, 5215, 5235, 5255, 5281, 5295, 5321, 5343, 5374, 5391, 5422, 5445, 5476, 5493, 5518, 5521])[j]?.getD 0
  | 3 => ([5632, 5644, 5649, 5676, 5703, 5730, 5732, 5737, 5763, 5791, 5817, 5837, 5863, 5877, 5907, 5930, 5961, 5978, 6009, 6032, 6063, 6074, 6077])[j]?.getD 0
  | _ => 0

def rawStart (c f : Nat) := if f=0 then row c 0 else
  if f≤3 then row c (f+1)+3 else row c (f+3)+(if f=4 then 1 else 3)
def source (f : Nat) : Reg := if 1≤f ∧ f≤3 then .x28 else .x7
def offset (f : Nat) := if f=0 then 0 else if f≤3 then 16+32*(f-1) else siblingOffset (f-4)
def width (f : Nat) := if f=0 then 16 else if f≤5 then 32 else if f≤9 then 30 else 28
def destResidue (c f : Nat) := (2*c+(if f≤5 then 0 else 30*(f-6)))%8

inductive Shape where
  | d16 | w16 | s16 | d28 | w28 | s28 | d30 | w30 | s30 | d32 | w32 | s32
  deriving DecidableEq, Repr

def shape (c f : Nat) : Shape :=
  let r := destResidue c f
  match width f with
  | 16 => if r=0 then .d16 else if r=4 then .w16 else .s16
  | 28 => if r=0 then .d28 else if r=4 then .w28 else .s28
  | 30 => if r=0 then .d30 else if r=4 then .w30 else .s30
  | _ => if r=0 then .d32 else if r=4 then .w32 else .s32

def Shape.size : Shape → Nat
  | .d16 => 16
  | .w16 => 16
  | .s16 => 16
  | .d28 => 28
  | .w28 => 28
  | .s28 => 28
  | .d30 => 30
  | .w30 => 30
  | .s30 => 30
  | .d32 => 32
  | .w32 => 32
  | .s32 => 32

def Shape.cycles : Shape → Nat
  | .d16 => 4
  | .w16 => 8
  | .s16 => 12
  | .d28 => 8
  | .w28 => 14
  | .s28 => 22
  | .d30 => 10
  | .w30 => 16
  | .s30 => 22
  | .d32 => 8
  | .w32 => 16
  | .s32 => 24

def pageClass (o : Nat) := recordBase o%8/2
def pageCost (o : Nat) := row (pageClass o) 22-row (pageClass o) 0
theorem class_lt (o : Nat) : pageClass o < 4 := by unfold pageClass; omega
theorem class_mod (o : Nat) : pageClass o=pageClass (o%4) := by
  unfold pageClass recordBase recordBytes
  omega
theorem class_residue (o : Nat) : recordBase o%8=2*pageClass o := by
  have := AlignedFields.record_even o; unfold pageClass; omega
theorem sibling_residue (o l : Nat) (hl : l<14) :
    siblingDestination o l%8=destResidue (pageClass o) (4+l) := by
  have := class_residue o
  unfold siblingDestination siblingOffset destResidue
  split <;> split_ifs <;> omega

end TwoPermutationPrototype.GroupedOpening.Whole
