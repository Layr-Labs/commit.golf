import CommitGolfCandidate.GroupOpenAlignedCode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Section starts within the four 512-word pages, checked against the delivered image. -/
def row (c j : Nat) : Nat := match c with
  | 0 => ([6147, 6151, 6156, 6167, 6178, 6189, 6191, 6196, 6206, 6218, 6232, 6258, 6278, 6304, 6320, 6351, 6374, 6405, 6422, 6453, 6476, 6501, 6503])[j]?.getD 0
  | 1 => ([6512, 6524, 6529, 6556, 6583, 6610, 6612, 6617, 6643, 6671, 6697, 6711, 6737, 6757, 6787, 6804, 6835, 6858, 6889, 6906, 6937, 6954, 6956])[j]?.getD 0
  | 2 => ([6965, 6973, 6978, 6997, 7016, 7035, 7037, 7042, 7060, 7080, 7100, 7126, 7140, 7166, 7188, 7219, 7236, 7267, 7290, 7321, 7338, 7363, 7365])[j]?.getD 0
  | 3 => ([7374, 7386, 7391, 7418, 7445, 7472, 7474, 7479, 7505, 7533, 7559, 7579, 7605, 7619, 7649, 7672, 7703, 7720, 7751, 7774, 7805, 7816, 7818])[j]?.getD 0
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

def firstCost (o : Nat) := if o=0 then 1 else 0
def setupPC (o : Nat) : Word := if o=0 then AlignedFields.pcAt 15 else AlignedFields.pcAt (row (pageClass o) 0-3)
def nextClass (c : Nat) := (c+3)%4

theorem class_succ (o : Nat) : pageClass (o+1)=nextClass (pageClass o) := by
  unfold pageClass nextClass recordBase recordBytes;omega
theorem zero_class : pageClass 0=0 := by decide

end TwoPermutationPrototype.GroupedOpening.Whole
