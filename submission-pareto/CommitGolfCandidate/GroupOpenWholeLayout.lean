import CommitGolfCandidate.GroupOpenAlignedCode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Section starts within the four 512-word pages, checked against the delivered image. -/
def row (c j : Nat) : Nat := match c with
  | 0 => ([6147, 6151, 6156, 6167, 6178, 6189, 6191, 6196, 6206, 6218, 6232, 6255, 6275, 6298, 6314, 6342, 6365, 6394, 6411, 6439, 6462, 6485, 6487])[j]?.getD 0
  | 1 => ([6496, 6507, 6512, 6536, 6560, 6584, 6586, 6591, 6614, 6639, 6662, 6676, 6699, 6719, 6747, 6764, 6792, 6815, 6844, 6861, 6889, 6906, 6908])[j]?.getD 0
  | 2 => ([6917, 6925, 6930, 6949, 6968, 6987, 6989, 6994, 7012, 7032, 7052, 7075, 7089, 7112, 7134, 7163, 7180, 7208, 7231, 7260, 7277, 7299, 7301])[j]?.getD 0
  | 3 => ([7310, 7321, 7326, 7350, 7374, 7398, 7400, 7405, 7428, 7453, 7476, 7496, 7519, 7533, 7560, 7583, 7612, 7629, 7657, 7680, 7709, 7720, 7722])[j]?.getD 0
  | _ => 0

def rawStart (c f : Nat) := if f=0 then row c 0 else
  if f≤3 then row c (f+1)+3 else row c (f+3)+(if f=4 then 1 else 3)
def source (f : Nat) : Reg := if 1≤f ∧ f≤3 then .x28 else .x7
def offset (f : Nat) := if f=0 then 0 else if f≤3 then 16+32*(f-1) else siblingOffset (f-4)
def width (f : Nat) := if f=0 then 16 else if f≤5 then 32 else if f≤9 then 30 else 28
def destResidue (c f : Nat) := (2*c+(if f≤5 then 0 else 30*(f-6)))%8

inductive Shape where
  | d16 | w16 | s16r2 | s16r6 | d28 | w28 | s28r2 | s28r6 | d30 | w30 | s30r2 | s30r6 | d32 | w32 | s32r2 | s32r6
  deriving DecidableEq, Repr

def shape (c f : Nat) : Shape :=
  let r := destResidue c f
  match width f with
  | 16 => if r=0 then .d16 else if r=4 then .w16 else if r=2 then .s16r2 else .s16r6
  | 28 => if r=0 then .d28 else if r=4 then .w28 else if r=2 then .s28r2 else .s28r6
  | 30 => if r=0 then .d30 else if r=4 then .w30 else if r=2 then .s30r2 else .s30r6
  | _ => if r=0 then .d32 else if r=4 then .w32 else if r=2 then .s32r2 else .s32r6

def Shape.size : Shape → Nat
  | .d16 => 16
  | .w16 => 16
  | .s16r2 | .s16r6 => 16
  | .d28 => 28
  | .w28 => 28
  | .s28r2 | .s28r6 => 28
  | .d30 => 30
  | .w30 => 30
  | .s30r2 | .s30r6 => 30
  | .d32 => 32
  | .w32 => 32
  | .s32r2 | .s32r6 => 32

def Shape.cycles : Shape → Nat
  | .d16 => 4
  | .w16 => 8
  | .s16r2 => 11
  | .s16r6 => 11
  | .d28 => 8
  | .w28 => 14
  | .s28r2 => 20
  | .s28r6 => 19
  | .d30 => 10
  | .w30 => 16
  | .s30r2 => 19
  | .s30r6 => 19
  | .d32 => 8
  | .w32 => 16
  | .s32r2 => 21
  | .s32r6 => 21

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
