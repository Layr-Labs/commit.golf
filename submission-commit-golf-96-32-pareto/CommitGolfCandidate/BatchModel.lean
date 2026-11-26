import CommitGolfCandidate.BatchUtilities

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
abbrev openingIndex (p : Positions) (r : Nat) := (Late.Check.recordIndex p r).val
theorem opening_index_bound (p : Positions) (r : Nat) : openingIndex p r<LENGTH :=
  (Late.Check.recordIndex p r).isLt
def lowerHash (h : Compression) (input : CheckInput) (r : Nat) := Late.Check.lower h input r 16
abbrev supplied := Late.Check.supplied
def firstAt (input : CheckInput) (bucket : Nat) :=
  (List.range 128).find? (fun r => openingIndex input.positions r/65536 == bucket)
def childrenAt (h : Compression) (input : CheckInput) (p : Nat) : Children :=
  ⟨(firstAt input (2*p)).map (lowerHash h input),(firstAt input (2*p+1)).map (lowerHash h input)⟩
def parentAt (h : Compression) (input : CheckInput) (p : Nat) :=
  (childrenAt h input p).parent h (supplied input p)
def capTable (h : Compression) (input : CheckInput) (p : Nat) :=
  if p<128 then parentAt h input p else 0
abbrev BatchValid := Late.Check.BatchValid
theorem pairAgreement {h : Compression} {x : CheckInput} (v : BatchValid h x) (r : Nat) (hr : r<128) :
    let i := openingIndex x.positions r
    (childrenAt h x (i/131072)).child (i.testBit 16)=some (lowerHash h x r) := v.agree r hr
theorem supplyRead (x : CheckInput) (p : Nat) :
    readBuffer (Late.submission.initialState .check x) (12079668256+32*p) 32 = supplied x p := by
  unfold supplied Late.Check.supplied Late.Check.proofAt
  exact congrArg (fun n=>readBuffer (Late.submission.initialState .check x) n 32)
    (show 12079668256+32*p=12079599648+(68608+32*p) by omega)
end CommitGolfCandidate.PairCap
