import CommitGolfCandidate.ReconstructedCommitSetup

namespace CommitGolfCandidate.Reconstruction.LeafCode
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitSetup CommitBlocks

def saved : Nat → Reg
  | 0 => .x9 | 1 => .x21 | 2 => .x22 | 3 => .x23
  | 4 => .x24 | 5 => .x25 | 6 => .x26 | _ => .x27

def spill : List Instr := (List.range 8).map fun j => .LD (saved j) .x12 (BitVec.ofNat 12 (112+8*j))

def groupSetup (g : Nat) : List Instr :=
  (if g%16 = 0 then [.SD .x8 .x10 8] else []) ++
  [.ADDI .x10 .x10 200,.ADDI .x12 .x10 4064,.ECALL,.ADDI .x12 .x10 3976,
   .ADDI .x10 .x8 (BitVec.ofNat 12 (4096-8*(g%16+1))),.ECALL] ++
  (if g < 341 then spill else [])

def rebase (slot : Nat) : List Instr := if slot ≠ 0 ∧ slot%63 = 0 then [.ADDI .x19 .x19 2016] else []

def saltLoad (lane : Nat) : List Instr :=
  let disp := 4096+16*(lane-1)-176-256*lane
  if lane = 0 then [] else if lane < 8 then
    [.LD .x6 .x10 (BitVec.ofNat 12 disp),.LD .x7 .x10 (BitVec.ofNat 12 (disp+8)),
     .SD .x10 .x6 8,.SD .x10 .x7 16]
  else [.SD .x10 (saved (2*(lane-8))) 8,.SD .x10 (saved (2*(lane-8)+1)) 16]

def body (slot : Nat) : List Instr :=
  let lane := slot%12
  (if lane = 0 then groupSetup (slot/12) else []) ++ rebase slot ++
  (if lane = 0 then [.ADDI .x10 .x12 176] else
    [.ADDI .x10 .x10 200,.ADDI .x12 .x10 4064,.ECALL,.ADDI .x10 .x10 56]) ++
  [.SD .x10 .x10 0] ++ saltLoad lane ++
  [.SB .x10 .x0 23,.ADDI .x12 .x19 (BitVec.ofNat 12 (32*(slot%63))),.ECALL,.SH .x12 .x17 30]

/-- Word address in the text segment. Only three lanes are present after lane zero
in the final partial group of a 4,096-entry tile. -/
def start (slot : Nat) : Nat :=
  let g := slot/12
  let lane := slot%12
  19+155*g+(g+15)/16+(slot-1)/63 +
    (if lane = 0 then 0 else (if g < 341 then 20 else 12) + (if g%16 = 0 then 1 else 0)
      + 13*min (lane-1) 7 + 11*(lane-8))

def wordMatches (atWord : Nat) (op : Instr) : Bool :=
  if h : atWord < 150132 then
    match decodeInstruction (Artifact.commitCode.get 32 ⟨atWord,h⟩) with
    | some (.base decoded) => decide (decoded = op)
    | _ => false
  else false

def matchOps : Nat → List Instr → Bool
  | _, [] => true
  | pc, op :: rest => wordMatches pc op && matchOps (pc+1) rest

def goodLane (s : Nat) := matchOps (start s) (body s) &&
  decide (start s + (body s).length = (if s+1=4096 then 53012 else start (s+1)))

theorem fetch_word (atWord : Nat) (op : Instr) (h : wordMatches atWord op = true)
    (s : MachineState) (pc : s.pc = addr atWord) : fetch im s = some (.base op) := by
  unfold wordMatches at h
  split at h <;> rename_i bound
  · cases dec : decodeInstruction (Artifact.commitCode.get 32 ⟨atWord,bound⟩) with
    | none => simp [dec] at h
    | some decoded =>
      cases decoded with
      | base inst =>
        have same : inst = op := by simpa [dec] using h
        subst inst
        exact fetch_at ⟨atWord,bound⟩ _ dec _ pc
      | word tag d a b => simp [dec] at h
      | sraiw d a b => simp [dec] at h
  · contradiction

theorem fetch_matchOps (ops : List Instr) (base j : Nat) (good : matchOps base ops = true)
    (inRange : j < ops.length) (s : MachineState) (pc : s.pc = addr (base+j)) :
    fetch im s = some (.base ops[j]) := by
  induction ops generalizing base j with
  | nil => simp at inRange
  | cons op rest ih =>
    simp only [matchOps,Bool.and_eq_true] at good
    cases j with
    | zero => exact fetch_word base op good.1 s pc
    | succ j =>
      exact ih (base+1) j good.2 (by simpa using inRange) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pc)

/-- A local chunk of static lane verifications. -/
def within (lo : Nat) : Nat → Bool
  | 0 => true
  | n+1 => within lo n && goodLane (lo+n)

theorem joinChunks (lo a b : Nat) (left : within lo a = true) (right : within (lo+a) b = true) :
    within lo (a+b) = true := by
  induction b with
  | zero => exact left
  | succ b ih =>
    simp only [within,Bool.and_eq_true] at right
    rw [Nat.add_succ,within,Bool.and_eq_true]
    exact ⟨ih right.1,by simpa only [Nat.add_assoc] using right.2⟩

theorem insideChunk (lo n j : Nat) (good : within lo n = true) (bound : j < n) :
    goodLane (lo+j) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [within,Bool.and_eq_true] at good
    by_cases h : j = n
    · exact h ▸ good.2
    · exact ih good.1 (by omega)

end CommitGolfCandidate.Reconstruction.LeafCode
