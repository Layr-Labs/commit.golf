import CommitGolfCandidate.ReconstructedCommitSetup
import CommitGolfCandidate.ReconstructedCommitParentsSpec

namespace CommitGolfCandidate.Reconstruction.CommitParents.Image
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Static instructions inside one node body of the emitted commitment image. -/
inductive Atom where
  | advanceSource | advanceDst | source (slot : Fin 64) | dest (slot : Fin 128)
  | labelRight | compress | continueAtDst | saveWide | loadTop | reduceTop | storeTop
  | loadNarrow | fillNarrow | saveNarrow
  deriving DecidableEq

def sourceImm (s : Fin 64) : BitVec 12 := BitVec.ofNat 12 (2048+64*s.val)
def destImm (s : Fin 128) : BitVec 12 := BitVec.ofNat 12 (2048+32*s.val)

def Atom.op : Atom → Instr
  | .advanceSource => .ADD .x18 .x18 .x22
  | .advanceDst => .ADD .x19 .x19 .x22
  | .source i => .ADDI .x10 .x18 (sourceImm i)
  | .dest i => .ADDI .x12 .x19 (destImm i)
  | .labelRight => .SH .x10 .x23 62
  | .compress => .ECALL
  | .continueAtDst => .ADDI .x10 .x12 0
  | .saveWide => .SH .x12 .x17 30
  | .loadTop => .LD .x6 .x12 24
  | .reduceTop => .REMU .x6 .x6 .x21
  | .storeTop => .SD .x12 .x6 24
  | .loadNarrow => .LHU .x6 .x12 28
  | .fillNarrow => .OR .x6 .x6 .x21
  | .saveNarrow => .SW .x12 .x6 28

def Atom.word : Atom → BitVec 32
  | .advanceSource => 0x01690933
  | .advanceDst => 0x016989b3
  | .source i => BitVec.ofNat 32 ((2048+64*i.val)*2^20+0x90513)
  | .dest i => BitVec.ofNat 32 ((2048+32*i.val)*2^20+0x98613)
  | .labelRight => 0x03751f23
  | .compress => 0x73
  | .continueAtDst => 0x60513
  | .saveWide => 0x01161f23
  | .loadTop => 0x01863303
  | .reduceTop => 0x03537333
  | .storeTop => 0x00663c23
  | .loadNarrow => 0x01c65303
  | .fillNarrow => 0x01536333
  | .saveNarrow => 0x00662e23

private def baseOnly : Option Instruction → Option Instr
  | some (.base op) => some op
  | _ => none

theorem Atom.decoded (a : Atom) : decodeInstruction a.word = some (.base a.op) := by
  have all : baseOnly (decodeInstruction a.word) = some a.op := by
    cases a
    case source j => exact (by decide : ∀ j : Fin 64, baseOnly (decodeInstruction (Atom.source j).word) = some (Atom.source j).op) _
    case dest j => exact (by decide : ∀ j : Fin 128, baseOnly (decodeInstruction (Atom.dest j).word) = some (Atom.dest j).op) _
    all_goals rfl
  cases v : decodeInstruction a.word with
  | none => rw [v] at all; cases all
  | some i => cases i <;> simp_all [baseOnly]

def shifts (i : Nat) : List Atom :=
  (if i≠0 ∧ i%64=0 then [.advanceSource] else []) ++
  (if i≠0 ∧ i%128=0 then [.advanceDst] else [])

def mark (d : Nat) : List Atom := if modulus (d+1) = 0 then [] else [.labelRight]
def rehash (d : Nat) : List Atom := if 1 < work d then .continueAtDst :: List.replicate (work d-1) .compress else []
def save (d : Nat) : List Atom :=
  if width d = 240 then [.saveWide] else if modulus d ≠ 0 then [.loadTop,.reduceTop,.storeTop]
  else if width d < 240 then [.loadNarrow,.fillNarrow,.saveNarrow] else []

def body (d i : Nat) : List Atom := shifts i ++ [.source ⟨i%64,by omega⟩] ++ mark d ++
  [.dest ⟨i%128,by omega⟩,.compress] ++ rehash d ++ save d

def unroll (d : Nat) := min (2^d) 512

def levelStart (d : Nat) := [150115,150099,150074,150033,149960,149823,149558,148908,145054,
  137353,129135,120917,112699,104993,97287,90093,83411,76729,71071,66437,62316,59219,56123,53027][d]?.getD 0

def start (d i : Nat) := levelStart d + (body d 0).length*i + (i-1)/64 + (i-1)/128

def readAt (i : Nat) : BitVec 32 := if h : i < 150132 then Artifact.commitCode.get 32 ⟨i,h⟩ else 0

def Check (d i : Nat) : Bool := ((body d i).zipIdx).all (fun row => readAt (start d i+row.2) == row.1.word)

theorem fetch_of_check {d i : Nat} (check : Check d i = true)
    {idx : Nat} (idxIn : idx < (body d i).length)
    (pcIn : start d i+idx < 150132) (s : MachineState)
    (pc : s.pc = CommitBlocks.addr (start d i+idx)) :
    fetch CommitSetup.im s = some (.base ((body d i)[idx]).op) := by
  have elem : ((body d i)[idx],idx) ∈ (body d i).zipIdx := by
    exact List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem idxIn)
  have same := beq_iff_eq.1 (List.all_eq_true.1 check _ elem)
  apply CommitSetup.fetch_at ⟨start d i+idx,pcIn⟩ _ _ s pc
  rw [show Artifact.commitCode.get 32 ⟨start d i+idx,pcIn⟩ = ((body d i)[idx]).word by simpa only [readAt,pcIn,dite_true] using same]
  exact Atom.decoded _

end CommitGolfCandidate.Reconstruction.CommitParents.Image
