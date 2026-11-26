import CommitGolfCandidate.R4aROM
import CommitGolfCandidate.R4Tree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
set_option Elab.async false

namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := Artifact.submission

theorem commit_dataBase : dataBase (submission.image .commit) = 68719476736 := rfl

theorem getElem?_decode (bits : Nat) {count : Nat} (packed : ArtifactEncoding.Packed count)
    (index : Nat) (inside : index < count) :
    (ArtifactEncoding.decode bits packed)[index]? = some (packed.get bits ⟨index, inside⟩) := by
  simp [ArtifactEncoding.decode, inside]

theorem fetch_of_packed {count : Nat} (code : ArtifactEncoding.Packed count) (data : List Byte)
    (state : MachineState) (idx : Nat) (inside : idx < count)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (instr : Instruction)
    (hdec : decodeInstruction (code.get 32 ⟨idx, inside⟩) = some instr)
    (hsmall : 0x1000 + 4 * idx < 2 ^ 64 := by omega) :
    fetch ⟨ArtifactEncoding.decode 32 code, data⟩ state = some instr := by
  unfold fetch
  have hpc_nat : state.pc.toNat = 0x1000 + 4 * idx := by
    rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  have hge : 0x1000 ≤ state.pc.toNat := by omega
  have hmod : state.pc.toNat % 4 = 0 := by omega
  have hidx : (state.pc.toNat - 0x1000) / 4 = idx := by omega
  simp only [hge, hmod, and_self, ite_true, hidx, getElem?_decode 32 code idx inside, hdec]

theorem fetch_of_packed_word {count : Nat} (code : ArtifactEncoding.Packed count) (data : List Byte)
    (state : MachineState) (idx : Nat) (inside : idx < count) (w : BitVec 32)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hword : code.get 32 ⟨idx, inside⟩ = w)
    (instr : Instruction)
    (hdec : decodeInstruction w = some instr)
    (hsmall : 0x1000 + 4 * idx < 2 ^ 64 := by omega) :
    fetch ⟨ArtifactEncoding.decode 32 code, data⟩ state = some instr := by
  refine fetch_of_packed code data state idx inside hpc instr ?_ hsmall
  rw [hword, hdec]

private def instDecEqInstruction : DecidableEq Instruction := fun a b =>
  match a, b with
  | .base i1, .base i2 =>
      if h : i1 = i2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .word o1 d1 s1 t1, .word o2 d2 s2 t2 =>
      if h : o1 = o2 ∧ d1 = d2 ∧ s1 = s2 ∧ t1 = t2 then
        isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl)
      else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl⟩)
  | .sraiw d1 s1 sh1, .sraiw d2 s2 sh2 =>
      if h : d1 = d2 ∧ s1 = s2 ∧ sh1 = sh2 then
        isTrue (by rcases h with ⟨rfl, rfl, rfl⟩; rfl)
      else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl⟩)
  | .base _, .word .. | .base _, .sraiw .. | .word .., .base _ | .word .., .sraiw ..
  | .sraiw .., .base _ | .sraiw .., .word .. => isFalse (by intro h; cases h)

local instance : DecidableEq Instruction := instDecEqInstruction

/-! ### Commit Program: Constant-Body Repeating Bulk Loops -/

def randPairWord : Nat → BitVec 32
  | 0 => 0x00000073#32
  | 1 => 0x0b850513#32
  | _ => 0#32

def randPairInstr : Nat → Instruction
  | 0 => .base .ECALL
  | 1 => .base (.ADDI .x10 .x10 (184#12))
  | _ => .base .EBREAK

theorem decode_randPairWord (j : Fin 2) :
    decodeInstruction (randPairWord j.val) = some (randPairInstr j.val) := by
  revert j; decide

private theorem randChunks : ROM.bankChunks 16 32783 2 := by decide +kernel
private theorem randWords : ROM.bankWords 16 32783 2 randPairWord := by decide +kernel

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 16384) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randPairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (16 + 2 * k + j) (by omega)
    (randPairWord j) hpc _ (randPairInstr j) (decode_randPairWord ⟨j, hj⟩)
  have v := ROM.bankRead (word := randPairWord) (by simp [ROM.allowed] : ROM.allowed 2) randChunks randWords
    (16 + 2 * k + j) (by omega) (by omega) (by omega)
  rwa [show ((16 + 2 * k + j) - 16) % 2 = j by omega] at v


def leaf0Word : Nat → BitVec 32
  | 0 => 0x10050513#32
  | 1 => 0x04050613#32
  | 2 => 0x00000073#32
  | _ => 0#32

def leaf0Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (256#12))
  | 1 => .base (.ADDI .x12 .x10 (64#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf0Word (j : Fin 3) :
    decodeInstruction (leaf0Word j.val) = some (leaf0Instr j.val) := by
  revert j; decide

private theorem leaf0Chunks : ROM.bankChunks 32797 81948 3 := by decide +kernel
private theorem leaf0Words : ROM.bankWords 32797 81948 3 leaf0Word := by decide +kernel

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 16384) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (32797 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  have v := ROM.bankRead (word := leaf0Word) (by simp [ROM.allowed] : ROM.allowed 3) leaf0Chunks leaf0Words
    (32797 + 3 * k + j) (by omega) (by omega) (by omega)
  rwa [show ((32797 + 3 * k + j) - 32797) % 3 = j by omega] at v


def leaf12PairWord : Nat → BitVec 32
  | 0 => 0x0a050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | 3 => 0x06050513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | 6 => 0x0a050513#32
  | 7 => 0x05860613#32
  | 8 => 0x00000073#32
  | 9 => 0x06050513#32
  | 10 => 0x02060613#32
  | 11 => 0x00000073#32
  | _ => 0#32

def leaf12PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (160#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (96#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | 6 => .base (.ADDI .x10 .x10 (160#12))
  | 7 => .base (.ADDI .x12 .x12 (88#12))
  | 8 => .base .ECALL
  | 9 => .base (.ADDI .x10 .x10 (96#12))
  | 10 => .base (.ADDI .x12 .x12 (32#12))
  | 11 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf12PairWord (j : Fin 12) :
    decodeInstruction (leaf12PairWord j.val) = some (leaf12PairInstr j.val) := by
  revert j; decide

private theorem leaf12Chunks : ROM.bankChunks 81960 131111 12 := by decide +kernel
private theorem leaf12Words : ROM.bankWords 81960 131111 12 leaf12PairWord := by decide +kernel

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 4096) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (81960 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12PairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (81960 + 12 * k + j) (by omega)
    (leaf12PairWord j) hpc _ (leaf12PairInstr j) (decode_leaf12PairWord ⟨j, hj⟩)
  have v := ROM.bankRead (word := leaf12PairWord) (by simp [ROM.allowed] : ROM.allowed 12) leaf12Chunks leaf12Words
    (81960 + 12 * k + j) (by omega) (by omega) (by omega)
  rwa [show ((81960 + 12 * k + j) - 81960) % 12 = j by omega] at v


def leaf3PairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | 3 => 0x05850513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | _ => 0#32

def leaf3PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (88#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf3PairWord (j : Fin 6) :
    decodeInstruction (leaf3PairWord j.val) = some (leaf3PairInstr j.val) := by
  revert j; decide

private theorem leaf3Chunks : ROM.bankChunks 131123 180274 6 := by decide +kernel
private theorem leaf3Words : ROM.bankWords 131123 180274 6 leaf3PairWord := by decide +kernel

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 8192) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (131123 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3PairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (131123 + 6 * k + j) (by omega)
    (leaf3PairWord j) hpc _ (leaf3PairInstr j) (decode_leaf3PairWord ⟨j, hj⟩)
  have v := ROM.bankRead (word := leaf3PairWord) (by simp [ROM.allowed] : ROM.allowed 6) leaf3Chunks leaf3Words
    (131123 + 6 * k + j) (by omega) (by omega) (by omega)
  rwa [show ((131123 + 6 * k + j) - 131123) % 6 = j by omega] at v


def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (384#12))
  | 4 => .base (.SLLI .x6 .x6 (11#6))
  | 5 => .base (.SLLI .x6 .x6 (11#6))
  | 6 => .base (.ADDI .x6 .x6 (0#12))
  | 7 => .base (.ADD .x18 .x9 .x6)
  | 8 => .base (.ADDI .x5 .x0 (2#12))
  | 9 => .base (.ADDI .x10 .x18 (72#12))
  | 10 => .base (.ADDI .x11 .x0 (40#12))
  | 11 => .base (.ADDI .x6 .x0 (368#12))
  | 12 => .base (.SLLI .x6 .x6 (11#6))
  | 13 => .base (.SLLI .x6 .x6 (11#6))
  | 14 => .base (.ADDI .x6 .x6 (72#12))
  | 15 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr (i : Fin 16) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 16)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  have h := decode_commitPrefixInstr ⟨idx - 0, by omega⟩
  have heq : 0 + (idx - 0) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid0Instr : Nat → Instruction
  | 32786 => .base (.ADDI .x0 .x0 0)
  | 32787 => .base (.ADDI .x5 .x0 (0#12))
  | 32788 => .base (.ADDI .x11 .x0 (96#12))
  | 32789 => .base (.ADDI .x13 .x0 (0#12))
  | 32790 => .base (.ADDI .x10 .x8 (3840#12))
  | 32791 => .base (.ADDI .x6 .x0 (1023#12))
  | 32792 => .base (.SLLI .x6 .x6 (11#6))
  | 32793 => .base (.ADDI .x6 .x6 (2047#12))
  | 32794 => .base (.SLLI .x6 .x6 (11#6))
  | 32795 => .base (.ADDI .x6 .x6 (1792#12))
  | 32796 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid0Instr (i : Fin 11) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨32786 + i.val, by omega⟩) =
      some (commitMid0Instr (32786 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 32786 ≤ idx) (hhi : idx < 32797)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  have h := decode_commitMid0Instr ⟨idx - 32786, by omega⟩
  have heq : 32786 + (idx - 32786) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1AInstr : Nat → Instruction
  | 81951 => .base (.ADDI .x0 .x0 0)
  | 81952 => .base (.ADDI .x10 .x8 (4000#12))
  | 81953 => .base (.ADDI .x12 .x18 (4064#12))
  | 81954 => .base (.ADDI .x6 .x0 (1023#12))
  | 81955 => .base (.SLLI .x6 .x6 (11#6))
  | 81956 => .base (.ADDI .x6 .x6 (2047#12))
  | 81957 => .base (.SLLI .x6 .x6 (11#6))
  | 81958 => .base (.ADDI .x6 .x6 (1952#12))
  | 81959 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1AInstr (i : Fin 9) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨81951 + i.val, by omega⟩) =
      some (commitMid1AInstr (81951 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 81951 ≤ idx) (hhi : idx < 81960)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  have h := decode_commitMid1AInstr ⟨idx - 81951, by omega⟩
  have heq : 81951 + (idx - 81951) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1BInstr : Nat → Instruction
  | 131114 => .base (.ADDI .x0 .x0 0)
  | 131115 => .base (.ADDI .x10 .x18 (4000#12))
  | 131116 => .base (.ADDI .x12 .x9 (4064#12))
  | 131117 => .base (.ADDI .x6 .x0 (367#12))
  | 131118 => .base (.SLLI .x6 .x6 (11#6))
  | 131119 => .base (.ADDI .x6 .x6 (2047#12))
  | 131120 => .base (.SLLI .x6 .x6 (11#6))
  | 131121 => .base (.ADDI .x6 .x6 (1952#12))
  | 131122 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1BInstr (i : Fin 9) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨131114 + i.val, by omega⟩) =
      some (commitMid1BInstr (131114 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 131114 ≤ idx) (hhi : idx < 131123)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  have h := decode_commitMid1BInstr ⟨idx - 131114, by omega⟩
  have heq : 131114 + (idx - 131114) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h


def lpc (i : Nat) := BitVec.ofNat 64 (0x1000 + 4 * i)
def longOff (n first : Nat) := BitVec.ofInt 21 (4 * ((first : Int) - (n + 1 : Nat)))
def longOp (n : Nat) (ins : Instr) : Bool :=
  if h : n < 262123 then
    match decodeInstruction (Artifact.commitCode.get 32 ⟨n,h⟩) with
    | some (.base i) => decide (i = ins)
    | _ => false
  else false

def LongSite (n first : Nat) : Prop :=
  longOp n (.BEQ .x10 .x19 8) ∧ longOp (n+1) (.JAL .x0 (longOff n first)) ∧
  longOp (n+2) (.ADDI .x0 .x0 0) ∧ lpc (n+1) + signExtend21 (longOff n first) = lpc first
instance (n first : Nat) : Decidable (LongSite n first) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem fetchLong {n : Nat} {ins : Instr} (s : MachineState) (pc : s.pc = lpc n)
    (h : longOp n ins) : fetch (submission.image .commit) s = some (.base ins) := by
  unfold longOp at h
  split at h
  next small =>
    apply fetch_of_packed Artifact.commitCode _ s n small pc
    split at h
    next i eq =>
      have same := of_decide_eq_true h
      rw [same] at eq
      exact eq
    next => contradiction
  next => contradiction

end CommitGolfCandidate.R4
