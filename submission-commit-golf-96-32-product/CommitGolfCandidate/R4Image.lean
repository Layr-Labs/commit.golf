import CommitGolf.Artifact
import CommitGolfCandidate.R4Tree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
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

private theorem commit_fetch_rand_words_0 (k : Fin 128) (j : Fin 2) :
    Artifact.commitCode.get 32 ⟨16 + 2 * (0 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_1 (k : Fin 128) (j : Fin 2) :
    Artifact.commitCode.get 32 ⟨16 + 2 * (128 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_2 (k : Fin 128) (j : Fin 2) :
    Artifact.commitCode.get 32 ⟨16 + 2 * (256 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_3 (k : Fin 128) (j : Fin 2) :
    Artifact.commitCode.get 32 ⟨16 + 2 * (384 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 512) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randPairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (16 + 2 * k + j) (by omega)
    (randPairWord j) hpc _ (randPairInstr j) (decode_randPairWord ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_rand_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    by_cases h1 : k < 256
    · have := commit_fetch_rand_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
      simpa [show 128 + (k - 128) = k by omega] using this
    ·
      by_cases h2 : k < 384
      · have := commit_fetch_rand_words_2 ⟨k - 256, by omega⟩ ⟨j, hj⟩
        simpa [show 256 + (k - 256) = k by omega] using this
      ·
        have := commit_fetch_rand_words_3 ⟨k - 384, by omega⟩ ⟨j, hj⟩
        simpa [show 384 + (k - 384) = k by omega] using this

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

private theorem commit_fetch_leaf0_words_0 (k : Fin 128) (j : Fin 3) :
    Artifact.commitCode.get 32 ⟨1051 + 3 * (0 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

private theorem commit_fetch_leaf0_words_1 (k : Fin 128) (j : Fin 3) :
    Artifact.commitCode.get 32 ⟨1051 + 3 * (128 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 256) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1051 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (1051 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_leaf0_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf0_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
    simpa [show 128 + (k - 128) = k by omega] using this

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

private theorem commit_fetch_leaf12_words_0 (k : Fin 32) (j : Fin 12) :
    Artifact.commitCode.get 32 ⟨1828 + 12 * (0 + k.val) + j.val, by omega⟩ = leaf12PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_leaf12_words_1 (k : Fin 32) (j : Fin 12) :
    Artifact.commitCode.get 32 ⟨1828 + 12 * (32 + k.val) + j.val, by omega⟩ = leaf12PairWord j.val := by
  revert k j; decide

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1828 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12PairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (1828 + 12 * k + j) (by omega)
    (leaf12PairWord j) hpc _ (leaf12PairInstr j) (decode_leaf12PairWord ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_leaf12_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf12_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

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

private theorem commit_fetch_leaf3_words_0 (k : Fin 64) (j : Fin 6) :
    Artifact.commitCode.get 32 ⟨2605 + 6 * (0 + k.val) + j.val, by omega⟩ = leaf3PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_leaf3_words_1 (k : Fin 64) (j : Fin 6) :
    Artifact.commitCode.get 32 ⟨2605 + 6 * (64 + k.val) + j.val, by omega⟩ = leaf3PairWord j.val := by
  revert k j; decide

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (2605 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3PairInstr j) := by
  apply fetch_of_packed_word Artifact.commitCode _ state (2605 + 6 * k + j) (by omega)
    (leaf3PairWord j) hpc _ (leaf3PairInstr j) (decode_leaf3PairWord ⟨j, hj⟩)
  by_cases h0 : k < 64
  · simpa using commit_fetch_leaf3_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf3_words_1 ⟨k - 64, by omega⟩ ⟨j, hj⟩
    simpa [show 64 + (k - 64) = k by omega] using this

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
  | 1040 => .base (.BNE .x10 .x19 (4096#13))
  | 1041 => .base (.ADDI .x5 .x0 (0#12))
  | 1042 => .base (.ADDI .x11 .x0 (96#12))
  | 1043 => .base (.ADDI .x13 .x0 (0#12))
  | 1044 => .base (.ADDI .x10 .x8 (3840#12))
  | 1045 => .base (.ADDI .x6 .x0 (1023#12))
  | 1046 => .base (.SLLI .x6 .x6 (11#6))
  | 1047 => .base (.ADDI .x6 .x6 (2047#12))
  | 1048 => .base (.SLLI .x6 .x6 (11#6))
  | 1049 => .base (.ADDI .x6 .x6 (1792#12))
  | 1050 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid0Instr (i : Fin 11) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨1040 + i.val, by omega⟩) =
      some (commitMid0Instr (1040 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 1040 ≤ idx) (hhi : idx < 1051)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  have h := decode_commitMid0Instr ⟨idx - 1040, by omega⟩
  have heq : 1040 + (idx - 1040) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1AInstr : Nat → Instruction
  | 1819 => .base (.BNE .x10 .x19 (5120#13))
  | 1820 => .base (.ADDI .x10 .x8 (4000#12))
  | 1821 => .base (.ADDI .x12 .x18 (4064#12))
  | 1822 => .base (.ADDI .x6 .x0 (1023#12))
  | 1823 => .base (.SLLI .x6 .x6 (11#6))
  | 1824 => .base (.ADDI .x6 .x6 (2047#12))
  | 1825 => .base (.SLLI .x6 .x6 (11#6))
  | 1826 => .base (.ADDI .x6 .x6 (1952#12))
  | 1827 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1AInstr (i : Fin 9) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨1819 + i.val, by omega⟩) =
      some (commitMid1AInstr (1819 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 1819 ≤ idx) (hhi : idx < 1828)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  have h := decode_commitMid1AInstr ⟨idx - 1819, by omega⟩
  have heq : 1819 + (idx - 1819) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1BInstr : Nat → Instruction
  | 2596 => .base (.BNE .x10 .x19 (5120#13))
  | 2597 => .base (.ADDI .x10 .x18 (4000#12))
  | 2598 => .base (.ADDI .x12 .x9 (4064#12))
  | 2599 => .base (.ADDI .x6 .x0 (367#12))
  | 2600 => .base (.SLLI .x6 .x6 (11#6))
  | 2601 => .base (.ADDI .x6 .x6 (2047#12))
  | 2602 => .base (.SLLI .x6 .x6 (11#6))
  | 2603 => .base (.ADDI .x6 .x6 (1952#12))
  | 2604 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1BInstr (i : Fin 9) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨2596 + i.val, by omega⟩) =
      some (commitMid1BInstr (2596 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 2596 ≤ idx) (hhi : idx < 2605)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  have h := decode_commitMid1BInstr ⟨idx - 2596, by omega⟩
  have heq : 2596 + (idx - 2596) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed Artifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1CInstr (_ : Nat) : Instruction := .base (.BNE .x10 .x19 (5120#13))
theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (lo : 3373 ≤ idx) (hi : idx < 3374)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  have eq : idx=3373:=by omega
  subst idx
  exact fetch_of_packed Artifact.commitCode _ state 3373 (by decide) pc _ (by decide)

end CommitGolfCandidate.R4
