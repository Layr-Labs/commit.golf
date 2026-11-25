import CommitGolfCandidate.Check
import CommitGolfCandidate.HeapLayout

/-! Decoded instruction table and in-place leaf chain execution for the unrolled
commitment image. The leaf loop processes 32 leaves per iteration as four 8-leaf chunks
(with `x29 = 2048` advancing `x8` after each chunk); within chunk `c < 4` and lane
`k < 8`, leaf `8*c + k` reads its salt from `x18 + 256*c + 32*k`, hashes in place at
`x8 + 256*k`, and writes its digest into `x23 + 384*c + heapOffset k`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000 in
private theorem signExtend12_mul8_fin :
    ∀ m : Fin 256, signExtend12 (BitVec.ofNat 12 (8 * m.val)) = BitVec.ofNat 64 (8 * m.val) := by
  decide

/-- Sign-extending any nonnegative 8-byte-aligned 12-bit offset preserves its value. -/
theorem signExtend12_ofNat_mul8 (n : Nat) (h : n < 2048) (h8 : n % 8 = 0) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  have hfin := signExtend12_mul8_fin ⟨n / 8, by omega⟩
  have heq : 8 * (n / 8) = n := by omega
  rw [heq] at hfin
  exact hfin

theorem pc_add_steps (n k m : Nat) (h : m = n + k) :
    BitVec.ofNat 64 (4096 + 4 * n) + BitVec.ofNat 64 (4 * k) = BitVec.ofNat 64 (4096 + 4 * m) := by
  rw [← BitVec.ofNat_add]
  congr 1
  omega

/-- Decoded instructions of one 4-word digest copy. -/
def commitCopyInstructions (src dst : Reg) (srcOff dstOff : Nat) : List Instr :=
  [.LD .x6 src (BitVec.ofNat 12 srcOff), .SD dst .x6 (BitVec.ofNat 12 dstOff),
   .LD .x6 src (BitVec.ofNat 12 (srcOff + 8)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 8)),
   .LD .x6 src (BitVec.ofNat 12 (srcOff + 16)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 16)),
   .LD .x6 src (BitVec.ofNat 12 (srcOff + 24)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 24))]

/-- The two pointer instructions before in-place call `j` of lane `k` in chunk `c`. -/
def chainCallInstructions (c k j : Nat) : List Instr :=
  [.ADDI .x10 .x8 (BitVec.ofNat 12 (64 * j + 256 * k)),
   if j = 3 then .ADDI .x12 .x23 (BitVec.ofNat 12 (384 * c + heapOffset k))
   else .ADDI .x12 .x8 (BitVec.ofNat 12 (64 * j + 64 + 256 * k))]

def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 4064, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 384,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x18 .x9 .x6,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 192,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0,
   .ADDI .x11 .x0 0, .SLLI .x11 .x11 11, .ADDI .x11 .x11 128,
   .SLLI .x11 .x11 11, .ADDI .x11 .x11 0, .SLLI .x11 .x11 11, .ADDI .x11 .x11 0]

def commitReadyInstructions : List Instr :=
  [.ADDI .x20 .x0 0, .SLLI .x20 .x20 11, .ADDI .x20 .x20 256,
   .SLLI .x20 .x20 11, .ADDI .x20 .x20 0,
   .ADDI .x29 .x0 1, .SLLI .x29 .x29 11,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0]

def commitNextInstructions : List Instr :=
  [.ADDI .x18 .x18 1024, .ADDI .x23 .x23 1536, .ADDI .x20 .x20 4095]

def parentStartInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 383, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 512, .ADD .x21 .x9 .x6,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 191, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 1280, .ADD .x22 .x9 .x6]

/-- The two pointer instructions before parent call `j` (descending from `q = 15 - j`),
either in the 16-parent loop (`isTail = false`) or the 15-parent root tail (`isTail = true`). -/
def parentCallInstructions (isTail : Bool) (j : Nat) : List Instr :=
  let q := 15 - j
  [.ADDI .x10 (if isTail then .x9 else .x21) (BitVec.ofNat 12 (96 * q)),
   .ADDI .x12 (if isTail then .x9 else .x22) (BitVec.ofNat 12 (heapOffset q))]

def parentNextInstructions : List Instr :=
  [.ADDI .x21 .x21 2560, .ADDI .x22 .x22 3328]

def commitExitInstructions : List Instr :=
  [.ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL]

/-- Closed-form decoded instruction at every PC index `0 .. 810` of the commitment image. -/
def commitInstrAt (index : Nat) : Option Instr :=
  if index < 28 then commitSetupInstructions[index]?
  else if index = 28 then some .ECALL
  else if index < 39 then commitReadyInstructions[index - 29]?
  else if index < 683 then
    let pos := index - 39
    let c := pos / 161
    let rem := pos % 161
    if rem < 160 then
      let k := rem / 20
      let off := rem % 20
      if off < 8 then (commitCopyInstructions .x18 .x8 (256 * c + 32 * k) (256 * k))[off]?
      else
        let j := (off - 8) / 3
        let s := (off - 8) % 3
        if s < 2 then (chainCallInstructions c k j)[s]?
        else some .ECALL
    else some (.ADD .x8 .x8 .x29)
  else if index < 686 then commitNextInstructions[index - 683]?
  else if index = 686 then some (.BNE .x20 .x0 5604)
  else if index < 703 then parentStartInstructions[index - 687]?
  else if index = 703 then some (.BEQ .x22 .x9 208)
  else if index < 752 then
    let pos := index - 704
    let j := pos / 3
    let s := pos % 3
    if s < 2 then (parentCallInstructions false j)[s]?
    else some .ECALL
  else if index < 754 then parentNextInstructions[index - 752]?
  else if index = 754 then some (.BNE .x22 .x9 7992)
  else if index < 800 then
    let pos := index - 755
    let j := pos / 3
    let s := pos % 3
    if s < 2 then (parentCallInstructions true j)[s]?
    else some .ECALL
  else if index < 808 then (commitCopyInstructions .x9 .x26 32 0)[index - 800]?
  else if index < 811 then commitExitInstructions[index - 808]?
  else none

private def tabulate {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | start, count + 1 => f start :: tabulate f (start + 1) count

private theorem map_getElem?_eq {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.map f)[n]? = (l[n]?).map f := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

private theorem tabulate_getElem? {α : Type} (f : Nat → α) (start count idx : Nat)
    (h : idx < count) :
    (tabulate f start count)[idx]? = some (f (start + idx)) := by
  induction count generalizing start idx with
  | zero => omega
  | succ count ih =>
    cases idx with
    | zero => rfl
    | succ idx =>
      change (tabulate f (start + 1) count)[idx]? = some (f (start + (idx + 1)))
      rw [ih (start + 1) idx (by omega), show start + 1 + idx = start + (idx + 1) by omega]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- Single-pass kernel verification that every one of the 811 encoded words of the
commitment image decodes to `commitInstrAt`. -/
theorem commit_code_decoded :
    (submission.image .commit).code.map decodeInstruction =
      tabulate (fun i => (commitInstrAt i).map Instruction.base) 0 811 := by
  rfl

theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 811) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : commitInstrAt index = some instruction) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  have hmap := congrArg (fun l => l[index]?) commit_code_decoded
  rw [map_getElem?_eq, tabulate_getElem? _ 0 811 index indexBound] at hmap
  simp only [Nat.zero_add, decoded] at hmap
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at hmap
  | some word =>
    simp [h] at hmap ⊢
    exact hmap

theorem commit_instr_leaf_copy (c k i : Nat) (hc : c < 4) (hk : k < 8) (hi : i < 8) :
    commitInstrAt (39 + 161 * c + 20 * k + i) =
      (commitCopyInstructions .x18 .x8 (256 * c + 32 * k) (256 * k))[i]? := by
  unfold commitInstrAt
  have h1 : ¬ (39 + 161 * c + 20 * k + i < 28) := by omega
  have h2 : ¬ (39 + 161 * c + 20 * k + i = 28) := by omega
  have h3 : ¬ (39 + 161 * c + 20 * k + i < 39) := by omega
  have h4 : 39 + 161 * c + 20 * k + i < 683 := by omega
  have hpos : 39 + 161 * c + 20 * k + i - 39 = 161 * c + 20 * k + i := by omega
  have hdivc : (161 * c + 20 * k + i) / 161 = c := by omega
  have hmodc : (161 * c + 20 * k + i) % 161 = 20 * k + i := by omega
  have hrem : 20 * k + i < 160 := by omega
  have hdivk : (20 * k + i) / 20 = k := by omega
  have hmodk : (20 * k + i) % 20 = i := by omega
  simp only [h1, h2, h3, h4, hpos, hdivc, hmodc, hrem, hdivk, hmodk, hi, ↓reduceIte]

theorem commit_instr_chain_setup (c k j i : Nat) (hc : c < 4) (hk : k < 8)
    (hj : j < 4) (hi : i < 2) :
    commitInstrAt (47 + 161 * c + 20 * k + 3 * j + i) =
      (chainCallInstructions c k j)[i]? := by
  unfold commitInstrAt
  have h1 : ¬ (47 + 161 * c + 20 * k + 3 * j + i < 28) := by omega
  have h2 : ¬ (47 + 161 * c + 20 * k + 3 * j + i = 28) := by omega
  have h3 : ¬ (47 + 161 * c + 20 * k + 3 * j + i < 39) := by omega
  have h4 : 47 + 161 * c + 20 * k + 3 * j + i < 683 := by omega
  have hpos : 47 + 161 * c + 20 * k + 3 * j + i - 39 = 161 * c + 20 * k + (8 + 3 * j + i) := by omega
  have hdivc : (161 * c + 20 * k + (8 + 3 * j + i)) / 161 = c := by omega
  have hmodc : (161 * c + 20 * k + (8 + 3 * j + i)) % 161 = 20 * k + (8 + 3 * j + i) := by omega
  have hrem : 20 * k + (8 + 3 * j + i) < 160 := by omega
  have hdivk : (20 * k + (8 + 3 * j + i)) / 20 = k := by omega
  have hmodk : (20 * k + (8 + 3 * j + i)) % 20 = 8 + 3 * j + i := by omega
  have hoff : ¬ (8 + 3 * j + i < 8) := by omega
  have hsub : 8 + 3 * j + i - 8 = 3 * j + i := by omega
  have hdivj : (3 * j + i) / 3 = j := by omega
  have hmodj : (3 * j + i) % 3 = i := by omega
  simp only [h1, h2, h3, h4, hpos, hdivc, hmodc, hrem, hdivk, hmodk, hoff, hsub, hdivj, hmodj,
    hi, ↓reduceIte]

theorem commit_instr_chain_ecall (c k j : Nat) (hc : c < 4) (hk : k < 8) (hj : j < 4) :
    commitInstrAt (49 + 161 * c + 20 * k + 3 * j) = some .ECALL := by
  unfold commitInstrAt
  have h1 : ¬ (49 + 161 * c + 20 * k + 3 * j < 28) := by omega
  have h2 : ¬ (49 + 161 * c + 20 * k + 3 * j = 28) := by omega
  have h3 : ¬ (49 + 161 * c + 20 * k + 3 * j < 39) := by omega
  have h4 : 49 + 161 * c + 20 * k + 3 * j < 683 := by omega
  have hpos : 49 + 161 * c + 20 * k + 3 * j - 39 = 161 * c + 20 * k + (10 + 3 * j) := by omega
  have hdivc : (161 * c + 20 * k + (10 + 3 * j)) / 161 = c := by omega
  have hmodc : (161 * c + 20 * k + (10 + 3 * j)) % 161 = 20 * k + (10 + 3 * j) := by omega
  have hrem : 20 * k + (10 + 3 * j) < 160 := by omega
  have hdivk : (20 * k + (10 + 3 * j)) / 20 = k := by omega
  have hmodk : (20 * k + (10 + 3 * j)) % 20 = 10 + 3 * j := by omega
  have hoff : ¬ (10 + 3 * j < 8) := by omega
  have hsub : 10 + 3 * j - 8 = 3 * j + 2 := by omega
  have hmodj : (3 * j + 2) % 3 = 2 := by omega
  have hns : ¬ (2 < 2) := by omega
  simp only [h1, h2, h3, h4, hpos, hdivc, hmodc, hrem, hdivk, hmodk, hoff, hsub, hmodj, hns,
    ↓reduceIte]

theorem commit_instr_chunk_advance (c : Nat) (hc : c < 4) :
    commitInstrAt (199 + 161 * c) = some (.ADD .x8 .x8 .x29) := by
  unfold commitInstrAt
  have h1 : ¬ (199 + 161 * c < 28) := by omega
  have h2 : ¬ (199 + 161 * c = 28) := by omega
  have h3 : ¬ (199 + 161 * c < 39) := by omega
  have h4 : 199 + 161 * c < 683 := by omega
  have hpos : 199 + 161 * c - 39 = 161 * c + 160 := by omega
  have hmodc : (161 * c + 160) % 161 = 160 := by omega
  have hrem : ¬ (160 < 160) := by omega
  simp only [h1, h2, h3, h4, hpos, hmodc, hrem, ↓reduceIte]

theorem commit_instr_parent_setup (isTail : Bool) (j i : Nat)
    (hj : j < if isTail then 15 else 16) (hi : i < 2) :
    commitInstrAt ((if isTail then 755 else 704) + 3 * j + i) =
      (parentCallInstructions isTail j)[i]? := by
  cases isTail with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hj ⊢
    unfold commitInstrAt
    have h1 : ¬ (704 + 3 * j + i < 28) := by omega
    have h2 : ¬ (704 + 3 * j + i = 28) := by omega
    have h3 : ¬ (704 + 3 * j + i < 39) := by omega
    have h4 : ¬ (704 + 3 * j + i < 683) := by omega
    have h5 : ¬ (704 + 3 * j + i < 686) := by omega
    have h6 : ¬ (704 + 3 * j + i = 686) := by omega
    have h7 : ¬ (704 + 3 * j + i < 703) := by omega
    have h8 : ¬ (704 + 3 * j + i = 703) := by omega
    have h9 : 704 + 3 * j + i < 752 := by omega
    have hpos : 704 + 3 * j + i - 704 = 3 * j + i := by omega
    have hdiv : (3 * j + i) / 3 = j := by omega
    have hmod : (3 * j + i) % 3 = i := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hpos, hdiv, hmod, hi, ↓reduceIte]
  | true =>
    simp only [↓reduceIte] at hj ⊢
    unfold commitInstrAt
    have h1 : ¬ (755 + 3 * j + i < 28) := by omega
    have h2 : ¬ (755 + 3 * j + i = 28) := by omega
    have h3 : ¬ (755 + 3 * j + i < 39) := by omega
    have h4 : ¬ (755 + 3 * j + i < 683) := by omega
    have h5 : ¬ (755 + 3 * j + i < 686) := by omega
    have h6 : ¬ (755 + 3 * j + i = 686) := by omega
    have h7 : ¬ (755 + 3 * j + i < 703) := by omega
    have h8 : ¬ (755 + 3 * j + i = 703) := by omega
    have h9 : ¬ (755 + 3 * j + i < 752) := by omega
    have h10 : ¬ (755 + 3 * j + i < 754) := by omega
    have h11 : ¬ (755 + 3 * j + i = 754) := by omega
    have h12 : 755 + 3 * j + i < 800 := by omega
    have hpos : 755 + 3 * j + i - 755 = 3 * j + i := by omega
    have hdiv : (3 * j + i) / 3 = j := by omega
    have hmod : (3 * j + i) % 3 = i := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpos, hdiv, hmod, hi, ↓reduceIte]

theorem commit_instr_parent_ecall (isTail : Bool) (j : Nat)
    (hj : j < if isTail then 15 else 16) :
    commitInstrAt ((if isTail then 755 else 704) + 3 * j + 2) = some .ECALL := by
  cases isTail with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hj ⊢
    unfold commitInstrAt
    have h1 : ¬ (704 + 3 * j + 2 < 28) := by omega
    have h2 : ¬ (704 + 3 * j + 2 = 28) := by omega
    have h3 : ¬ (704 + 3 * j + 2 < 39) := by omega
    have h4 : ¬ (704 + 3 * j + 2 < 683) := by omega
    have h5 : ¬ (704 + 3 * j + 2 < 686) := by omega
    have h6 : ¬ (704 + 3 * j + 2 = 686) := by omega
    have h7 : ¬ (704 + 3 * j + 2 < 703) := by omega
    have h8 : ¬ (704 + 3 * j + 2 = 703) := by omega
    have h9 : 704 + 3 * j + 2 < 752 := by omega
    have hpos : 704 + 3 * j + 2 - 704 = 3 * j + 2 := by omega
    have hmod : (3 * j + 2) % 3 = 2 := by omega
    have hns : ¬ (2 < 2) := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hpos, hmod, hns, ↓reduceIte]
  | true =>
    simp only [↓reduceIte] at hj ⊢
    unfold commitInstrAt
    have h1 : ¬ (755 + 3 * j + 2 < 28) := by omega
    have h2 : ¬ (755 + 3 * j + 2 = 28) := by omega
    have h3 : ¬ (755 + 3 * j + 2 < 39) := by omega
    have h4 : ¬ (755 + 3 * j + 2 < 683) := by omega
    have h5 : ¬ (755 + 3 * j + 2 < 686) := by omega
    have h6 : ¬ (755 + 3 * j + 2 = 686) := by omega
    have h7 : ¬ (755 + 3 * j + 2 < 703) := by omega
    have h8 : ¬ (755 + 3 * j + 2 = 703) := by omega
    have h9 : ¬ (755 + 3 * j + 2 < 752) := by omega
    have h10 : ¬ (755 + 3 * j + 2 < 754) := by omega
    have h11 : ¬ (755 + 3 * j + 2 = 754) := by omega
    have h12 : 755 + 3 * j + 2 < 800 := by omega
    have hpos : 755 + 3 * j + 2 - 755 = 3 * j + 2 := by omega
    have hmod : (3 * j + 2) % 3 = 2 := by omega
    have hns : ¬ (2 < 2) := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpos, hmod, hns, ↓reduceIte]

theorem commit_instr_root_copy (i : Nat) (hi : i < 8) :
    commitInstrAt (800 + i) = (commitCopyInstructions .x9 .x26 32 0)[i]? := by
  unfold commitInstrAt
  have h1 : ¬ (800 + i < 28) := by omega
  have h2 : ¬ (800 + i = 28) := by omega
  have h3 : ¬ (800 + i < 39) := by omega
  have h4 : ¬ (800 + i < 683) := by omega
  have h5 : ¬ (800 + i < 686) := by omega
  have h6 : ¬ (800 + i = 686) := by omega
  have h7 : ¬ (800 + i < 703) := by omega
  have h8 : ¬ (800 + i = 703) := by omega
  have h9 : ¬ (800 + i < 752) := by omega
  have h10 : ¬ (800 + i < 754) := by omega
  have h11 : ¬ (800 + i = 754) := by omega
  have h12 : ¬ (800 + i < 800) := by omega
  have h13 : 800 + i < 808 := by omega
  have hpos : 800 + i - 800 = i := by omega
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hpos, ↓reduceIte]

private def chainCallPrefix (state : MachineState) (c k j count : Nat) : MachineState :=
  ((chainCallInstructions c k j).take count).foldl execInstrBr state

def chainSetupState (state : MachineState) (c k j : Nat) : MachineState :=
  chainCallPrefix state c k j 2

/-- Input address of call `j` of lane `k` (independent of chunk `c`). -/
def chainSource (state : MachineState) (k j : Nat) : Word :=
  state.getReg .x8 + BitVec.ofNat 64 (64 * j + 256 * k)

/-- Output address of call `j` of lane `k` in chunk `c`. -/
def chainOutput (state : MachineState) (c k j : Nat) : Word :=
  if j = 3 then state.getReg .x23 + BitVec.ofNat 64 (384 * c + heapOffset k)
  else state.getReg .x8 + BitVec.ofNat 64 (64 * j + 64 + 256 * k)

/-- State after call `j`: the reply is written at the call's output address. -/
def chainCallState (state : MachineState) (c k j : Nat) (answer : BitVec 256) : MachineState :=
  writeBits (chainSetupState state c k j) (chainOutput state c k j) answer

theorem chain_setup_memory (state : MachineState) (c k j : Nat) :
    (chainSetupState state c k j).mem = state.mem := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;> rfl

theorem chain_setup_register (state : MachineState) (c k j : Nat) (reg : Reg)
    (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainSetupState state c k j).getReg reg = state.getReg reg := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;>
    simp only [List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem chain_setup_registers (state : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4) :
    (chainSetupState state c k j).getReg .x10 = chainSource state k j ∧
    (chainSetupState state c k j).getReg .x12 = chainOutput state c k j ∧
    (chainSetupState state c k j).pc = state.pc + 8 ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → (chainSetupState state c k j).getReg reg = state.getReg reg := by
  have hsrc : signExtend12 (BitVec.ofNat 12 (64 * j + 256 * k)) =
      BitVec.ofNat 64 (64 * j + 256 * k) :=
    signExtend12_ofNat_mul8 _ (by omega) (by omega)
  have hheap : signExtend12 (BitVec.ofNat 12 (384 * c + heapOffset k)) =
      BitVec.ofNat 64 (384 * c + heapOffset k) :=
    signExtend12_ofNat_mul8 _ (by unfold heapOffset; omega) (by unfold heapOffset; omega)
  refine ⟨?_, ?_, ?_, fun reg n10 n12 => chain_setup_register state c k j reg n10 n12⟩
  · by_cases h3 : j = 3
    · subst h3
      simp only [chainSetupState, chainCallPrefix, chainCallInstructions, chainSource,
        ↓reduceIte, List.take, List.foldl, execInstrBr, hsrc, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
    · simp only [chainSetupState, chainCallPrefix, chainCallInstructions, chainSource, h3,
        ↓reduceIte, List.take, List.foldl, execInstrBr, hsrc, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
  · by_cases h3 : j = 3
    · simp only [chainSetupState, chainCallPrefix, chainCallInstructions, chainOutput, h3,
        ↓reduceIte, List.take, List.foldl, execInstrBr, hheap, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x23)]
    · have hnext : signExtend12 (BitVec.ofNat 12 (64 * j + 64 + 256 * k)) =
          BitVec.ofNat 64 (64 * j + 64 + 256 * k) :=
        signExtend12_ofNat_mul8 _ (by omega) (by omega)
      simp only [chainSetupState, chainCallPrefix, chainCallInstructions, chainOutput, h3,
        ↓reduceIte, List.take, List.foldl, execInstrBr, hnext, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x8)]
  · by_cases h3 : j = 3 <;>
      simp only [chainSetupState, chainCallPrefix, chainCallInstructions, h3, ↓reduceIte,
        List.take, List.foldl, execInstrBr, MachineState.pc_setReg, MachineState.setPC,
        BitVec.add_assoc] <;>
      rfl

theorem chain_call_memory (state : MachineState) (c k j : Nat) (answer : BitVec 256) :
    (chainCallState state c k j answer).mem =
      (writeBits state (chainOutput state c k j) answer).mem :=
  write_bits_memory_congr _ _ _ answer (chain_setup_memory state c k j)

theorem chain_call_register (state : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4)
    (answer : BitVec 256) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainCallState state c k j answer).getReg reg = state.getReg reg := by
  rw [chainCallState, writeBits_register]
  exact (chain_setup_registers state c k j hc hk hj).2.2.2 reg n10 n12

theorem chain_call_pc (state : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4) (answer : BitVec 256) :
    (chainCallState state c k j answer).pc = state.pc + 12 := by
  simp only [chainCallState, writeBits, MachineState.setPC]
  rw [(chain_setup_registers state c k j hc hk hj).2.2.1, BitVec.add_assoc]
  rfl

set_option maxHeartbeats 1600000 in
/-- In-place call `j` of lane `k` in chunk `c`: two pointer instructions and one direct
96-byte compression query. Ten cycles and one query, proved symbolically for all lanes. -/
theorem commit_chain_call (state : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k + 3 * j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sourceValid : rangeValid (chainSource state k j) 96 = true)
    (sourceAligned : (chainSource state k j).toNat % 8 = 0)
    (destinationValid : rangeValid (chainOutput state c k j) 32 = true)
    (destinationAligned : (chainOutput state c k j).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (.inl
            (readBuffer state (chainSource state k j).toNat 96)))
          let result ← execute (submission.image .commit) fuel
            (chainCallState state c k j answer) true
          return result.charge 10 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining
              (chainCallPrefix state c k j 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := chainCallPrefix state c k j)
    intro i hi
    refine ⟨.base (((chainCallInstructions c k j)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (47 + 161 * c + 20 * k + 3 * j + i) _ (by omega)
      · interval_cases i
        · simpa [chainCallPrefix] using pc
        · simp only [chainCallPrefix, chainCallInstructions, List.take, List.foldl, execInstrBr,
            MachineState.pc_setReg, MachineState.setPC, pc]
          exact pc_add_steps _ 1 _ (by omega)
      · have hcode := commit_instr_chain_setup c k j i hc hk hj hi
        interval_cases i
        · simpa [chainCallInstructions] using hcode
        · by_cases h3 : j = 3 <;> simpa [chainCallInstructions, h3] using hcode
    · interval_cases i
      · rfl
      · by_cases h3 : j = 3 <;>
          simp [chainCallPrefix, chainCallInstructions, h3, ordinaryStep, memoryArgumentsValid,
            memAccess]
    · interval_cases i
      · rfl
      · by_cases h3 : j = 3 <;> simp [chainCallInstructions, h3, instructionCycles]
  let ready := chainCallPrefix state c k j 2
  have regs := chain_setup_registers state c k j hc hk hj
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (49 + 161 * c + 20 * k + 3 * j)) := by
    change (chainSetupState state c k j).pc = _
    rw [regs.2.2.1, pc]
    exact pc_add_steps _ 2 _ (by omega)
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ (49 + 161 * c + 20 * k + 3 * j) _ (by omega) readyPC
    exact commit_instr_chain_ecall c k j hc hk hj
  have r5' : ready.getReg .x5 = 0 := (regs.2.2.2 .x5 (by decide) (by decide)).trans r5
  have r11' : ready.getReg .x11 = 96 := (regs.2.2.2 .x11 (by decide) (by decide)).trans r11
  have r13' : ready.getReg .x13 = 0 := (regs.2.2.2 .x13 (by decide) (by decide)).trans r13
  have r10' : ready.getReg .x10 = chainSource state k j := regs.1
  have r12' : ready.getReg .x12 = chainOutput state c k j := regs.2.1
  have sv : rangeValid (ready.getReg .x10) 96 = true := by rw [r10']; exact sourceValid
  have sa : (ready.getReg .x10).toNat % 8 = 0 := by rw [r10']; exact sourceAligned
  have dv : rangeValid (ready.getReg .x12) 32 = true := by rw [r12']; exact destinationValid
  have da : (ready.getReg .x12).toNat % 8 = 0 := by rw [r12']; exact destinationAligned
  have memory : readBuffer ready (ready.getReg .x10).toNat 96 =
      readBuffer state (ready.getReg .x10).toNat 96 := by
    have sameMem : ready.mem = state.mem := chain_setup_memory state c k j
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have input' : oracleInput ready = some (.inl (readBuffer state (ready.getReg .x10).toNat 96)) := by
    simp [oracleInput, r11', r13', sv, sa, dv, da, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, memory]
    try rw [r13']
    try simp [memory]
    try rfl
  have input : oracleInput ready = some (.inl
      (readBuffer state (chainSource state k j).toNat 96)) := by
    rw [input', r10']
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup, execute, fetched, if_pos r5', input]
  simp only [writeOracleAnswer, r12', bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl
      (readBuffer state (chainSource state k j).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, chainCallState, chainSetupState,
    ← Nat.add_assoc]
  congr

/-- Small offsets from an in-range pointer do not wrap. -/
theorem pointer_offset_nat (base offset : Nat) (bound : base + offset ≤ MEMORY_BYTES) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 offset).toNat = base + offset := by
  have b : base < 2 ^ 64 := by dsimp [MEMORY_BYTES] at bound; omega
  have o : offset < 2 ^ 64 := by dsimp [MEMORY_BYTES] at bound; omega
  have t : base + offset < 2 ^ 64 := by dsimp [MEMORY_BYTES] at bound; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b,
    Nat.mod_eq_of_lt o, Nat.mod_eq_of_lt t]

theorem chain_source_nat (s : MachineState) (k j : Nat) (hk : k < 8) (hj : j < 4) (base : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base) (slotBound : base + 2080 ≤ MEMORY_BYTES) :
    (chainSource s k j).toNat = base + 256 * k + 64 * j := by
  unfold chainSource
  rw [slotPointer, pointer_offset_nat base (64 * j + 256 * k) (by omega)]
  omega

theorem chain_output_slot_nat (s : MachineState) (c k j : Nat) (hk : k < 8) (hj : j < 3)
    (base : Nat) (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base)
    (slotBound : base + 2080 ≤ MEMORY_BYTES) :
    chainOutput s c k j = BitVec.ofNat 64 (base + 256 * k + 64 * j + 64) := by
  unfold chainOutput
  rw [if_neg (by omega), slotPointer, ← BitVec.ofNat_add]
  congr 1
  omega

theorem chain_output_heap_nat (s : MachineState) (c k : Nat) (heap : Nat)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) :
    chainOutput s c k 3 = BitVec.ofNat 64 (heap + 384 * c + heapOffset k) := by
  unfold chainOutput
  rw [if_pos rfl, heapPointer, ← BitVec.ofNat_add]
  congr 1
  omega

theorem word_small_toNat (x : Nat) (small : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-- Address and alignment side conditions of in-place call `j` of lane `k` in chunk `c`. -/
theorem chain_call_valid (s : MachineState) (c k j : Nat) (hc : c < 4) (hk : k < 8) (hj : j < 4)
    (base heap : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base) (slotAligned : base % 8 = 0)
    (slotBound : base + 2080 ≤ MEMORY_BYTES)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) (heapAligned : heap % 8 = 0)
    (heapBound : heap + 1536 ≤ MEMORY_BYTES) :
    rangeValid (chainSource s k j) 96 = true ∧
    (chainSource s k j).toNat % 8 = 0 ∧
    rangeValid (chainOutput s c k j) 32 = true ∧ (chainOutput s c k j).toNat % 8 = 0 := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have hkOff : heapOffset k + 32 ≤ 384 := by unfold heapOffset; omega
  have hkAlign : heapOffset k % 8 = 0 := heap_offset_aligned k
  have source := chain_source_nat s k j hk hj base slotPointer slotBound
  have output : (chainOutput s c k j).toNat =
      if j = 3 then heap + 384 * c + heapOffset k else base + 256 * k + 64 * j + 64 := by
    by_cases last : j = 3
    · subst last
      rw [chain_output_heap_nat s c k heap heapPointer, word_small_toNat _ (by omega), if_pos rfl]
    · rw [chain_output_slot_nat s c k j hk (by omega) base slotPointer slotBound,
        word_small_toNat _ (by omega), if_neg last]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, source, decide_eq_true_eq]; omega
  · rw [source]; omega
  · simp only [rangeValid, output, decide_eq_true_eq]; split <;> omega
  · rw [output]; split <;> omega

end CommitGolfCandidate
