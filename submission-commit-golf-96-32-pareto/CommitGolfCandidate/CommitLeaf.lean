import CommitGolfCandidate.Execution
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HeapLayout

/-! Structural code indexing and execution of one 17-instruction lane of the 32-leaf
unrolled commitment loop. Each lane copies its 16-byte salt from `x18 + 16*j` and stores
the unique 8-byte leaf tag `x10` into `[x10, x10+24)`, executes four in-place 96-byte
compression calls (writing `d0` at `x10+56`, `d1` at `x10+120`, `d2` at `x10+184`, and
the leaf digest at `x23 + heapOffset j`), and advances `x10` by 256 bytes total. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Helper: indexing into a flatMap of equal-length chunks. -/
theorem flatMap_fixed_getElem? {α β : Type} (f : α → List β) (k : Nat)
    (hlen : ∀ a, (f a).length = k) (xs : List α) (j m : Nat)
    (hj : j < xs.length) (hm : m < k) :
    (xs.flatMap f)[k * j + m]? = (f (xs[j]'hj))[m]? := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x rest ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [hlen]; omega)]
    | succ j =>
      have hj' : j < rest.length := by simp at hj; omega
      have hmul : k * (j + 1) = k * j + k := by rw [Nat.mul_add, Nat.mul_one]
      rw [List.getElem?_append_right (by rw [hlen, hmul]; omega), hlen]
      have idx : k * (j + 1) + m - k = k * j + m := by rw [hmul]; omega
      rw [idx]
      exact ih j hj'

/-- Structural decomposition of `(commitCode LOG_LENGTH).filter isNotLabel` into its
eight contiguous sections so code lookup never reduces the full assembled image. -/
def commitPreRandomAsm : List Asm :=
  let n := 2 ^ LOG_LENGTH
  [addi 8 10 (-24), mv 26 11, mv 9 12] ++ li 6 (96 * n) ++
  [regop 18 9 6] ++ li 6 (48 * n) ++ [regop 23 9 6] ++
  [addi 5 0 2, mv 10 18] ++ li 11 (16 * n) ++ [regop 20 18 11, insn 0x73] ++
  [mv 10 8, addi 5 0 0, addi 11 0 96, addi 13 0 0]

def commitLeafLoopAsm : List Asm := (List.range 32).flatMap leafChunk

def commitLeafLatchAsm : List Asm :=
  [addi 18 18 512, addi 23 23 1536, .branch 1 18 20 "commit-block"]

def commitParentSetupAsm : List Asm :=
  let n := 2 ^ LOG_LENGTH
  [addi 21 23 (-1536), addi 24 0 1536, addi 24 24 1536] ++
  li 6 (48 * n - 1536) ++ [regop 22 9 6, .branch 0 22 9 "commit-tail"]

def commitParentLoopAsm : List Asm := (List.range 32).flatMap fun j => parentChunk (31 - j)

def commitParentLatchAsm : List Asm :=
  [regop 21 21 24 0 0x20, addi 22 22 (-1536), .branch 1 22 9 "commit-parent"]

def commitParentTailAsm : List Asm := (List.range 31).flatMap fun j => parentChunk (31 - j)

def commitEpilogueAsm : List Asm := copyDigest 9 26 32 ++ halt true

private theorem filter_leafChunk (j : Nat) : (leafChunk j).filter isNotLabel = leafChunk j := rfl
private theorem filter_parentChunk (u : Nat) : (parentChunk u).filter isNotLabel = parentChunk u := rfl

private theorem filter_flatMap_id {α : Type} (f : α → List Asm) (xs : List α)
    (h : ∀ a, (f a).filter isNotLabel = f a) :
    (xs.flatMap f).filter isNotLabel = xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.flatMap_cons, List.filter_append, h x, ih]

theorem commitCode_filtered_eq :
    (commitCode LOG_LENGTH).filter isNotLabel =
      commitPreRandomAsm ++ commitLeafLoopAsm ++ commitLeafLatchAsm ++
      commitParentSetupAsm ++ commitParentLoopAsm ++ commitParentLatchAsm ++
      commitParentTailAsm ++ commitEpilogueAsm := by
  unfold commitCode commitPreRandomAsm commitLeafLoopAsm commitLeafLatchAsm
    commitParentSetupAsm commitParentLoopAsm commitParentLatchAsm
    commitParentTailAsm commitEpilogueAsm
  simp only [List.filter_append, List.filter_cons, isNotLabel, List.filter_nil,
    filter_flatMap_id leafChunk _ filter_leafChunk,
    filter_flatMap_id (fun j => parentChunk (31 - j)) _ (fun j => filter_parentChunk (31 - j)),
    List.append_assoc, List.nil_append]
  rfl

theorem commitPreRandom_len : commitPreRandomAsm.length = 34 := by decide
theorem commitLeafLoop_len : commitLeafLoopAsm.length = 544 := by
  simp [commitLeafLoopAsm, List.length_flatMap, leafChunk]
theorem commitLeafLatch_len : commitLeafLatchAsm.length = 3 := by decide
theorem commitParentSetup_len : commitParentSetupAsm.length = 12 := by decide
theorem commitParentLoop_len : commitParentLoopAsm.length = 96 := by
  simp [commitParentLoopAsm, List.length_flatMap, parentChunk]
theorem commitParentLatch_len : commitParentLatchAsm.length = 3 := by decide
theorem commitParentTail_len : commitParentTailAsm.length = 93 := by
  simp [commitParentTailAsm, List.length_flatMap, parentChunk]
theorem commitEpilogue_len : commitEpilogueAsm.length = 11 := by decide

private def labelStep (state : Nat × List (String × Nat)) (instruction : Asm) :
    Nat × List (String × Nat) :=
  match instruction with
  | .label name => (state.1, (name, state.1) :: state.2)
  | _ => (state.1 + 1, state.2)

private theorem labelStep_foldl_noLabel (code : List Asm) (pos : Nat) (acc : List (String × Nat))
    (h : code.filter isNotLabel = code) :
    code.foldl labelStep (pos, acc) = (pos + code.length, acc) := by
  induction code generalizing pos with
  | nil => simp
  | cons x rest ih =>
    cases x with
    | label _ =>
      have hlen := congrArg List.length h
      simp only [List.filter_cons, isNotLabel, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
      have hle := List.length_filter_le isNotLabel rest
      omega
    | word _ | branch _ _ _ _ | jump _ _ =>
      simp only [List.filter_cons, isNotLabel, ↓reduceIte, List.cons.injEq, true_and] at h
      simp only [List.foldl_cons, labelStep, List.length_cons]
      rw [ih (pos + 1) h]
      congr 1; omega

theorem commit_labelPositions :
    labelPositions (commitCode LOG_LENGTH) =
      [("commit-tail", 692), ("commit-parent", 593), ("commit-block", 34)] := by
  have hcode : commitCode LOG_LENGTH =
      commitPreRandomAsm ++ [.label "commit-block"] ++ commitLeafLoopAsm ++ commitLeafLatchAsm ++
      commitParentSetupAsm ++ [.label "commit-parent"] ++ commitParentLoopAsm ++ commitParentLatchAsm ++
      [.label "commit-tail"] ++ commitParentTailAsm ++ commitEpilogueAsm := by
    unfold commitCode commitPreRandomAsm commitLeafLoopAsm commitLeafLatchAsm
      commitParentSetupAsm commitParentLoopAsm commitParentLatchAsm
      commitParentTailAsm commitEpilogueAsm
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hPre : commitPreRandomAsm.filter isNotLabel = commitPreRandomAsm := rfl
  have hLeaf : commitLeafLoopAsm.filter isNotLabel = commitLeafLoopAsm :=
    filter_flatMap_id leafChunk _ filter_leafChunk
  have hLL : commitLeafLatchAsm.filter isNotLabel = commitLeafLatchAsm := rfl
  have hPS : commitParentSetupAsm.filter isNotLabel = commitParentSetupAsm := rfl
  have hPL : commitParentLoopAsm.filter isNotLabel = commitParentLoopAsm :=
    filter_flatMap_id (fun j => parentChunk (31 - j)) _ (fun j => filter_parentChunk (31 - j))
  have hPLatch : commitParentLatchAsm.filter isNotLabel = commitParentLatchAsm := rfl
  have hPT : commitParentTailAsm.filter isNotLabel = commitParentTailAsm :=
    filter_flatMap_id (fun j => parentChunk (31 - j)) _ (fun j => filter_parentChunk (31 - j))
  have hEpi : commitEpilogueAsm.filter isNotLabel = commitEpilogueAsm := rfl
  change ((commitCode LOG_LENGTH).foldl labelStep (0, [])).2 = _
  rw [hcode]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    labelStep_foldl_noLabel _ _ _ hPre, commitPreRandom_len,
    labelStep_foldl_noLabel _ _ _ hLeaf, commitLeafLoop_len,
    labelStep_foldl_noLabel _ _ _ hLL, commitLeafLatch_len,
    labelStep_foldl_noLabel _ _ _ hPS, commitParentSetup_len,
    labelStep_foldl_noLabel _ _ _ hPL, commitParentLoop_len,
    labelStep_foldl_noLabel _ _ _ hPLatch, commitParentLatch_len,
    labelStep_foldl_noLabel _ _ _ hPT, commitParentTail_len,
    labelStep_foldl_noLabel _ _ _ hEpi, commitEpilogue_len]
  rfl

/-- Extract a single word from `(submission.image .commit).code` when the filtered
assembly list holds `.word w` at `index`. -/
theorem commit_code_word_at (index : Nat) (w : BitVec 32)
    (h : ((commitCode LOG_LENGTH).filter isNotLabel)[index]? = some (.word w)) :
    (submission.image .commit).code[index]? = some w :=
  assemble_word_getElem? (commitCode LOG_LENGTH) index w h

/-- Extract a branch word from `(submission.image .commit).code` using `commit_labelPositions`. -/
theorem commit_code_branch_at (index : Nat) (cond left right : Nat) (target : String) (addr : Nat)
    (h : ((commitCode LOG_LENGTH).filter isNotLabel)[index]? = some (.branch cond left right target))
    (hl : (labelPositions (commitCode LOG_LENGTH)).find? (fun p => p.1 == target) = some (target, addr)) :
    (submission.image .commit).code[index]? =
      some (branchWord cond left right (4 * ((addr : Int) - index))) := by
  change (assemble (commitCode LOG_LENGTH))[index]? = _
  unfold assemble
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  rw [h]
  simp only [Option.map_some, hl, Nat.zero_add]

/-- Standard fetch lemma for the commitment image. -/
theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 796) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .commit).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

/-- Indexing into the pre-random section (indices 0..33). -/
theorem commit_filtered_preRandom (i : Nat) (hi : i < 34) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[i]? = commitPreRandomAsm[i]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by rw [commitPreRandom_len]; exact hi)]

/-- Indexing into the unrolled leaf loop (indices 34..577). -/
theorem commit_filtered_leaf (j m : Nat) (hj : j < 32) (hm : m < 17) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[34 + 17 * j + m]? = (leafChunk j)[m]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len]
  rw [show 34 + 17 * j + m - 34 = 17 * j + m by omega]
  rw [List.getElem?_append_left (by rw [commitLeafLoop_len]; omega)]
  unfold commitLeafLoopAsm
  have h := flatMap_fixed_getElem? leafChunk 17 (fun _ => rfl) (List.range 32) j m
    (by simp; exact hj) hm
  simpa only [List.getElem_range] using h

/-- Indexing into the leaf latch (indices 578..580). -/
theorem commit_filtered_leafLatch (i : Nat) (hi : i < 3) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[578 + i]? = commitLeafLatchAsm[i]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 578 + i - 34 = 544 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 544 + i - 544 = i by omega,
    List.getElem?_append_left (by rw [commitLeafLatch_len]; exact hi)]

/-- Indexing into parent setup (indices 581..592). -/
theorem commit_filtered_parentSetup (i : Nat) (hi : i < 12) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[581 + i]? = commitParentSetupAsm[i]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 581 + i - 34 = 547 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 547 + i - 544 = 3 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLatch_len]; omega), commitLeafLatch_len,
    show 3 + i - 3 = i by omega,
    List.getElem?_append_left (by rw [commitParentSetup_len]; exact hi)]

/-- Indexing into the unrolled parent loop (indices 593..688). -/
theorem commit_filtered_parentLoop (j m : Nat) (hj : j < 32) (hm : m < 3) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[593 + 3 * j + m]? = (parentChunk (31 - j))[m]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 593 + 3 * j + m - 34 = 559 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 559 + 3 * j + m - 544 = 15 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitLeafLatch_len]; omega), commitLeafLatch_len,
    show 15 + 3 * j + m - 3 = 12 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitParentSetup_len]; omega), commitParentSetup_len,
    show 12 + 3 * j + m - 12 = 3 * j + m by omega,
    List.getElem?_append_left (by rw [commitParentLoop_len]; omega)]
  unfold commitParentLoopAsm
  have h := flatMap_fixed_getElem? (fun k => parentChunk (31 - k)) 3 (fun _ => rfl)
    (List.range 32) j m (by simp; exact hj) hm
  simpa only [List.getElem_range] using h

/-- Indexing into the parent latch (indices 689..691). -/
theorem commit_filtered_parentLatch (i : Nat) (hi : i < 3) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[689 + i]? = commitParentLatchAsm[i]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 689 + i - 34 = 655 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 655 + i - 544 = 111 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLatch_len]; omega), commitLeafLatch_len,
    show 111 + i - 3 = 108 + i by omega,
    List.getElem?_append_right (by rw [commitParentSetup_len]; omega), commitParentSetup_len,
    show 108 + i - 12 = 96 + i by omega,
    List.getElem?_append_right (by rw [commitParentLoop_len]; omega), commitParentLoop_len,
    show 96 + i - 96 = i by omega,
    List.getElem?_append_left (by rw [commitParentLatch_len]; exact hi)]

/-- Indexing into the 31-parent tail (indices 692..784). -/
theorem commit_filtered_parentTail (j m : Nat) (hj : j < 31) (hm : m < 3) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[692 + 3 * j + m]? = (parentChunk (31 - j))[m]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 692 + 3 * j + m - 34 = 658 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 658 + 3 * j + m - 544 = 114 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitLeafLatch_len]; omega), commitLeafLatch_len,
    show 114 + 3 * j + m - 3 = 111 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitParentSetup_len]; omega), commitParentSetup_len,
    show 111 + 3 * j + m - 12 = 99 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitParentLoop_len]; omega), commitParentLoop_len,
    show 99 + 3 * j + m - 96 = 3 + 3 * j + m by omega,
    List.getElem?_append_right (by rw [commitParentLatch_len]; omega), commitParentLatch_len,
    show 3 + 3 * j + m - 3 = 3 * j + m by omega,
    List.getElem?_append_left (by rw [commitParentTail_len]; omega)]
  unfold commitParentTailAsm
  have h := flatMap_fixed_getElem? (fun k => parentChunk (31 - k)) 3 (fun _ => rfl)
    (List.range 31) j m (by simp; exact hj) hm
  simpa only [List.getElem_range] using h

/-- Indexing into root copy and halt (indices 785..795). -/
theorem commit_filtered_epilogue (i : Nat) (hi : i < 11) :
    ((commitCode LOG_LENGTH).filter isNotLabel)[785 + i]? = commitEpilogueAsm[i]? := by
  rw [commitCode_filtered_eq]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [commitPreRandom_len]; omega), commitPreRandom_len,
    show 785 + i - 34 = 751 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLoop_len]; omega), commitLeafLoop_len,
    show 751 + i - 544 = 207 + i by omega,
    List.getElem?_append_right (by rw [commitLeafLatch_len]; omega), commitLeafLatch_len,
    show 207 + i - 3 = 204 + i by omega,
    List.getElem?_append_right (by rw [commitParentSetup_len]; omega), commitParentSetup_len,
    show 204 + i - 12 = 192 + i by omega,
    List.getElem?_append_right (by rw [commitParentLoop_len]; omega), commitParentLoop_len,
    show 192 + i - 96 = 96 + i by omega,
    List.getElem?_append_right (by rw [commitParentLatch_len]; omega), commitParentLatch_len,
    show 96 + i - 3 = 93 + i by omega,
    List.getElem?_append_right (by rw [commitParentTail_len]; omega), commitParentTail_len,
    show 93 + i - 93 = i by omega]

/-! ### Exact 32-lane decode and sign-extension helpers -/

theorem signExtend12_salt0 (j : Fin 32) :
    signExtend12 (BitVec.ofNat 12 (16 * j.val)) = BitVec.ofNat 64 (16 * j.val) := by
  fin_cases j <;> rfl

theorem signExtend12_salt1 (j : Fin 32) :
    signExtend12 (BitVec.ofNat 12 (16 * j.val + 8)) = BitVec.ofNat 64 (16 * j.val + 8) := by
  fin_cases j <;> rfl

theorem signExtend12_heapOffset (j : Fin 32) :
    signExtend12 (BitVec.ofNat 12 (heapOffset j.val)) = BitVec.ofNat 64 (heapOffset j.val) := by
  fin_cases j <;> rfl

private theorem decode_ld_salt0 (j : Nat) (hj : j < 32) :
    decodeInstruction (BitVec.ofNat 32 (16 * j * 2^20 + 18 * 2^15 + 3 * 2^12 + 6 * 2^7 + 3)) =
      some (.base (.LD .x6 .x18 (BitVec.ofNat 12 (16 * j)))) := by
  interval_cases j <;> rfl

private theorem decode_ld_salt1 (j : Nat) (hj : j < 32) :
    decodeInstruction (BitVec.ofNat 32 ((16 * j + 8) * 2^20 + 18 * 2^15 + 3 * 2^12 + 6 * 2^7 + 3)) =
      some (.base (.LD .x6 .x18 (BitVec.ofNat 12 (16 * j + 8)))) := by
  interval_cases j <;> rfl

private theorem decode_addi_heap (j : Nat) (hj : j < 32) :
    decodeInstruction (BitVec.ofNat 32 (imm (heapOffset j) 12 * 2^20 + 23 * 2^15 + 12 * 2^7 + 0x13)) =
      some (.base (.ADDI .x12 .x23 (BitVec.ofNat 12 (heapOffset j)))) := by
  interval_cases j <;> rfl

/-- Decoded 17 instructions of leaf lane `j < 32`. -/
def leafLaneInstr (j : Nat) : Nat → Instr
  | 0  => .LD .x6 .x18 (BitVec.ofNat 12 (16 * j))
  | 1  => .SD .x10 .x6 0
  | 2  => .LD .x6 .x18 (BitVec.ofNat 12 (16 * j + 8))
  | 3  => .SD .x10 .x6 8
  | 4  => .SD .x10 .x10 16
  | 5  => .ADDI .x12 .x10 56
  | 6  => .ECALL
  | 7  => .ADDI .x10 .x10 56
  | 8  => .ADDI .x12 .x10 64
  | 9  => .ECALL
  | 10 => .ADDI .x10 .x10 64
  | 11 => .ADDI .x12 .x10 64
  | 12 => .ECALL
  | 13 => .ADDI .x10 .x10 64
  | 14 => .ADDI .x12 .x23 (BitVec.ofNat 12 (heapOffset j))
  | 15 => .ECALL
  | _  => .ADDI .x10 .x10 72

private theorem decode_sd_slot0 :
    decodeInstruction (BitVec.ofNat 32 (0 / 32 * 2^25 + 6 * 2^20 + 10 * 2^15 + 3 * 2^12 + (0 % 32) * 2^7 + 0x23)) =
      some (.base (.SD .x10 .x6 0)) := rfl

private theorem decode_sd_slot8 :
    decodeInstruction (BitVec.ofNat 32 (8 / 32 * 2^25 + 6 * 2^20 + 10 * 2^15 + 3 * 2^12 + (8 % 32) * 2^7 + 0x23)) =
      some (.base (.SD .x10 .x6 8)) := rfl

private theorem decode_sd_tag16 :
    decodeInstruction (BitVec.ofNat 32 (16 / 32 * 2^25 + 10 * 2^20 + 10 * 2^15 + 3 * 2^12 + (16 % 32) * 2^7 + 0x23)) =
      some (.base (.SD .x10 .x10 16)) := rfl

private theorem decode_addi_12_10_56 :
    decodeInstruction (BitVec.ofNat 32 (imm 56 12 * 2^20 + 10 * 2^15 + 12 * 2^7 + 0x13)) =
      some (.base (.ADDI .x12 .x10 56)) := rfl

theorem decode_ecall_word :
    decodeInstruction (BitVec.ofNat 32 0x73) = some (.base .ECALL) := rfl

private theorem decode_addi_10_10_56 :
    decodeInstruction (BitVec.ofNat 32 (imm 56 12 * 2^20 + 10 * 2^15 + 10 * 2^7 + 0x13)) =
      some (.base (.ADDI .x10 .x10 56)) := rfl

private theorem decode_addi_12_10_64 :
    decodeInstruction (BitVec.ofNat 32 (imm 64 12 * 2^20 + 10 * 2^15 + 12 * 2^7 + 0x13)) =
      some (.base (.ADDI .x12 .x10 64)) := rfl

private theorem decode_addi_10_10_64 :
    decodeInstruction (BitVec.ofNat 32 (imm 64 12 * 2^20 + 10 * 2^15 + 10 * 2^7 + 0x13)) =
      some (.base (.ADDI .x10 .x10 64)) := rfl

private theorem decode_addi_10_10_72 :
    decodeInstruction (BitVec.ofNat 32 (imm 72 12 * 2^20 + 10 * 2^15 + 10 * 2^7 + 0x13)) =
      some (.base (.ADDI .x10 .x10 72)) := rfl

theorem commit_leaf_decode (j m : Nat) (hj : j < 32) (hm : m < 17) :
    ((submission.image .commit).code[34 + 17 * j + m]?).bind decodeInstruction =
      some (.base (leafLaneInstr j m)) := by
  have hfilt := commit_filtered_leaf j m hj hm
  interval_cases m
  · simp only [leafChunk, ld, insn, List.getElem?_cons_zero] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ld_salt0 j hj]; rfl
  · simp only [leafChunk, sd, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_sd_slot0]; rfl
  · simp only [leafChunk, ld, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ld_salt1 j hj]; rfl
  · simp only [leafChunk, sd, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_sd_slot8]; rfl
  · simp only [leafChunk, sd, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_sd_tag16]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_12_10_56]; rfl
  · simp only [leafChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_10_10_56]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_12_10_64]; rfl
  · simp only [leafChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_10_10_64]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_12_10_64]; rfl
  · simp only [leafChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_10_10_64]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_heap j hj]; rfl
  · simp only [leafChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl
  · simp only [leafChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
    rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_addi_10_10_72]; rfl

/-! ### Pointer arithmetic helpers -/

/-- Direct 96-byte compression oracle input when registers and alignments match. -/
theorem oracleInput_compression (state : MachineState)
    (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sv : rangeValid (state.getReg .x10) 96 = true)
    (sa : (state.getReg .x10).toNat % 8 = 0)
    (dv : rangeValid (state.getReg .x12) 32 = true)
    (da : (state.getReg .x12).toNat % 8 = 0) :
    oracleInput state = some (.inl (readBuffer state (state.getReg .x10).toNat 96)) := by
  unfold oracleInput
  dsimp only
  rw [r11, r13]
  simp [sv, sa, dv, da, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH]

/-- Add a known `Nat` constant literal to `BitVec.ofNat 64 a` without `BitVec.toNat` leakage. -/
theorem ofNat64_add_eq (a k b : Nat) (h : a + k = b) :
    BitVec.ofNat 64 a + (OfNat.ofNat k : Word) = BitVec.ofNat 64 b := by
  change BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 b
  rw [← BitVec.ofNat_add, h]

/-- Rewrite `BitVec.ofNat 64 a + b` (for a `BitVec 64` numeral `b`) into `BitVec.ofNat 64 (a + b)`. -/
theorem bitvec64_ofNat_add_lit (a b : Nat) :
    BitVec.ofNat 64 a + (OfNat.ofNat b : Word) = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- Rewrite `a + BitVec.ofNat 64 b` (for a `BitVec 64` numeral `a`) into `BitVec.ofNat 64 (a + b)`. -/
theorem bitvec64_lit_add_ofNat (a b : Nat) :
    (OfNat.ofNat a : Word) + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- `writeBits` advances the PC by 4 without unfolding the byte-write fold. -/
theorem writeBits_pc {bits : Nat} (state : MachineState) (address : Word) (answer : BitVec bits) :
    (writeBits state address answer).pc = state.pc + 4 := rfl

/-- Combine nested `Execution.charge` wrappers so constant cycle/query totals reduce directly. -/
theorem charge_charge (e : Execution) (c1 q1 c2 q2 : Nat) :
    (e.charge c1 q1).charge c2 q2 = e.charge (c2 + c1) (q2 + q1) := by
  cases e; simp [Execution.charge, Nat.add_assoc]

/-- Small offsets from an in-range pointer do not wrap. -/
theorem pointer_offset_nat (base offset : Nat) (bound : base + offset ≤ MEMORY_BYTES) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 offset).toNat = base + offset := by
  have b : base < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  have o : offset < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  have t : base + offset < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b,
    Nat.mod_eq_of_lt o, Nat.mod_eq_of_lt t]

theorem word_small_toNat (x : Nat) (small : x < 2^64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-! ### One 17-instruction leaf lane: state transitions and execution -/

/-- First 6 instructions of lane `j`: copy 16-byte salt from `x18 + 16*j` to `x10`,
write tag `x10` to `x10 + 16`, and set `x12 := x10 + 56`. -/
def leafPrepInstrs (j : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (16 * j)),
   .SD .x10 .x6 0,
   .LD .x6 .x18 (BitVec.ofNat 12 (16 * j + 8)),
   .SD .x10 .x6 8,
   .SD .x10 .x10 16,
   .ADDI .x12 .x10 56]

def leafPrepPrefix (state : MachineState) (j count : Nat) : MachineState :=
  ((leafPrepInstrs j).take count).foldl execInstrBr state

def leafPrepState (state : MachineState) (j : Nat) : MachineState := leafPrepPrefix state j 6

private theorem mem_getReg (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

theorem leaf_prep_prefix_reg (state : MachineState) (j count : Nat) (hc : count ≤ 6)
    (reg : Reg) (n6 : reg ≠ .x6) (n12 : reg ≠ .x12) :
    (leafPrepPrefix state j count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, mem_getReg,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem leaf_prep_pc (state : MachineState) (j : Nat) :
    (leafPrepState state j).pc = state.pc + 24 := by
  simp [leafPrepState, leafPrepPrefix, leafPrepInstrs, execInstrBr, MachineState.setPC,
    BitVec.add_assoc]

theorem leaf_prep_x12 (state : MachineState) (j : Nat) :
    (leafPrepState state j).getReg .x12 = state.getReg .x10 + 56 := by
  simp [leafPrepState, leafPrepPrefix, leafPrepInstrs, execInstrBr, signExtend12,
    MachineState.getReg_setPC, mem_getReg, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

/-- Exact state after Call 0 (reply written at `x10 + 56`). -/
def leafCall0State (state : MachineState) (j : Nat) (a0 : BitVec 256) : MachineState :=
  writeBits (leafPrepState state j) (state.getReg .x10 + 56) a0

/-- Exact state after Call 1 (`x10 += 56`, `x12 := x10 + 64`, reply at `x10 + 120`). -/
def leafCall1Setup (state : MachineState) : MachineState :=
  ((state.setReg .x10 (state.getReg .x10 + 56)).setReg .x12 (state.getReg .x10 + 120)).setPC (state.pc + 8)

def leafCall1State (state : MachineState) (a1 : BitVec 256) : MachineState :=
  writeBits (leafCall1Setup state) (state.getReg .x10 + 120) a1

/-- Exact state after Call 2 (`x10 += 64`, `x12 := x10 + 64`, reply at `x10 + 128` relative to s1). -/
def leafCall2Setup (state : MachineState) : MachineState :=
  ((state.setReg .x10 (state.getReg .x10 + 64)).setReg .x12 (state.getReg .x10 + 128)).setPC (state.pc + 8)

def leafCall2State (state : MachineState) (a2 : BitVec 256) : MachineState :=
  writeBits (leafCall2Setup state) (state.getReg .x10 + 128) a2

/-- Exact state after Call 3 (`x10 += 64`, `x12 := x23 + heapOffset j`, reply at `x23 + heapOffset j`). -/
def leafCall3Setup (state : MachineState) (j : Nat) : MachineState :=
  ((state.setReg .x10 (state.getReg .x10 + 64)).setReg .x12
    (state.getReg .x23 + BitVec.ofNat 64 (heapOffset j))).setPC (state.pc + 8)

def leafCall3State (state : MachineState) (j : Nat) (a3 : BitVec 256) : MachineState :=
  writeBits (leafCall3Setup state j) (state.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) a3

/-- Final instruction of lane `j`: `addi x10, x10, 72`. -/
def leafAdvanceState (state : MachineState) : MachineState :=
  (state.setReg .x10 (state.getReg .x10 + 72)).setPC (state.pc + 4)

/-- Complete 4-query monadic run of lane `j`. -/
def leafLaneRun (state : MachineState) (j : Nat) : OracleComp World MachineState := do
  let p0 := leafPrepState state j
  let a0 ← World.query (.inr (.inl (readBuffer p0 (state.getReg .x10).toNat 96)))
  let s1 := leafCall0State state j a0
  let a1 ← World.query (.inr (.inl (readBuffer s1 (state.getReg .x10 + 56).toNat 96)))
  let s2 := leafCall1State s1 a1
  let a2 ← World.query (.inr (.inl (readBuffer s2 (s1.getReg .x10 + 120).toNat 96)))
  let s3 := leafCall2State s2 a2
  let a3 ← World.query (.inr (.inl (readBuffer s3 (s2.getReg .x10 + 128).toNat 96)))
  return leafAdvanceState (leafCall3State s3 j a3)

/-- Helper: execute the 6-instruction prep prefix of lane `j`. -/
private theorem exec_leaf_prep (state : MachineState) (j : Nat) (hj : j < 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j)))
    (salt0Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j)) 8 = true)
    (salt1Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j + 8)) 8 = true)
    (slotValid : ∀ w : Fin 3, accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * w.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (leafPrepState state j) true
          return result.charge 6 0) := by
  apply execute_unit_steps (states := leafPrepPrefix state j)
  intro i hi
  refine ⟨.base ((leafPrepInstrs j)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (34 + 17 * j + i) _ (by omega)
    · interval_cases i
      · exact pc
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc]
        apply ofNat64_add_eq _ 4 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (8 : Word) = _
        apply ofNat64_add_eq _ 8 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (12 : Word) = _
        apply ofNat64_add_eq _ 12 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (16 : Word) = _
        apply ofNat64_add_eq _ 16 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (20 : Word) = _
        apply ofNat64_add_eq _ 20 _; omega
    · have hd := commit_leaf_decode j i hj (by omega)
      interval_cases i <;> exact hd
  · have r18 := leaf_prep_prefix_reg state j i (by omega) .x18 (by decide) (by decide)
    have r10 := leaf_prep_prefix_reg state j i (by omega) .x10 (by decide) (by decide)
    have s0 := signExtend12_salt0 ⟨j, hj⟩
    have s1 := signExtend12_salt1 ⟨j, hj⟩
    have w0 := slotValid ⟨0, by decide⟩
    have w1 := slotValid ⟨1, by decide⟩
    have w2 := slotValid ⟨2, by decide⟩
    have valid : memoryArgumentsValid (leafPrepPrefix state j i)
        ((leafPrepInstrs j)[i]?.getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [leafPrepInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, r18, r10]
      · rw [s0]; exact salt0Valid
      · simpa [signExtend12] using w0
      · rw [s1]; exact salt1Valid
      · simpa [signExtend12] using w1
      · simpa [signExtend12] using w2
    interval_cases i <;>
      simp only [leafPrepInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Helper: execute a 3-instruction compression step (`addi x10, x10, dx`,
`addi x12, src, dy`, `ecall`) at `34 + 17 * j + m`. -/
private theorem exec_two_addi_ecall (state : MachineState) (j m : Nat) (hj : j < 32)
    (hm : m = 7 ∨ m = 10 ∨ m = 13)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + m)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (dx : Nat) (hdx : dx = if m = 7 then 56 else 64)
    (outAddr : Word)
    (hout : outAddr = if m = 13 then state.getReg .x23 + BitVec.ofNat 64 (heapOffset j)
                      else state.getReg .x10 + BitVec.ofNat 64 (dx + 64))
    (sv : rangeValid (state.getReg .x10 + BitVec.ofNat 64 dx) 96 = true)
    (sa : (state.getReg .x10 + BitVec.ofNat 64 dx).toNat % 8 = 0)
    (dv : rangeValid outAddr 32 = true)
    (da : outAddr.toNat % 8 = 0)
    (fuel : Nat) :
    let nextX10 := state.getReg .x10 + BitVec.ofNat 64 dx
    let ready := ((state.setReg .x10 nextX10).setReg .x12 outAddr).setPC (state.pc + 8)
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (.inl (readBuffer state nextX10.toNat 96)))
          let result ← execute (submission.image .commit) fuel (writeBits ready outAddr answer) true
          return result.charge 10 1) := by
  dsimp only
  let nextX10 := state.getReg .x10 + BitVec.ofNat 64 dx
  let mid := (state.setReg .x10 nextX10).setPC (state.pc + 4)
  let ready := ((state.setReg .x10 nextX10).setReg .x12 outAddr).setPC (state.pc + 8)
  have hpc1 : mid.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + (m + 1))) := by
    change state.pc + 4 = _
    rw [pc]
    apply ofNat64_add_eq _ 4 _; omega
  have hpc2 : ready.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + (m + 2))) := by
    change state.pc + 8 = _
    rw [pc]
    apply ofNat64_add_eq _ 8 _; omega
  have f0 : fetch (submission.image .commit) state = some (.base (leafLaneInstr j m)) :=
    commit_fetch state (34 + 17 * j + m) _ (by rcases hm with rfl | rfl | rfl <;> omega) pc
      (commit_leaf_decode j m hj (by rcases hm with rfl | rfl | rfl <;> omega))
  have f1 : fetch (submission.image .commit) mid = some (.base (leafLaneInstr j (m + 1))) :=
    commit_fetch mid (34 + 17 * j + (m + 1)) _ (by rcases hm with rfl | rfl | rfl <;> omega) hpc1
      (commit_leaf_decode j (m + 1) hj (by rcases hm with rfl | rfl | rfl <;> omega))
  have f2 : fetch (submission.image .commit) ready = some (.base .ECALL) :=
    commit_fetch ready (34 + 17 * j + (m + 2)) .ECALL (by rcases hm with rfl | rfl | rfl <;> omega) hpc2
      (by rcases hm with rfl | rfl | rfl <;> exact commit_leaf_decode j _ hj (by omega))
  have s0 : ordinaryStep state (.base (leafLaneInstr j m)) = some mid := by
    rcases hm with rfl | rfl | rfl <;> subst hdx <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, nextX10]
  have h44 : (4 : Word) + 4 = 8 := by decide
  have s1 : ordinaryStep mid (.base (leafLaneInstr j (m + 1))) = some ready := by
    rcases hm with rfl | rfl | rfl
    · subst hdx; subst hout
      have h56 : BitVec.ofNat 64 56 + (64 : Word) = BitVec.ofNat 64 (56 + 64) := by decide
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, h44, h56]
    · subst hdx; subst hout
      have h64 : BitVec.ofNat 64 64 + (64 : Word) = BitVec.ofNat 64 (64 + 64) := by decide
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, h44, h64]
    · subst hdx; subst hout
      have sheap := signExtend12_heapOffset ⟨j, hj⟩
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, sheap, h44]
  have rr5 : ready.getReg .x5 = 0 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r5]
  have rr11 : ready.getReg .x11 = 96 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r11]
  have rr13 : ready.getReg .x13 = 0 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r13]
  have rr10 : ready.getReg .x10 = nextX10 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]
  have rr12 : ready.getReg .x12 = outAddr := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
  have sameMem : ready.mem = state.mem := rfl
  have rmem : readBuffer ready nextX10.toNat 96 = readBuffer state nextX10.toNat 96 := by
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have hinput : oracleInput ready = some (.inl (readBuffer state nextX10.toNat 96)) := by
    have h := oracleInput_compression ready rr11 rr13
      (by rw [rr10]; exact sv) (by rw [rr10]; exact sa)
      (by rw [rr12]; exact dv) (by rw [rr12]; exact da)
    rwa [rr10, rmem] at h
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,
    execute_ordinary_step _ _ _ _ _ _ f1 s1,
    execute, f2, if_pos rr5, hinput]
  simp only [writeOracleAnswer, rr12, bind_assoc, pure_bind]
  have c0 : instructionCycles (.base (leafLaneInstr j m)) = 1 := by
    rcases hm with rfl | rfl | rfl <;> rfl
  have c1 : instructionCycles (.base (leafLaneInstr j (m + 1))) = 1 := by
    rcases hm with rfl | rfl | rfl <;> rfl
  rw [c0, c1]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer state nextX10.toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, charge_charge]
  rfl

/-- Register and PC facts preserved across one 17-instruction lane `j`. -/
theorem leaf_lane_support (state finished : MachineState) (j : Nat)
    (reachable : finished ∈ support (leafLaneRun state j)) :
    ∃ a0 a1 a2 a3,
      let s1 := leafCall0State state j a0
      let s2 := leafCall1State s1 a1
      let s3 := leafCall2State s2 a2
      finished = leafAdvanceState (leafCall3State s3 j a3) := by
  simp only [leafLaneRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨a0, _, a1, _, a2, _, a3, _, rfl⟩ := reachable
  exact ⟨a0, a1, a2, a3, rfl⟩

theorem leaf_lane_registers (state finished : MachineState) (j : Nat)
    (reachable : finished ∈ support (leafLaneRun state j)) :
    finished.getReg .x10 = state.getReg .x10 + 256 ∧
    finished.pc = state.pc + 68 ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → finished.getReg reg = state.getReg reg := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := leaf_lane_support state finished j reachable
  have p0x10 : (leafPrepState state j).getReg .x10 = state.getReg .x10 :=
    leaf_prep_prefix_reg state j 6 (by decide) .x10 (by decide) (by decide)
  have s1x10 : (leafCall0State state j a0).getReg .x10 = state.getReg .x10 := by
    rw [leafCall0State, writeBits_register, p0x10]
  have s2x10 : (leafCall1State (leafCall0State state j a0) a1).getReg .x10 =
      state.getReg .x10 + 56 := by
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide),
      s1x10]
  have s3x10 : (leafCall2State (leafCall1State (leafCall0State state j a0) a1) a2).getReg .x10 =
      state.getReg .x10 + 120 := by
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide),
      s2x10, BitVec.add_assoc]; rfl
  have s4x10 : (leafCall3State (leafCall2State (leafCall1State (leafCall0State state j a0) a1) a2) j a3).getReg .x10 =
      state.getReg .x10 + 184 := by
    rw [leafCall3State, writeBits_register, leafCall3Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide),
      s3x10, BitVec.add_assoc]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [leafAdvanceState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide),
      s4x10, BitVec.add_assoc]; rfl
  · simp only [leafAdvanceState, leafCall3State, leafCall3Setup, leafCall2State, leafCall2Setup,
      leafCall1State, leafCall1Setup, leafCall0State, writeBits_pc, MachineState.setPC, leaf_prep_pc,
      BitVec.add_assoc]
    rfl
  · intro reg n6 n10 n12
    rw [leafAdvanceState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      leafCall3State, writeBits_register, leafCall3Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      leafCall0State, writeBits_register]
    exact leaf_prep_prefix_reg state j 6 (by decide) reg n6 n12

set_option maxHeartbeats 1600000 in
/-- Execute one complete 17-instruction lane `j < 32` of the unrolled leaf block:
17 instructions, 45 cycles, 4 compression queries. -/
theorem commit_leaf_lane (state : MachineState) (j : Nat) (hj : j < 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 280 ≤ MEMORY_BYTES)
    (salt0Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j)) 8 = true)
    (salt1Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j + 8)) 8 = true)
    (heap : Nat) (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (17 + fuel) state true =
      (do let finished ← leafLaneRun state j
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 45 4) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have hOff : heapOffset j + 32 ≤ 1536 := by
    have := heap_offset_bound j 16 (by omega); omega
  have hOffAl : heapOffset j % 8 = 0 := heap_offset_aligned j
  have slotAccess : ∀ w : Fin 3, accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * w.val)) 8 = true := by
    intro w
    have hw := w.isLt
    simp only [accessValid, rangeValid, slotPtr, pointer_offset_nat slot (8 * w.val) (by omega),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  -- Helper for aligned offsets from slot
  have slotOffNat (off : Nat) (hb : off ≤ 280) :
      (state.getReg .x10 + BitVec.ofNat 64 off).toNat = slot + off := by
    rw [slotPtr]; exact pointer_offset_nat slot off (by omega)
  have heapOffNat : (state.getReg .x23 + BitVec.ofNat 64 (heapOffset j)).toNat = heap + heapOffset j := by
    rw [heapPtr]; exact pointer_offset_nat heap (heapOffset j) (by omega)
  -- Execute prep (6 instructions)
  rw [show 17 + fuel = 6 + (1 + (3 + (3 + (3 + (1 + fuel))))) by omega,
    exec_leaf_prep state j hj pc salt0Valid salt1Valid slotAccess]
  simp only [leafLaneRun, bind_assoc, pure_bind]
  -- Call 0 ECALL at index 34 + 17*j + 6
  let p0 := leafPrepState state j
  have p0pc : p0.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 6)) := by
    dsimp only [p0]; rw [leaf_prep_pc, pc]
    apply ofNat64_add_eq _ 24 _; omega
  have p0r5 : p0.getReg .x5 = 0 := (leaf_prep_prefix_reg state j 6 (by decide) .x5 (by decide) (by decide)).trans r5
  have p0r11 : p0.getReg .x11 = 96 := (leaf_prep_prefix_reg state j 6 (by decide) .x11 (by decide) (by decide)).trans r11
  have p0r13 : p0.getReg .x13 = 0 := (leaf_prep_prefix_reg state j 6 (by decide) .x13 (by decide) (by decide)).trans r13
  have p0r10 : p0.getReg .x10 = state.getReg .x10 := leaf_prep_prefix_reg state j 6 (by decide) .x10 (by decide) (by decide)
  have p0r12 : (leafPrepState state j).getReg .x12 = state.getReg .x10 + 56 := leaf_prep_x12 state j
  have p0r23 : p0.getReg .x23 = state.getReg .x23 := leaf_prep_prefix_reg state j 6 (by decide) .x23 (by decide) (by decide)
  have f0 : fetch (submission.image .commit) p0 = some (.base .ECALL) :=
    commit_fetch p0 (34 + 17 * j + 6) .ECALL (by omega) p0pc (commit_leaf_decode j 6 hj (by decide))
  have s0nat : (state.getReg .x10).toNat = slot := by rw [slotPtr]; exact word_small_toNat slot (by omega)
  have d0nat : (state.getReg .x10 + 56).toNat = slot + 56 := slotOffNat 56 (by omega)
  have inp0 : oracleInput p0 = some (.inl (readBuffer p0 (state.getReg .x10).toNat 96)) := by
    have sv0 : rangeValid (p0.getReg .x10) 96 = true := by
      simp only [rangeValid, p0r10, s0nat, decide_eq_true_eq]; omega
    have sa0 : (p0.getReg .x10).toNat % 8 = 0 := by rw [p0r10, s0nat]; omega
    have dv0 : rangeValid (p0.getReg .x12) 32 = true := by
      dsimp only [p0]; simp only [rangeValid, p0r12, d0nat, decide_eq_true_eq]; omega
    have da0 : (p0.getReg .x12).toNat % 8 = 0 := by dsimp only [p0]; rw [p0r12, d0nat]; omega
    have h := oracleInput_compression p0 p0r11 p0r13 sv0 sa0 dv0 da0
    rwa [p0r10] at h
  rw [show 1 + (3 + (3 + (3 + (1 + fuel)))) = (3 + (3 + (3 + (1 + fuel)))) + 1 by omega,
    execute, f0, if_pos p0r5, inp0]
  simp only [writeOracleAnswer, p0r12, bind_assoc, pure_bind]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer p0 (state.getReg .x10).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a0
  change BitVec 256 at a0
  let s1 := leafCall0State state j a0
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 7)) := by
    dsimp only [s1]; rw [leafCall0State, writeBits_pc, p0pc]
    apply ofNat64_add_eq _ 4 _; omega
  have s1r5 : s1.getReg .x5 = 0 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r5
  have s1r11 : s1.getReg .x11 = 96 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r11
  have s1r13 : s1.getReg .x13 = 0 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r13
  have s1r10 : s1.getReg .x10 = state.getReg .x10 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r10
  have s1r23 : s1.getReg .x23 = state.getReg .x23 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r23
  -- Call 1 (3 instructions at +7..+9)
  have s1_56 : (s1.getReg .x10 + BitVec.ofNat 64 56).toNat = slot + 56 := by rw [s1r10]; exact d0nat
  have s1_120 : (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)).toNat = slot + 120 := by
    rw [s1r10]; exact slotOffNat 120 (by omega)
  have c1 := exec_two_addi_ecall s1 j 7 hj (Or.inl rfl) s1pc s1r5 s1r11 s1r13 56 rfl
    (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)) rfl
    (by simp only [rangeValid, s1_56, decide_eq_true_eq]; omega) (by rw [s1_56]; omega)
    (by simp only [rangeValid, s1_120, decide_eq_true_eq]; omega) (by rw [s1_120]; omega)
    (3 + (3 + (1 + fuel)))
  have hs1 : @writeBits COMPRESSION_OUTPUT_LENGTH (leafPrepState state j) (state.getReg .x10 + 56) a0 = s1 := rfl
  rw [hs1, c1]
  simp only [bind_assoc, pure_bind]
  rw [show (s1.getReg .x10 + BitVec.ofNat 64 56).toNat = (state.getReg .x10 + 56).toNat by rw [s1r10]; rfl]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s1 (state.getReg .x10 + 56).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a1
  change BitVec 256 at a1
  let s2 := leafCall1State s1 a1
  have s2eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s1.setReg .x10 (s1.getReg .x10 + BitVec.ofNat 64 56)).setReg .x12
      (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64))).setPC (s1.pc + 8))
      (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)) a1 = s2 := rfl
  rw [s2eq]
  have s2pc : s2.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 10)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s1.pc + 8 + 4 = _
    rw [s1pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  have s2r5 : s2.getReg .x5 = 0 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r5
  have s2r11 : s2.getReg .x11 = 96 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r11
  have s2r13 : s2.getReg .x13 = 0 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r13
  have s2r10 : s2.getReg .x10 = s1.getReg .x10 + 56 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]
  have s2r23 : s2.getReg .x23 = state.getReg .x23 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r23
  -- Call 2 (3 instructions at +10..+12)
  have s2_64_eq : s2.getReg .x10 + BitVec.ofNat 64 64 = s1.getReg .x10 + 120 := by
    rw [s2r10, BitVec.add_assoc]; rfl
  have s2_64 : (s2.getReg .x10 + BitVec.ofNat 64 64).toNat = slot + 120 := by
    rw [s2_64_eq, s1r10]; exact slotOffNat 120 (by omega)
  have s2_128 : (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)).toNat = slot + 184 := by
    rw [s2r10, s1r10, BitVec.add_assoc]
    exact slotOffNat 184 (by omega)
  have c2 := exec_two_addi_ecall s2 j 10 hj (Or.inr (Or.inl rfl)) s2pc s2r5 s2r11 s2r13 64 rfl
    (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)) rfl
    (by simp only [rangeValid, s2_64, decide_eq_true_eq]; omega) (by rw [s2_64]; omega)
    (by simp only [rangeValid, s2_128, decide_eq_true_eq]; omega) (by rw [s2_128]; omega)
    (3 + (1 + fuel))
  rw [c2]
  simp only [bind_assoc, pure_bind]
  rw [show (s2.getReg .x10 + BitVec.ofNat 64 64).toNat = (s1.getReg .x10 + 120).toNat by rw [s2_64_eq]]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s2 (s1.getReg .x10 + 120).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a2
  change BitVec 256 at a2
  let s3 := leafCall2State s2 a2
  have s3eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s2.setReg .x10 (s2.getReg .x10 + BitVec.ofNat 64 64)).setReg .x12
      (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64))).setPC (s2.pc + 8))
      (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)) a2 = s3 := rfl
  rw [s3eq]
  have s3pc : s3.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 13)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s2.pc + 8 + 4 = _
    rw [s2pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  have s3r5 : s3.getReg .x5 = 0 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r5
  have s3r11 : s3.getReg .x11 = 96 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r11
  have s3r13 : s3.getReg .x13 = 0 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r13
  have s3r10 : s3.getReg .x10 = s2.getReg .x10 + 64 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]
  have s3r23 : s3.getReg .x23 = state.getReg .x23 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r23
  -- Call 3 (3 instructions at +13..+15)
  have s3_64_eq : s3.getReg .x10 + BitVec.ofNat 64 64 = s2.getReg .x10 + 128 := by
    rw [s3r10, BitVec.add_assoc]; rfl
  have s3_64 : (s3.getReg .x10 + BitVec.ofNat 64 64).toNat = slot + 184 := by
    rw [s3_64_eq]; exact s2_128
  have s3_heap : (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)).toNat = heap + heapOffset j := by
    rw [s3r23]; exact heapOffNat
  have c3 := exec_two_addi_ecall s3 j 13 hj (Or.inr (Or.inr rfl)) s3pc s3r5 s3r11 s3r13 64 rfl
    (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) rfl
    (by simp only [rangeValid, s3_64, decide_eq_true_eq]; omega) (by rw [s3_64]; omega)
    (by simp only [rangeValid, s3_heap, decide_eq_true_eq]; omega) (by rw [s3_heap]; omega)
    (1 + fuel)
  rw [c3]
  simp only [bind_assoc, pure_bind]
  rw [show (s3.getReg .x10 + BitVec.ofNat 64 64).toNat = (s2.getReg .x10 + 128).toNat by rw [s3_64_eq]]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s3 (s2.getReg .x10 + 128).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a3
  change BitVec 256 at a3
  let s4 := leafCall3State s3 j a3
  have s4eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s3.setReg .x10 (s3.getReg .x10 + BitVec.ofNat 64 64)).setReg .x12
      (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j))).setPC (s3.pc + 8))
      (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) a3 = s4 := rfl
  rw [s4eq]
  have s4pc : s4.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 16)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s3.pc + 8 + 4 = _
    rw [s3pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  -- Final instruction: addi x10, x10, 72
  have fAdv : fetch (submission.image .commit) s4 = some (.base (.ADDI .x10 .x10 72)) :=
    commit_fetch s4 (34 + 17 * j + 16) (.ADDI .x10 .x10 72) (by omega) s4pc
      (commit_leaf_decode j 16 hj (by decide))
  have sAdv : ordinaryStep s4 (.base (.ADDI .x10 .x10 72)) = some (leafAdvanceState s4) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, leafAdvanceState]
  rw [show 1 + fuel = fuel + 1 by omega, execute_ordinary_step _ _ _ _ _ _ fAdv sAdv]
  simp [oracleCycles, COMPRESSION_CYCLES, instructionCycles, charge_charge]
  rfl

end CommitGolfCandidate
