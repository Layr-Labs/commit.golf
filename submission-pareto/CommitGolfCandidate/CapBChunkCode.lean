import CommitGolfCandidate.CapBPrice
import CommitGolfCandidate.CapBPrepCode
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.GroupedOpening
open TwoPermutationPrototype.GroupedOpening.CapB (entryLen)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- First word of block `mask`. -/
def chunkBlockWord (mask : Nat) : Nat := 8224+16*mask

/-- `jal` offset from word `w` to word `t`. -/
def jalOffset (w t : Nat) : BitVec 21 := BitVec.ofInt 21 (4*((t : Int)-w))

/-- Shift and pre-shifted offset of relative node `r`: `chunkNode n r = (8 n + entryOffset r) >>> entryShift r`. -/
def entryShift (r : Nat) : Nat := 3-depthOf r
def entryOffset (r : Nat) : Nat := (r-2^depthOf r)*2^(entryShift r)

def entryCode (r w : Nat) : List Instr :=
  if depthOf r=3 then [.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)), .JALR .x18 .x19 0]
  else [.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)), .SRLI .x6 .x6 (BitVec.ofNat 6 (entryShift r)),
    .JALR .x18 .x19 0]

def blockCode : List Nat → Nat → List Instr
  | [], w => [.SRLI .x6 .x16 3, .JAL .x0 (jalOffset (w+1) 703)]
  | r :: rest, w => entryCode r w++blockCode rest (w+entryLen r)

def nopInstr : Instr := (CommitGolfCandidate.CapB.decodeBase 0x13).getD .EBREAK

def paddedBlock (mask : Nat) : List Instr :=
  let code := if mask=0 then [] else blockCode (chunkEntries mask) (chunkBlockWord mask)
  code++List.replicate (16-code.length) nopInstr

def blockTable : List Instr := (List.range 256).flatMap paddedBlock

theorem entry_code_length (r w : Nat) : (entryCode r w).length=entryLen r := by
  unfold entryCode entryLen; split <;> rfl

theorem padded_length : ∀ mask < 256, (paddedBlock mask).length=16 := by decide +kernel

theorem block_fits : ∀ mask < 256, mask ≠ 0 → (blockCode (chunkEntries mask) (chunkBlockWord mask)).length ≤ 16 := by
  decide +kernel

/-- The 4096 block words of the image decode to the block table (one kernel pass). -/
theorem block_table_code :
    ((openingImage.code.drop 8224).take 4096).map CommitGolfCandidate.CapB.decodeBase=blockTable.map some := by
  decide +kernel

private theorem flat_uniform {β : Type} (f : Nat → List β) (L : Nat) : ∀ (xs : List Nat),
    (∀ a ∈ xs, (f a).length=L) → ∀ m j, (hm : m<xs.length) → j<L → (xs.flatMap f)[L*m+j]?=(f xs[m])[j]?
  | [], _, m, j, hm, _ => absurd hm (by simp)
  | x :: rest, hL, m, j, hm, hj => by
    have hx : (f x).length=L := hL x (by simp)
    rw [List.flatMap_cons]
    cases m with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ m =>
      rw [List.getElem?_append_right (by rw [hx]; nlinarith), hx,
        show L*(m+1)+j-L=L*m+j by rw [Nat.mul_succ]; omega]
      exact flat_uniform f L rest (fun a ha => hL a (List.mem_cons_of_mem _ ha)) m j
        (by simpa using hm) hj

private theorem bind_of_map {α β : Type} (o : Option α) (f : α → Option β) (p : Option β)
    (h : o.map f=p.map some) : o.bind f=p := by
  cases o <;> cases p <;> simp_all

/-- Word `j` of block `mask` decodes to word `j` of the padded block. -/
theorem block_decode (mask j : Nat) (hm : mask<256) (hj : j<16) :
    (openingImage.code[chunkBlockWord mask+j]?).bind CommitGolfCandidate.CapB.decodeBase=(paddedBlock mask)[j]? := by
  have eq := congrArg (fun l => l[16*mask+j]?) block_table_code
  simp only [List.getElem?_map] at eq
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at eq
  have table : blockTable[16*mask+j]?=(paddedBlock mask)[j]? := by
    have h := flat_uniform paddedBlock 16 (List.range 256)
      (fun a ha => padded_length a (List.mem_range.mp ha)) mask j (by simpa using hm) hj
    simpa [blockTable] using h
  rw [table] at eq
  unfold chunkBlockWord
  rw [show 8224+16*mask+j=8224+(16*mask+j) by omega]
  exact bind_of_map _ _ _ eq

/-- Instruction `j` of the block code of a marked mask. -/
theorem block_instr (mask j : Nat) (hm : mask<256) (nz : mask ≠ 0)
    (hj : j<(blockCode (chunkEntries mask) (chunkBlockWord mask)).length) :
    (openingImage.code[chunkBlockWord mask+j]?).bind CommitGolfCandidate.CapB.decodeBase=
      (blockCode (chunkEntries mask) (chunkBlockWord mask))[j]? := by
  have fits := block_fits mask hm nz
  rw [block_decode mask j hm (by omega), paddedBlock]
  simp only [nz, ite_false]
  rw [List.getElem?_append_left hj]

theorem chunk_entries_range : ∀ mask<256, mask ≠ 0 → ∀ r ∈ chunkEntries mask, 2 ≤ r ∧ r<16 := by decide +kernel

theorem chunk_node_lt (node r : Nat) (hn : node<64) (lo : 2 ≤ r) (hi : r<16) : chunkNode node r<512 := by
  unfold chunkNode depthOf
  interval_cases r <;> simp <;> omega

theorem entry_node (node r : Nat) (lo : 2 ≤ r) (hi : r<16) :
    (8*node+entryOffset r)/2^(entryShift r)=chunkNode node r ∧ entryOffset r<8 := by
  unfold entryOffset entryShift chunkNode depthOf
  interval_cases r <;> simp <;> omega

theorem small_imm (k : Nat) (hk : k<8) : signExtend12 (BitVec.ofNat 12 k)=BitVec.ofNat 64 k := by
  interval_cases k <;> decide

/-- The block code from word `w` decodes as listed. -/
def BlockAt (rs : List Nat) (w : Nat) : Prop :=
  ∀ j<(blockCode rs w).length, (openingImage.code[w+j]?).bind CommitGolfCandidate.CapB.decodeBase=(blockCode rs w)[j]?

theorem block_at_tail (r : Nat) (rest : List Nat) (w : Nat) (code : BlockAt (r :: rest) w) :
    BlockAt rest (w+entryLen r) := by
  intro j hj
  have total : (blockCode (r :: rest) w).length=entryLen r+(blockCode rest (w+entryLen r)).length := by
    simp [blockCode, entry_code_length]
  have h := code (entryLen r+j) (by omega)
  rw [show w+(entryLen r+j)=w+entryLen r+j by omega] at h
  rw [h, blockCode, List.getElem?_append_right (by rw [entry_code_length]; omega), entry_code_length,
    show entryLen r+j-entryLen r=j by omega]

theorem block_at_head (r : Nat) (rest : List Nat) (w : Nat) (code : BlockAt (r :: rest) w) (j : Nat)
    (hj : j<entryLen r) :
    (openingImage.code[w+j]?).bind CommitGolfCandidate.CapB.decodeBase=(entryCode r w)[j]? := by
  have h := code j (by simp [blockCode, entry_code_length]; omega)
  rw [h, blockCode, List.getElem?_append_left (by rw [entry_code_length]; exact hj)]

theorem block_code_two : ∀ (rs : List Nat) (w : Nat), 2 ≤ (blockCode rs w).length
  | [], w => by simp [blockCode]
  | r :: rest, w => by
    rw [blockCode, List.length_append, entry_code_length]
    have := block_code_two rest (w+entryLen r)
    omega

end CommitGolfCandidate.CapB
