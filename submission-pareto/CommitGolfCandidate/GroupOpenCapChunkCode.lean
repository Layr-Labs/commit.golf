import CommitGolfCandidate.GroupOpenCapCost
import CommitGolfCandidate.GroupOpenContext
import CommitGolfCandidate.GroupOpenWalk

/-! Chunk code (words 8192..8219) and the 256 frontier blocks (16 words each from word 8224). Words 6144..8191
are reserved for other code and are not read here.

The chunk code reads the eight leaf marks of the level-5 node `x16/8`, forms the leaf mask `m` and jumps to block
`m`. Block `m` holds, for each relative frontier node `r` of `chunkEntries m`, `addi x6,x16,o<<s`, `srli x6,x6,s`
(omitted for a leaf) and `jal x18,<668>`; it ends with `srli x6,x16,3; jal x0,<703>`. The blocks are compared with
the image once (`block_table_code`). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open Opening (markBase machineMarks markWord CapSpan)
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
  if depthOf r=3 then [.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)), .JAL .x18 (jalOffset (w+1) 668)]
  else [.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)), .SRLI .x6 .x6 (BitVec.ofNat 6 (entryShift r)),
    .JAL .x18 (jalOffset (w+2) 668)]

def blockCode : List Nat → Nat → List Instr
  | [], w => [.SRLI .x6 .x16 3, .JAL .x0 (jalOffset (w+1) 703)]
  | r :: rest, w => entryCode r w++blockCode rest (w+entryLen r)

def nopInstr : Instr := (Opening.decodeBase 0x13).getD .EBREAK

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
    ((openingImage.code.drop 8224).take 4096).map Opening.decodeBase=blockTable.map some := by
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
    (openingImage.code[chunkBlockWord mask+j]?).bind Opening.decodeBase=(paddedBlock mask)[j]? := by
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
    (openingImage.code[chunkBlockWord mask+j]?).bind Opening.decodeBase=
      (blockCode (chunkEntries mask) (chunkBlockWord mask))[j]? := by
  have fits := block_fits mask hm nz
  rw [block_decode mask j hm (by omega), paddedBlock]
  simp only [nz, ite_false]
  rw [List.getElem?_append_left hj]

/-- Fetch at any word of the image. -/
theorem packed_fetch_long (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<2^40) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase=some instruction) :
    fetch openingImage state=some (.base instruction) := by
  have current : state.pc.toNat=4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, current, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases code : openingImage.code[index]? with
  | none => simp [code] at decoded
  | some word =>
    simp [code, Opening.decodeBase] at decoded
    cases dec : decodeInstruction word with
    | none => simp [dec] at decoded
    | some result =>
      cases result with
      | base inst =>
        simp [dec] at decoded
        simpa [decoded] using dec
      | word op rd rs₁ rs₂ => simp [dec] at decoded
      | sraiw rd rs sh => simp [dec] at decoded

/-! ### The chunk code -/

def chunkAddrRows : List Row := [(8192,.SLLI .x7 .x16 3),(8193,.ADD .x7 .x7 .x26)]
/-- Mask rows `j .. j+n-1` from word `a`: `ld x29,8j(x7); slli x29,x29,j; or x28,x28,x29`. -/
def maskTail (a : Nat) : Nat → Nat → List Row
  | _, 0 => []
  | j, n+1 => [(a,.LD .x29 .x7 (BitVec.ofNat 12 (8*j))),(a+1,.SLLI .x29 .x29 (BitVec.ofNat 6 j)),
      (a+2,.OR .x28 .x28 .x29)]++maskTail (a+3) (j+1) n
def chunkMaskRows : List Row := [(8194,.LD .x28 .x7 0)]++maskTail 8195 1 7
def chunkJumpRows : List Row := [(8216,.SLLI .x28 .x28 6),(8217,.LUI .x11 9),(8218,.ADD .x11 .x11 .x28),(8219,.JALR .x0 .x11 128)]
def chunkRows : List Row := chunkAddrRows++chunkMaskRows++chunkJumpRows

theorem chunk_rows_present : presentRows chunkRows := by
  have raw : ∀ i : Fin chunkRows.length, chunkRows[i].1<2^40 ∧
      (openingImage.code[chunkRows[i].1]?).bind Opening.decodeBase=some chunkRows[i].2 := by decide +kernel
  intro p hp
  obtain ⟨j, hj, eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  intro st pc
  exact packed_fetch_long st _ _ (raw ⟨j, hj⟩).1 pc (raw ⟨j, hj⟩).2

theorem chunk_rows_price : price chunkRows=28 := by decide

/-- Eight 0/1 marks combine to the mask. -/
theorem mask_combine : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (((((((BitVec.ofNat 64 b0.toNat ||| BitVec.ofNat 64 b1.toNat <<< 1) ||| BitVec.ofNat 64 b2.toNat <<< 2) |||
      BitVec.ofNat 64 b3.toNat <<< 3) ||| BitVec.ofNat 64 b4.toNat <<< 4) ||| BitVec.ofNat 64 b5.toNat <<< 5) |||
      BitVec.ofNat 64 b6.toNat <<< 6) ||| BitVec.ofNat 64 b7.toNat <<< 7)=
    BitVec.ofNat 64 (b0.toNat+2*b1.toNat+4*b2.toNat+8*b3.toNat+16*b4.toNat+32*b5.toNat+64*b6.toNat+
      128*b7.toNat) := by decide +kernel

/-- The marks of the eight leaves under a level-5 node. -/
theorem leaf_mark (groups : List Nat) (state : MachineState) (context : CapContext groups state)
    (node j : Nat) (span : CapSpan node 3) (hj : j<8) :
    state.getMem (BitVec.ofNat 64 (4096+64*node)+signExtend12 (BitVec.ofNat 12 (8*j)))=
      BitVec.ofNat 64 (capIsMarked groups (8*node+j) 0).toNat := by
  have lo := span.start
  have hi := span.finish
  simp only [Nat.reducePow] at lo hi
  have addr : BitVec.ofNat 64 (4096+64*node)+signExtend12 (BitVec.ofNat 12 (8*j))=
      BitVec.ofNat 64 (markBase+8*(8*node+j)) := by
    have : signExtend12 (BitVec.ofNat 12 (8*j))=BitVec.ofNat 64 (8*j) := by
      interval_cases j <;> decide
    rw [this, ← BitVec.ofNat_add]; congr 1; unfold markBase; ring
  rw [addr]
  have value := context.markValue (8*node+j) (by omega) (by omega)
  unfold machineMarks at value
  have leaf : Opening.capHeight (8*node+j)=0 := Opening.cap_leaf_height ⟨8*node+j, by omega⟩ (by simp; omega)
  rw [value, markWord, leaf]

end TwoPermutationPrototype.GroupedOpening
