import CommitGolfCandidate.TwoPermutationPackedUnpackCopy

/-! Pieces of one iteration of the back-to-front copy loop (words 445-513). -/
namespace TwoPermutationPrototype.Packed.Checker
variable [UnpackOrigin]
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-! ### Unpacked bytes by field -/

theorem ub_src (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : i%498 < 15) :
    unpackedByte Q k n i = Q.getD (481*(i/498) + i%498) 0 := by
  rw [unpackedByte, if_pos h1, if_pos h2]

theorem ub_salt (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : i%498 = 15) :
    unpackedByte Q k n i = BitVec.ofNat 8 ((Q.getD (481*(i/498) + 45) 0).toNat % 4) := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_pos h2]

theorem ub_leaf (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : 15 < i%498) (h3 : i%498 < 46) :
    unpackedByte Q k n i = Q.getD (481*(i/498) + i%498 - 1) 0 := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_neg (by omega), if_pos h3]

theorem ub_leaf30 (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : i%498 = 46) :
    unpackedByte Q k n i = BitVec.ofNat 8 ((Q.getD (481*(i/498) + 45) 0).toNat / 4) := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem ub_zero (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : i%498 = 47) :
    unpackedByte Q k n i = 0 := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

theorem ub_rec (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : ¬ i%498 < 48) (h3 : (i%498-48)%30 ≠ 29) :
    unpackedByte Q k n i = Q.getD (481*(i/498) + 46 + 29*((i%498-48)/30) + (i%498-48)%30) 0 := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg h2, if_neg h3]

theorem ub_rec29 (Q : Proof) (k n i : Nat) (h1 : i < 498*k) (h2 : ¬ i%498 < 48) (h3 : (i%498-48)%30 = 29) :
    unpackedByte Q k n i = remByte Q k n (15*(i/498) + (i%498-48)/30) := by
  rw [unpackedByte, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg h2, if_pos h3]

theorem ub_foot (Q : Proof) (k n i : Nat) (h1 : ¬ i < 498*k) (h3 : (i-498*k)%30 ≠ 29) :
    unpackedByte Q k n i = Q.getD (481*k + 29*((i-498*k)/30) + (i-498*k)%30) 0 := by
  rw [unpackedByte, if_neg h1, if_neg h3]

theorem ub_foot29 (Q : Proof) (k n i : Nat) (h1 : ¬ i < 498*k) (h3 : (i-498*k)%30 = 29) :
    unpackedByte Q k n i = remByte Q k n (15*k + (i-498*k)/30) := by
  rw [unpackedByte, if_neg h1, if_pos h3]

/-! ### Blocks -/

theorem bltu_step (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (a b : Reg)
    (off : BitVec 13) (bounded : index < 1024) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.BLTU a b off)))
    (target : Nat) (ht : BitVec.ofNat 64 (4096+4*index) + signExtend13 off = BitVec.ofNat 64 (4096+4*target)) :
    Hop s (s.setPC (if v a < v b then BitVec.ofNat 64 (4096+4*target)
      else BitVec.ofNat 64 (4096+4*(index+1)))) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [bltu_exec s v hv, pc, ht, pc_next] at h
  exact h

def digitBlock : List Instr := [.ADDI .x23 .x0 29]
def digitCopy : List Instr := [.ADD .x26 .x26 .x25, .ADD .x26 .x26 .x15]

theorem dg_x23 (v : Reg → Nat) (h0 : v .x0 = 0) : digitBlock.foldl stepV v .x23 = 29 := by
  simp only [digitBlock]; vsimp; rw [h0]

theorem dc_x26 (v : Reg → Nat) (base c p : Nat) (h26 : v .x26 = base) (h25 : v .x25 = c)
    (h15 : v .x15 = proofBase) (hp : base + c = p) (pb : p ≤ 2^34) :
    digitCopy.foldl stepV v .x26 = proofBase + p := by
  simp only [digitCopy]; vsimp; rw [h26, h25, h15]; unfold proofBase; omega

def addBase : List Instr := [.ADD .x26 .x26 .x15]

theorem ab_x26 (v : Reg → Nat) (p : Nat) (h26 : v .x26 = p) (h15 : v .x15 = proofBase) (pb : p ≤ 2^34) :
    addBase.foldl stepV v .x26 = proofBase + p := by
  simp only [addBase]; vsimp; rw [h26, h15]; unfold proofBase; omega

def recordBlock : List Instr :=
  [.ADDI .x23 .x0 498, .DIVU .x24 .x22 .x23, .MUL .x25 .x24 .x23, .SUB .x25 .x22 .x25, .ADDI .x23 .x0 481,
   .MUL .x26 .x24 .x23, .ADDI .x23 .x0 48]

theorem rc_x24 (v : Reg → Nat) (i : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (ib : i ≤ 2^34) :
    recordBlock.foldl stepV v .x24 = i/498 := by
  simp only [recordBlock]; vsimp; rw [h0, h22]; vnorm

theorem rc_x25 (v : Reg → Nat) (i : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (ib : i ≤ 2^34) :
    recordBlock.foldl stepV v .x25 = i%498 := by
  simp only [recordBlock]; vsimp; rw [h0, h22]; vnorm
  have e : i / 498 * 498 % 18446744073709551616 = i / 498 * 498 := Nat.mod_eq_of_lt (by omega)
  rw [e]; omega

theorem rc_x26 (v : Reg → Nat) (i : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (ib : i ≤ 2^34) :
    recordBlock.foldl stepV v .x26 = 481*(i/498) := by
  simp only [recordBlock]; vsimp; rw [h0, h22]; vnorm; omega

theorem rc_x23 (v : Reg → Nat) (h0 : v .x0 = 0) : recordBlock.foldl stepV v .x23 = 48 := by
  simp only [recordBlock]; vsimp; rw [h0]

def set15 : List Instr := [.ADDI .x23 .x0 15]
def set46 : List Instr := [.ADDI .x23 .x0 46]
def srcBlock : List Instr := [.ADD .x26 .x26 .x25]
def leafBlock : List Instr := [.ADD .x26 .x26 .x25, .ADDI .x26 .x26 4095]

theorem s15_x23 (v : Reg → Nat) (h0 : v .x0 = 0) : set15.foldl stepV v .x23 = 15 := by
  simp only [set15]; vsimp; rw [h0]

theorem s46_x23 (v : Reg → Nat) (h0 : v .x0 = 0) : set46.foldl stepV v .x23 = 46 := by
  simp only [set46]; vsimp; rw [h0]

theorem sb_x26 (v : Reg → Nat) (a b : Nat) (h26 : v .x26 = a) (h25 : v .x25 = b) (hb : a + b < 2^64) :
    srcBlock.foldl stepV v .x26 = a + b := by
  simp only [srcBlock]; vsimp; rw [h26, h25]; omega

theorem lb_x26 (v : Reg → Nat) (a b : Nat) (h26 : v .x26 = a) (h25 : v .x25 = b) (hb : a + b < 2^63)
    (pos : 1 ≤ a + b) : leafBlock.foldl stepV v .x26 = a + b - 1 := by
  simp only [leafBlock]; vsimp; rw [h26, h25]; omega

def digestBlock : List Instr :=
  [.SUB .x25 .x25 .x23, .ADDI .x23 .x0 30, .DIVU .x30 .x25 .x23, .MUL .x31 .x30 .x23, .SUB .x25 .x25 .x31,
   .ADDI .x26 .x26 46, .ADDI .x23 .x0 29, .MUL .x31 .x30 .x23, .ADD .x26 .x26 .x31, .ADDI .x23 .x0 15,
   .MUL .x31 .x24 .x23, .ADD .x30 .x31 .x30]

theorem dg_x25 (v : Reg → Nat) (t : Nat) (h0 : v .x0 = 0) (h25 : v .x25 = t) (h23 : v .x23 = 48)
    (lo : 48 ≤ t) (hi : t < 498) : digestBlock.foldl stepV v .x25 = (t-48)%30 := by
  simp only [digestBlock]; vsimp; rw [h0, h25, h23]; vnorm; omega

theorem dg_x26 (v : Reg → Nat) (t r : Nat) (h0 : v .x0 = 0) (h25 : v .x25 = t) (h23 : v .x23 = 48)
    (h26 : v .x26 = 481*r) (lo : 48 ≤ t) (hi : t < 498) (rb : r ≤ 2^34) :
    digestBlock.foldl stepV v .x26 = 481*r + 46 + 29*((t-48)/30) := by
  simp only [digestBlock]; vsimp; rw [h0, h25, h23, h26]; vnorm; omega

theorem dg_x30 (v : Reg → Nat) (t r : Nat) (h0 : v .x0 = 0) (h25 : v .x25 = t) (h23 : v .x23 = 48)
    (h24 : v .x24 = r) (lo : 48 ≤ t) (hi : t < 498) (rb : r ≤ 2^34) :
    digestBlock.foldl stepV v .x30 = 15*r + (t-48)/30 := by
  simp only [digestBlock]; vsimp; rw [h0, h25, h23, h24]; vnorm; omega

def footBlock : List Instr :=
  [.SUB .x25 .x22 .x29, .ADDI .x23 .x0 30, .DIVU .x30 .x25 .x23, .MUL .x31 .x30 .x23, .SUB .x25 .x25 .x31,
   .ADDI .x23 .x0 481, .MUL .x26 .x16 .x23, .ADDI .x23 .x0 29, .MUL .x31 .x30 .x23, .ADD .x26 .x26 .x31,
   .ADDI .x23 .x0 15, .MUL .x31 .x16 .x23, .ADD .x30 .x31 .x30]

theorem ft_x25 (v : Reg → Nat) (i k : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (h29 : v .x29 = 498*k)
    (lo : 498*k ≤ i) (ib : i ≤ 2^34) : footBlock.foldl stepV v .x25 = (i-498*k)%30 := by
  simp only [footBlock]; vsimp; rw [h0, h22, h29]; vnorm; vmod; try omega

theorem ft_x26 (v : Reg → Nat) (i k : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (h29 : v .x29 = 498*k)
    (h16 : v .x16 = k) (lo : 498*k ≤ i) (ib : i ≤ 2^34) (kb : k ≤ 2^24) :
    footBlock.foldl stepV v .x26 = 481*k + 29*((i-498*k)/30) := by
  simp only [footBlock]; vsimp; rw [h0, h22, h29, h16]; vnorm; vmod; try omega

theorem ft_x30 (v : Reg → Nat) (i k : Nat) (h0 : v .x0 = 0) (h22 : v .x22 = i) (h29 : v .x29 = 498*k)
    (h16 : v .x16 = k) (lo : 498*k ≤ i) (ib : i ≤ 2^34) (kb : k ≤ 2^24) :
    footBlock.foldl stepV v .x30 = 15*k + (i-498*k)/30 := by
  simp only [footBlock]; vsimp; rw [h0, h22, h29, h16]; vnorm; vmod; try omega

def loopStep : List Instr := [.ADDI .x22 .x22 4095]

theorem ls_x22' (v : Reg → Nat) (m : Nat) (h22 : v .x22 = m) (hm : 0 < m) (mb : m ≤ 2^34) :
    loopStep.foldl stepV v .x22 = m - 1 := by
  simp only [loopStep]; vsimp; rw [h22]; omega

/-! ### The digit tail: words 503-506 -/

theorem digit_tail (input : CheckInput) (vM : Reg → Nat) (mv : MainView input vM) (sz : Sizes input)
    (m : Nat) (hm : 0 < m) (hl : m ≤ lenOf input) (s : MachineState) (v : Reg → Nat) (hv : View s v)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*503)) (h22 : v .x22 = m-1)
    (fr : ∀ r, r ∉ mainWrites → v r = vM r) (mem : ∀ a, s.getByte a = mainMem input m a)
    (c j p : Nat) (h25 : v .x25 = c) (h30 : v .x30 = j) (hc : c < 30)
    (h26 : v .x26 + c = p) (hp : p < m)
    (rem : c = 29 → j < countOf input ∧ remByte input.proof input.positions.card (countOf input) j =
      unpackedByte input.proof input.positions.card (countOf input) (m-1))
    (copy : c ≠ 29 → input.proof.getD p 0 =
      unpackedByte input.proof input.positions.card (countOf input) (m-1)) :
    ∃ t, Hop s t (if c = 29 then 7 else 9) (if c = 29 then 7 else 9) ∧ MainAt input vM (m-1) t := by
  have len := sz.len
  have h0 : v .x0 = 0 := view_x0 hv
  have h15 : v .x15 = proofBase := (fr .x15 (by decide)).trans mv.x15
  obtain ⟨hA, wA, pA, mA⟩ := block_run _ 503 digitBlock v hv (by decide) pc
    (by intro i hi; simp only [digitBlock, List.length] at hi; interval_cases i <;> rfl) rfl
  have g := beq_step _ _ wA 504 .x25 .x23 20 (by decide) pA rfl 509 rfl
  have a23 := dg_x23 v h0
  have a25 : digitBlock.foldl stepV v .x25 = c := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact h25
  rw [a25, a23] at g
  have frA : ∀ r, r ∉ mainWrites → digitBlock.foldl stepV v r = vM r := fun r hr => by
    rw [foldl_stepV_within digitBlock mainWrites (by decide) _ r hr]; exact fr r hr
  have a22 : digitBlock.foldl stepV v .x22 = m-1 := by rw [foldl_stepV_notin _ _ _ (by decide)]; exact h22
  have memA : ∀ a, (digitBlock.foldl execInstrBr s).getByte a = mainMem input m a := fun a => by
    rw [getByte_of_mem mA, mem]
  by_cases c29 : c = 29
  · rw [if_pos c29] at g
    obtain ⟨jn, eq⟩ := rem c29
    obtain ⟨t, ht, at'⟩ := rem_tail input vM mv sz m hm hl _ _ (view_pc_only _ _ _ wA) rfl a22 frA memA j
      (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact h30) jn eq
    refine ⟨t, ?_, at'⟩
    rw [if_pos c29]
    exact (hA.thenDo g).thenDo ht
  · rw [if_neg c29] at g
    have w1 := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*(504+1))) wA
    obtain ⟨hB, wB, pB, mB⟩ := block_run _ 505 digitCopy _ w1 (by decide) rfl
      (by intro i hi; simp only [digitCopy, List.length] at hi; interval_cases i <;> rfl) rfl
    have e26 := dc_x26 (digitBlock.foldl stepV v) (v .x26) c p
      (by rw [foldl_stepV_notin _ _ _ (by decide)]) a25
      (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact h15) h26 (by omega)
    obtain ⟨t, ht, at'⟩ := copy_tail input vM mv sz m hm hl _ _ wB pB
      (by rw [foldl_stepV_notin _ _ _ (by decide)]; exact a22)
      (fun r hr => by rw [foldl_stepV_within digitCopy mainWrites (by decide) _ r hr]; exact frA r hr)
      (fun a => by rw [getByte_of_mem mB, setPC_getByte, memA]) p e26 hp (copy c29)
    refine ⟨t, ?_, at'⟩
    rw [if_neg c29]
    exact ((hA.thenDo g).thenDo hB).thenDo ht

end TwoPermutationPrototype.Packed.Checker
