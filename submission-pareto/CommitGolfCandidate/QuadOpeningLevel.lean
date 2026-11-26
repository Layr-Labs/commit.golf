import CommitGolfCandidate.QuadOpeningRun

/-! One level of a penta record: `x6 = index / 5^k` gives the group base of the four other
children in the trapdoor; they are appended to the output as 16 doublewords. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Record layout -/

/-- Level-`k` node index of the `j`-th other child (Nat version of `pentaNeighbour`). -/
def neighbourNat (i k j : Nat) : Nat := 5*(i/5^(k+1)) + (i/5^k%5+j+1)%5

theorem neighbour_nat (index : Index) (k j : Nat) : pentaNeighbour index k j = neighbourNat index.val k j := rfl

/-- Initial address of doubleword `d < 114` of the record of position `i`. -/
def recordSource (i d : Nat) : Nat :=
  if d < 2 then nonceBase+16*i+8*d
  else trapdoorBase+pentaSlotOffset ((d-2)/16) (neighbourNat i ((d-2)/16) ((d-2)%16/4))+8*((d-2)%4)

/-- The position written by record `o` (0 past the end). -/
def ordinalIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

/-- Record doublewords at stride 114 (912-byte records; the table has its own source map). -/
def wordSource (positions : Positions) (u : Nat) : Nat := recordSource (ordinalIndex positions (u/114)) (u%114)

theorem word_source_level (positions : Positions) (o k j w : Nat) (hk : k < 7) (hj : j < 4) (hw : w < 4) :
    wordSource positions (114*o+2+16*k+4*j+w) =
      trapdoorBase+pentaSlotOffset k (neighbourNat (ordinalIndex positions o) k j)+8*w := by
  unfold wordSource recordSource
  have q : (114*o+2+16*k+4*j+w)/114 = o := by omega
  have r : (114*o+2+16*k+4*j+w)%114 = 2+16*k+4*j+w := by omega
  rw [q, r, if_neg (by omega)]
  have a : (2+16*k+4*j+w-2)/16 = k := by omega
  have b : (2+16*k+4*j+w-2)%16/4 = j := by omega
  have c : (2+16*k+4*j+w-2)%4 = w := by omega
  rw [a, b, c]

theorem word_source_salt (positions : Positions) (o w : Nat) (hw : w < 2) :
    wordSource positions (114*o+w) = nonceBase+16*ordinalIndex positions o+8*w := by
  unfold wordSource recordSource
  have q : (114*o+w)/114 = o := by omega
  have r : (114*o+w)%114 = w := by omega
  rw [q, r, if_pos hw]

theorem div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i/5^k < pentaCount k
  | 0 => by simpa [pentaCount] using inside
  | k+1 => by
    have ih := div_lt_count i inside k
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    show i/5^k/5 < (pentaCount k+4)/5
    omega

theorem group_room : ∀ k < 11, pentaGroupBase k+368*pentaCount (k+1) ≤ 1543577600 := by decide
private theorem group_aligned : ∀ k < 11, (pentaGroupBase k+40) % 8 = 0 := by decide

theorem neighbour_source (i k j : Nat) (inside : i < LENGTH) (hk : k < 11) (hj : j < 4) :
    trapdoorBase+pentaSlotOffset k (neighbourNat i k j) =
      trapdoorBase+pentaGroupBase k+40+368*(i/5^k/5)+32*((i/5^k%5+j+1)%5) ∧
    (trapdoorBase+pentaSlotOffset k (neighbourNat i k j)) % 8 = 0 ∧
    trapdoorBase+pentaSlotOffset k (neighbourNat i k j)+32 ≤ proofBase ∧
    pentaSlotOffset k (neighbourNat i k j)+32 ≤ 1543577600 := by
  have split : i/5^(k+1) = i/5^k/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have count := div_lt_count i inside (k+1)
  rw [split] at count
  have room := group_room k hk
  have aligned := group_aligned k hk
  have slot := Nat.mod_lt (i/5^k%5+j+1) (show 0 < 5 by decide)
  have heap : trapdoorBase = 4294971424 := rfl
  have proof : proofBase = 10804535392 := rfl
  unfold pentaSlotOffset neighbourNat
  rw [split]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Register arithmetic -/

theorem word_lt (n : Nat) (small : n < 2^64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem divu_five (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n/5) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem remu_five (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n%5) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem rem_by_shift (n : Nat) (small : n < 2^40) :
    BitVec.ofNat 64 n - ((BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5)) = BitVec.ofNat 64 (n%5) := by
  apply BitVec.eq_of_toNat_eq
  have five : (BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5) = BitVec.ofNat 64 (5*(n/5)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
    omega
  rw [five, BitVec.toNat_sub, word_lt _ (by omega), word_lt _ (by omega), word_lt _ (by omega)]
  omega

theorem mul_width (q : Nat) (small : q < 2^40) :
    BitVec.ofNat 64 q * BitVec.ofNat 64 368 = BitVec.ofNat 64 (368*q) := by
  rw [← BitVec.ofNat_mul]
  congr 1
  omega

theorem lui_page : ∀ k < 11,
    ((BitVec.ofNat 20 (groupPage k)).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (pentaGroupBase k+40) := by
  decide

theorem shift_slot (m : Nat) (small : m < 2^40) : BitVec.ofNat 64 m <<< (5 : Nat) = BitVec.ofNat 64 (32*m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show m*2^5 % 2^64 = _
  omega

theorem addi_small : ∀ j < 4, signExtend12 (BitVec.ofNat 12 (j+1)) = BitVec.ofNat 64 (j+1) := by decide

/-! ### Level head -/

theorem base_reg_frame (k : Nat) : baseReg k ≠ .x0 ∧ baseReg k ≠ .x27 ∧ baseReg k ≠ .x6 ∧ baseReg k ≠ .x7 ∧
    baseReg k ≠ .x8 ∧ baseReg k ≠ .x10 ∧ baseReg k ≠ .x11 ∧ baseReg k ≠ .x18 ∧ baseReg k ≠ .x21 ∧
    baseReg k ≠ .x24 ∧ baseReg k ≠ .x25 ∧ baseReg k ≠ .x30 ∧ baseReg k ≠ .x31 := by
  unfold baseReg
  split <;> decide

theorem table_reg_frame (k : Nat) : tableReg k ≠ .x0 ∧ tableReg k ≠ .x27 ∧ tableReg k ≠ .x6 ∧ tableReg k ≠ .x7 ∧
    tableReg k ≠ .x8 ∧ tableReg k ≠ .x10 ∧ tableReg k ≠ .x11 ∧ tableReg k ≠ .x18 ∧ tableReg k ≠ .x21 ∧
    tableReg k ≠ .x24 ∧ tableReg k ≠ .x25 ∧ tableReg k ≠ .x30 ∧ tableReg k ≠ .x31 := by
  unfold tableReg
  split <;> decide

theorem node_reg_cases (j : Nat) : nodeReg j = .x6 ∨ nodeReg j = .x24 := by
  unfold nodeReg
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem node_reg_succ (j : Nat) : nodeReg j ≠ nodeReg (j+1) := by
  unfold nodeReg
  split <;> split <;> first | decide | omega

/-- Every register other than `x6` and `x24` differs from a node register. -/
theorem ne_node_reg (r : Reg) (j : Nat) (a : r ≠ .x6) (b : r ≠ .x24) : r ≠ nodeReg j := by
  rcases node_reg_cases j with h | h <;> rw [h] <;> assumption

/-- A level head with node register `a`, parent register `b` and group-base register `base`. -/
theorem head_with_post (state : MachineState) (a b base : Reg) (n G : Nat) (small : n < 2^30)
    (ab : a ≠ b) (b0 : b ≠ .x0) (b10 : b ≠ .x10) (b19 : b ≠ .x19) (b23 : b ≠ .x23) (b25 : b ≠ .x25)
    (b30 : b ≠ .x30) (a10 : a ≠ .x10) (a25 : a ≠ .x25) (c10 : base ≠ .x10) (c25 : base ≠ .x25) (cb : base ≠ b)
    (node : state.getReg a = BitVec.ofNat 64 n) (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (width : state.getReg .x23 = BitVec.ofNat 64 368) (hbase : state.getReg base = BitVec.ofNat 64 G) :
    let after := (headWith a b base).foldl execInstrBr state
    after.getReg b = BitVec.ofNat 64 (n/5) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%5) ∧
      after.getReg .x30 = BitVec.ofNat 64 (G+368*(n/5)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x25 → r ≠ .x30 → r ≠ b → after.getReg r = state.getReg r := by
  intro after
  have quotient := divu_five n (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [after, headWith, execInstrBr, node, five, quotient, b0, b10, b25, b30, Ne.symm b10, Ne.symm b25,
      Ne.symm b30]
  · simp [after, headWith, execInstrBr, node, five, quotient, b0, ab, Ne.symm ab, b25, Ne.symm b25,
      a25, Ne.symm a25]
    exact rem_by_shift n (by omega)
  · simp [after, headWith, execInstrBr, node, five, quotient, width, hbase, b0, ab, Ne.symm ab, b10,
      Ne.symm b10, b23, Ne.symm b23, b25, Ne.symm b25, c10, Ne.symm c10, c25, Ne.symm c25, cb, Ne.symm cb]
    rw [mul_width _ (by omega), ← BitVec.ofNat_add]
    congr 1
    omega
  · intro r h10 h25 h30 hb
    simp [after, headWith, execInstrBr, Ne.symm h10, Ne.symm h25, Ne.symm h30, Ne.symm hb]

/-- The level head reads the node from `nodeReg k` and the preloaded group base from `baseReg k`. -/
theorem level_head_post (state : MachineState) (k n : Nat) (hk : k < 7) (small : n < 2^30)
    (node : state.getReg (nodeReg k) = BitVec.ofNat 64 n) (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (width : state.getReg .x23 = BitVec.ofNat 64 368)
    (base : state.getReg (baseReg k) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40)) :
    let after := (levelHead k).foldl execInstrBr state
    after.getReg (nodeReg (k+1)) = BitVec.ofNat 64 (n/5) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%5) ∧
      after.getReg .x30 = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40+368*(n/5)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x25 → r ≠ .x30 → r ≠ nodeReg (k+1) → after.getReg r = state.getReg r := by
  obtain ⟨_, _, c6, _, _, c10, _, _, _, c24, c25, _, _⟩ := base_reg_frame k
  have cases (j : Nat) : nodeReg j ≠ .x0 ∧ nodeReg j ≠ .x10 ∧ nodeReg j ≠ .x19 ∧ nodeReg j ≠ .x23 ∧
      nodeReg j ≠ .x25 ∧ nodeReg j ≠ .x30 := by
    rcases node_reg_cases j with h | h <;> rw [h] <;> decide
  obtain ⟨b0, b10, b19, b23, b25, b30⟩ := cases (k+1)
  obtain ⟨_, a10, _, _, a25, _⟩ := cases k
  exact head_with_post state (nodeReg k) (nodeReg (k+1)) (baseReg k) n _ small (node_reg_succ k) b0 b10 b19
    b23 b25 b30 a10 a25 c10 c25 (ne_node_reg _ _ c6 c24) node five width base

/-! ### One level -/

def levelStart (k : Nat) : Nat := 41+9*k

/-- Address of the (now unused) word-159 copy variants; the pass still loads it into `x26`. -/
def tableBase : Nat := 4096+4*159

def levelSteps (k : Nat) : Nat := if k = 6 then 43 else 42
def levelCycles (k : Nat) : Nat := if k = 6 then 49 else 48

/-- Output doubleword index at which level `k` of record `o` starts. -/
def levelWord (o k : Nat) : Nat := 114*o+2+16*k

/-- `x21` during level `k` of record `o`: the record start, or the next record after level 6. -/
def levelDest (o k : Nat) : Nat := proofBase+8*(114*o+(if k = 7 then 114 else 0))

/-! ### Code placement (structural, without evaluating the whole program) -/

theorem chunk_get {α β : Type} (f : α → List β) (c : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = c) → ∀ i j, j < c →
      (l.flatMap f)[c*i + j]? = (l[i]?).bind (fun x => (f x)[j]?)
  | [], _, i, j, _ => by simp
  | x :: rest, same, i, j, hj => by
    have hx := same x (by simp)
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem?_cons_succ]
      rw [Nat.mul_succ, List.getElem?_append_right (by omega), hx, show c*i+c+j-c = c*i+j by omega]
      exact chunk_get f c rest (fun y hy => same y (by simp [hy])) i j hj

theorem chunk_length {α β : Type} (f : α → List β) (c : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = c) → (l.flatMap f).length = c*l.length
  | [], _ => by simp
  | x :: rest, same => by
    rw [List.flatMap_cons, List.length_append, same x (by simp),
      chunk_length f c rest (fun y hy => same y (by simp [hy]))]
    simp [Nat.mul_succ]; omega

theorem level_code_length (k : Nat) : (levelCode k).length = 9 := by
  simp [levelCode, levelHead, headWith, dispatchCode]

theorem variant_code_length (k v : Nat) : (levelVariantCode k v).length = 64 := by
  unfold levelVariantCode levelAdvance
  by_cases h : k = 6 <;> simp [h, level_pairs_length]

def variantsList : List Instr := (List.range 7).flatMap (fun k => (List.range 5).flatMap (levelVariantCode k))

/-- Padding to word 6144 and the three pair-variant blocks. -/
def pairTail : List Instr := List.replicate 832 (.ADDI .x0 .x0 0) ++ pairsList

def levelsPrefix : List Instr := setupCode ++ baseCode ++ tableCode ++ endCode ++ saltCode

def levelsRest : List Instr := tailCode ++ [footerJump] ++ List.replicate 41 (.ADDI .x0 .x0 0) ++ exitCode ++
  List.replicate 7 (.ADDI .x0 .x0 0) ++ (List.range 5).flatMap variantCode ++ prefixCode ++ footerCode ++
  (List.replicate 251 (.ADDI .x0 .x0 0) ++ (variantsList ++ pairTail))

theorem program_levels : program = levelsPrefix ++ (levelsCode ++ levelsRest) := by
  simp only [program, levelsPrefix, levelsRest, variantsList, pairTail, List.append_assoc]

theorem levels_prefix_length : levelsPrefix.length = 41 := by decide

def variantsHead : List Instr := levelsPrefix ++ (levelsCode ++ (tailCode ++ [footerJump] ++
  List.replicate 41 (.ADDI .x0 .x0 0) ++ exitCode ++ List.replicate 7 (.ADDI .x0 .x0 0) ++
  (List.range 5).flatMap variantCode ++ prefixCode ++ footerCode ++ List.replicate 251 (.ADDI .x0 .x0 0)))

theorem program_variants : program = variantsHead ++ (variantsList ++ pairTail) := by
  rw [program_levels]
  simp only [variantsHead, levelsRest, List.append_assoc]

theorem variants_list_length : variantsList.length = 2240 := by
  unfold variantsList
  rw [chunk_length _ 320 _ (fun k _ => by rw [chunk_length _ 64 _ (fun v _ => variant_code_length k v)]; simp)]
  simp

theorem gen_pairs_length (reg : Reg) (off k v n : Nat) : (genPairs reg off k v n).length = 2*n := by
  unfold genPairs
  rw [chunk_length _ 2 _ (fun _ _ => rfl)]
  simp [Nat.mul_comm]

theorem next_prep_length (p : Nat) : (nextPrep p).length ≤ 12 := by
  unfold nextPrep; split <;> simp [pairPrep, prepWith, triplePrep]

theorem pair_variant_code_length (p v : Nat) : (pairVariantCode p v).length = 128 := by
  have := next_prep_length p
  simp only [pairVariantCode, List.length_append, gen_pairs_length, List.length_replicate, List.length_singleton]
  omega

theorem pair_chunk_length (p : Nat) :
    ((List.range 25).flatMap (pairVariantCode p) ++ List.replicate 896 (Instr.ADDI .x0 .x0 0)).length = 4096 := by
  rw [List.length_append, chunk_length _ 128 _ (fun v _ => pair_variant_code_length p v), List.length_replicate,
    List.length_range]

theorem triple_variant_code_length (v : Nat) : (tripleVariantCode v).length = 128 := by
  simp [tripleVariantCode, gen_pairs_length]

theorem pairs_list_length : pairsList.length = 24192 := by
  unfold pairsList
  rw [List.length_append, chunk_length _ 4096 _ (fun p _ => pair_chunk_length p), List.length_range,
    chunk_length _ 128 _ (fun v _ => triple_variant_code_length v), List.length_range]

theorem variants_head_length : variantsHead.length = 3072 := by
  have h := congrArg List.length program_variants
  have t : pairTail.length = 25024 := by
    rw [pairTail, List.length_append, List.length_replicate, pairs_list_length]
  rw [List.length_append, List.length_append, variants_list_length, t, program_length] at h
  omega

theorem program_variant (k v i : Nat) (hk : k < 7) (hv : v < 5) (hi : i < 64) :
    program[levelVariantStart k v + i]? = (levelVariantCode k v)[i]? := by
  rw [program_variants, List.getElem?_append_right (by rw [variants_head_length]; unfold levelVariantStart; omega),
    variants_head_length, show levelVariantStart k v + i - 3072 = 320*k + (64*v + i) by unfold levelVariantStart; omega,
    List.getElem?_append_left (by rw [variants_list_length]; omega)]
  unfold variantsList
  rw [chunk_get _ 320 _ (fun k _ => by rw [chunk_length _ 64 _ (fun v _ => variant_code_length k v)]; simp) k _
    (by omega), List.getElem?_range hk, Option.bind_some,
    chunk_get _ 64 _ (fun v _ => variant_code_length k v) v i hi, List.getElem?_range hv, Option.bind_some]

theorem pair_block_length (p : Nat) : (pairBlock p).length = 18 := by
  simp [pairBlock, pairHead, pairPrep, prepWith]

theorem levels_code_get (i : Nat) (hi : i < 36) :
    levelsCode[i]? = ((List.range 2).flatMap pairBlock)[i]? := by
  unfold levelsCode
  rw [List.getElem?_append_left (by rw [chunk_length _ 18 _ (fun p _ => pair_block_length p)]; simp; omega)]

theorem triple_block_length : tripleBlock.length = 27 := by
  simp [tripleBlock, tripleHead, triplePrep]

theorem levels_code_length : levelsCode.length = 63 := by
  unfold levelsCode
  rw [List.length_append, chunk_length _ 18 _ (fun p _ => pair_block_length p), triple_block_length]
  simp

theorem program_pair_block (p i : Nat) (hp : p < 2) (hi : i < 18) :
    program[41+18*p+i]? = (pairBlock p)[i]? := by
  rw [program_levels, List.getElem?_append_right (by rw [levels_prefix_length]; omega),
    levels_prefix_length, show 41+18*p+i-41 = 18*p+i by omega,
    List.getElem?_append_left (by rw [levels_code_length]; omega),
    levels_code_get _ (by omega), chunk_get _ 18 _ (fun p _ => pair_block_length p) p i hi,
    List.getElem?_range hp, Option.bind_some]

theorem program_triple_block (i : Nat) (hi : i < 27) :
    program[77+i]? = tripleBlock[i]? := by
  rw [program_levels, List.getElem?_append_right (by rw [levels_prefix_length]; omega),
    levels_prefix_length, show 77+i-41 = 36+i by omega,
    List.getElem?_append_left (by rw [levels_code_length]; omega)]
  unfold levelsCode
  rw [List.getElem?_append_right (by rw [chunk_length _ 18 _ (fun p _ => pair_block_length p)]; simp),
    chunk_length _ 18 _ (fun p _ => pair_block_length p)]
  simp

theorem variant_codes : ∀ k < 7, ∀ v < 5, CodeAt (levelVariantStart k v) (levelPairs k v 16) ∧
    CodeAt (levelVariantStart k v+32) (levelAdvance k) ∧
    program[levelExitWord k v]? = some (.JAL .x0 (backJump (levelExitWord k v) (nextStart k))) := by
  intro k hk v hv
  have hp : (levelPairs k v 16).length = 32 := level_pairs_length k v 16
  have ha : (levelAdvance k).length ≤ 1 := by unfold levelAdvance; split <;> simp
  have shape : levelVariantCode k v = levelPairs k v 16 ++ (levelAdvance k ++
      ([.JAL .x0 (backJump (levelExitWord k v) (nextStart k))] ++
        List.replicate (31-(levelAdvance k).length) (.ADDI .x0 .x0 0))) := by
    simp only [levelVariantCode, List.append_assoc]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [hp] at hi
    rw [program_variant k v i hk hv (by omega), shape, List.getElem?_append_left (by omega)]
  · rw [Nat.add_assoc, program_variant k v (32+i) hk hv (by omega), shape,
      List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left, List.getElem?_append_left hi]
  · have e : levelExitWord k v = levelVariantStart k v + (32 + (levelAdvance k).length) := by
      unfold levelExitWord; omega
    conv_lhs => rw [e]
    rw [program_variant k v _ hk hv (by omega), shape,
      List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left,
      List.getElem?_append_right (by omega), Nat.sub_self]
    rfl

theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

set_option maxRecDepth 100000 in
theorem exit_target : ∀ k < 7, ∀ v < 5,
    BitVec.ofNat 64 (4096+4*levelExitWord k v) + signExtend21 (backJump (levelExitWord k v) (nextStart k)) =
      BitVec.ofNat 64 (4096+4*levelStart (k+1)) := by decide

/-- One jump-and-link step. -/
theorem runs_jalr (state : MachineState) (rd rs : Reg) (index : Nat)
    (code : program[index]? = some (.JALR rd rs 0)) (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    Runs state (execInstrBr state (.JALR rd rs 0)) 1 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state index _ code pc) rfl]
  rfl

theorem jalr_post (state : MachineState) (rd rs : Reg) :
    (execInstrBr state (.JALR rd rs 0)).pc = (state.getReg rs + signExtend12 0) &&& ~~~1#64 ∧
    (execInstrBr state (.JALR rd rs 0)).mem = state.mem ∧
    (rd ≠ .x0 → (execInstrBr state (.JALR rd rs 0)).getReg rd = state.pc + 4) ∧
    ∀ r, r ≠ rd → (execInstrBr state (.JALR rd rs 0)).getReg r = state.getReg r := by
  refine ⟨rfl, mem_set_reg _ _ _, ?_, ?_⟩
  · intro nonzero
    simp [execInstrBr, nonzero]
  · intro r other
    simp [execInstrBr, Ne.symm other]

/-- One jump step (no link). -/
theorem runs_jal (state : MachineState) (imm : BitVec 21) (index : Nat)
    (code : program[index]? = some (.JAL .x0 imm)) (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    Runs state (execInstrBr state (.JAL .x0 imm)) 1 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state index _ code pc) rfl]
  rfl

theorem jal_post (state : MachineState) (imm : BitVec 21) :
    (execInstrBr state (.JAL .x0 imm)).pc = state.pc + signExtend21 imm ∧
    (execInstrBr state (.JAL .x0 imm)).mem = state.mem ∧
    ∀ r, (execInstrBr state (.JAL .x0 imm)).getReg r = state.getReg r := by
  refine ⟨rfl, mem_set_reg _ _ _, ?_⟩
  intro r
  simp [execInstrBr]

structure LevelAt (init state : MachineState) (positions : Positions) (o k start : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*start)
  node : state.getReg (nodeReg k) = BitVec.ofNat 64 (ordinalIndex positions o / 5^k)
  dest : state.getReg .x21 = BitVec.ofNat 64 (levelDest o k)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  five : state.getReg .x19 = BitVec.ofNat 64 5
  width : state.getReg .x23 = BitVec.ofNat 64 368
  bases : ∀ j < 7, state.getReg (baseReg j) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase j+40)
  tables : ∀ j < 7, state.getReg (tableReg j) = BitVec.ofNat 64 (tableStart j)
  inv : Inv init state (wordSource positions) (levelWord o k)

/-- One level: head, dispatch into the level-`k` variant `x25`, copy, (advance), jump to the next level. -/
def levelRun (k : Nat) (state : MachineState) : MachineState :=
  let s₁ := (levelHead k ++ dispatchCode k).foldl execInstrBr state
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  let v := (s₁.getReg .x25).toNat
  let s₃ := (levelPairs k v 16).foldl execInstrBr s₂
  let s₄ := (levelAdvance k).foldl execInstrBr s₃
  execInstrBr s₄ (.JAL .x0 (backJump (levelExitWord k v) (nextStart k)))

end TwoPermutationPrototype.QuadOpening
