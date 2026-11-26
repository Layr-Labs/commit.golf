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

theorem base_reg_frame (k : Nat) : baseReg k ≠ .x0 ∧ baseReg k ≠ .x1 ∧ baseReg k ≠ .x6 ∧ baseReg k ≠ .x7 ∧
    baseReg k ≠ .x8 ∧ baseReg k ≠ .x10 ∧ baseReg k ≠ .x11 ∧ baseReg k ≠ .x18 ∧ baseReg k ≠ .x21 ∧
    baseReg k ≠ .x24 ∧ baseReg k ≠ .x25 ∧ baseReg k ≠ .x30 ∧ baseReg k ≠ .x31 := by
  unfold baseReg
  split <;> decide

theorem table_reg_frame (k : Nat) : tableReg k ≠ .x0 ∧ tableReg k ≠ .x1 ∧ tableReg k ≠ .x6 ∧ tableReg k ≠ .x7 ∧
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

def levelsPrefix : List Instr := setupCode ++ baseCode ++ tableCode ++ endCode ++ saltCode

def levelsRest : List Instr := tailCode ++ [footerJump] ++ List.replicate 41 (.ADDI .x0 .x0 0) ++ exitCode ++
  List.replicate 7 (.ADDI .x0 .x0 0) ++ (List.range 5).flatMap variantCode ++ prefixCode ++ footerCode ++
  (List.replicate 251 (.ADDI .x0 .x0 0) ++ variantsList)

theorem program_levels : program = levelsPrefix ++ ((List.range 7).flatMap levelCode ++ levelsRest) := by
  simp only [program, levelsPrefix, levelsRest, variantsList, List.append_assoc]

theorem levels_prefix_length : levelsPrefix.length = 41 := by decide

def variantsHead : List Instr := levelsPrefix ++ ((List.range 7).flatMap levelCode ++ (tailCode ++ [footerJump] ++
  List.replicate 41 (.ADDI .x0 .x0 0) ++ exitCode ++ List.replicate 7 (.ADDI .x0 .x0 0) ++
  (List.range 5).flatMap variantCode ++ prefixCode ++ footerCode ++ List.replicate 251 (.ADDI .x0 .x0 0)))

theorem program_variants : program = variantsHead ++ variantsList := by
  rw [program_levels]
  simp only [variantsHead, levelsRest, List.append_assoc]

theorem variants_list_length : variantsList.length = 2240 := by
  unfold variantsList
  rw [chunk_length _ 320 _ (fun k _ => by rw [chunk_length _ 64 _ (fun v _ => variant_code_length k v)]; simp)]
  simp

theorem variants_head_length : variantsHead.length = 3072 := by
  have h := congrArg List.length program_variants
  rw [List.length_append, variants_list_length, program_length] at h
  omega

theorem program_variant (k v i : Nat) (hk : k < 7) (hv : v < 5) (hi : i < 64) :
    program[levelVariantStart k v + i]? = (levelVariantCode k v)[i]? := by
  rw [program_variants, List.getElem?_append_right (by rw [variants_head_length]; unfold levelVariantStart; omega),
    variants_head_length, show levelVariantStart k v + i - 3072 = 320*k + (64*v + i) by unfold levelVariantStart; omega]
  unfold variantsList
  rw [chunk_get _ 320 _ (fun k _ => by rw [chunk_length _ 64 _ (fun v _ => variant_code_length k v)]; simp) k _
    (by omega), List.getElem?_range hk, Option.bind_some,
    chunk_get _ 64 _ (fun v _ => variant_code_length k v) v i hi, List.getElem?_range hv, Option.bind_some]

theorem program_level_code (k i : Nat) (hk : k < 7) (hi : i < 9) :
    program[levelStart k + i]? = (levelCode k)[i]? := by
  rw [program_levels, List.getElem?_append_right (by rw [levels_prefix_length]; unfold levelStart; omega),
    levels_prefix_length, show levelStart k + i - 41 = 9*k + i by unfold levelStart; omega,
    List.getElem?_append_left (by rw [chunk_length _ 9 _ (fun k _ => level_code_length k)]; simp; omega),
    chunk_get _ 9 _ (fun k _ => level_code_length k) k i hi, List.getElem?_range hk, Option.bind_some]

theorem level_codes : ∀ k < 7, CodeAt (levelStart k) (levelHead k) ∧ CodeAt (levelStart k+6) (dispatchCode k) ∧
    program[levelStart k+8]? = some (.JALR .x0 .x7 0) := by
  intro k hk
  have hh : (levelHead k).length = 6 := by simp [levelHead, headWith]
  have hd : (dispatchCode k).length = 2 := by simp [dispatchCode]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [hh] at hi
    rw [program_level_code k i hk (by omega), levelCode, List.append_assoc, List.getElem?_append_left (by omega)]
  · rw [hd] at hi
    rw [Nat.add_assoc, program_level_code k (6+i) hk (by omega), levelCode, List.append_assoc,
      List.getElem?_append_right (by omega), hh, Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)]
  · rw [program_level_code k 8 hk (by omega), levelCode, List.getElem?_append_right (by simp [hh, hd])]
    simp [hh, hd]

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
theorem dispatch_target : ∀ k < 7, ∀ r < 5,
    (BitVec.ofNat 64 r <<< (8 : Nat) + BitVec.ofNat 64 (tableStart k) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*levelVariantStart k r) := by decide

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

structure LevelAt (init state : MachineState) (positions : Positions) (o k : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*levelStart k)
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

theorem level_step (init state : MachineState) (positions : Positions) (o k : Nat) (hk7 : k < 7)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (at_ : LevelAt init state positions o k) :
    Runs state (levelRun k state) (levelSteps k) (levelCycles k) ∧ LevelAt init (levelRun k state) positions o (k+1) ∧
      ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 →
        r ≠ .x30 → r ≠ .x31 → (levelRun k state).getReg r = state.getReg r := by
  have hk : k < 11 := by omega
  let i := ordinalIndex positions o
  let n := i/5^k
  let rr := n%5
  let G := trapdoorBase+pentaGroupBase k+40+368*(n/5)
  obtain ⟨c₁, c₂, c₃⟩ := level_codes k hk7
  have hr : rr < 5 := Nat.mod_lt _ (by decide)
  obtain ⟨v₁, v₂, v₃⟩ := variant_codes k hk7 rr hr
  have small : n < 2^30 := by
    have := Nat.div_le_self i (5^k); have : i < 2^24 := inside; omega
  have nodeNe (r : Reg) (a : r ≠ .x6) (b : r ≠ .x24) : r ≠ nodeReg (k+1) := ne_node_reg r (k+1) a b
  -- head
  let s₀ := (levelHead k).foldl execInstrBr state
  have headPure : (levelHead k).all pureOp = true := by simp [levelHead, headWith, pureOp]
  have run₀ := runs_pure _ _ state c₁ at_.pc headPure
  have post₀ := level_head_post state k n hk7 small at_.node at_.five at_.width (at_.bases k hk7)
  have pc₀ : s₀.pc = BitVec.ofNat 64 (4096+4*(levelStart k+6)) := by
    rw [pure_pc _ _ headPure, at_.pc, pc_offset]
    rfl
  have keep₀ (r : Reg) (a : r ≠ .x10) (c : r ≠ .x25) (e : r ≠ .x30) (b : r ≠ nodeReg (k+1)) :
      s₀.getReg r = state.getReg r := post₀.2.2.2 r a c e b
  -- dispatch address
  let s₁ := (dispatchCode k).foldl execInstrBr s₀
  have dispatchPure : (dispatchCode k).all pureOp = true := by simp [dispatchCode, pureOp]
  have run₁ := runs_pure _ _ s₀ c₂ pc₀ dispatchPure
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8)) := by
    rw [pure_pc _ _ dispatchPure, pc₀, pc_offset]
    rfl
  obtain ⟨_, _, t6, t7, _, t10, _, _, _, t24, t25, t30, _⟩ := table_reg_frame k
  have keep₁ (r : Reg) (a : r ≠ .x7) : s₁.getReg r = s₀.getReg r := by
    simp [s₁, dispatchCode, execInstrBr, Ne.symm a]
  have x7₁ : s₁.getReg .x7 = BitVec.ofNat 64 rr <<< (8 : Nat) + BitVec.ofNat 64 (tableStart k) := by
    have h25 : s₀.getReg .x25 = BitVec.ofNat 64 rr := post₀.2.1
    have ht : s₀.getReg (tableReg k) = BitVec.ofNat 64 (tableStart k) :=
      (keep₀ (tableReg k) t10 t25 t30 (nodeNe _ t6 t24)).trans (at_.tables k hk7)
    simp only [s₁, dispatchCode, List.foldl_cons, List.foldl_nil]
    simp only [execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp [t7, Ne.symm t7, h25, ht]
  have x25₁ : s₁.getReg .x25 = BitVec.ofNat 64 rr := (keep₁ .x25 (by decide)).trans post₀.2.1
  have split₁ : (levelHead k ++ dispatchCode k).foldl execInstrBr state = s₁ := by
    simp only [s₁, s₀, List.foldl_append]
  -- jump into the variant
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  have run₂ := runs_jalr s₁ .x0 .x7 _ c₃ pc₁
  obtain ⟨jpc₂, jmem₂, _, jkeep₂⟩ := jalr_post s₁ .x0 .x7
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*levelVariantStart k rr) := by
    rw [jpc₂, x7₁]
    exact dispatch_target k hk7 rr hr
  have keep₂ (r : Reg) (b : r ≠ .x7) : s₂.getReg r = s₀.getReg r := by
    by_cases z : r = .x0
    · subst z; rfl
    · exact (jkeep₂ r z).trans (keep₁ r b)
  -- the copy
  have source (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o k+m) = G+variantOffset rr m := by
    have level := word_source_level positions o k (m/4) (m%4) hk7 (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i k (m/4) inside hk (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*k+m = 114*o+2+16*k+4*(m/4)+m%4 by omega, level, neighbour]
    unfold variantOffset
    simp only [G, rr, n]
    omega
  have Galigned : G % 8 = 0 := by
    have := (neighbour_source i k 0 inside hk (by decide)).2.1
    rw [(neighbour_source i k 0 inside hk (by decide)).1] at this
    simp only [G, n]
    omega
  have Ghigh : G+160 ≤ proofBase := by
    have count := div_lt_count i inside (k+1)
    have room := group_room k hk
    have split : i/5^(k+1) = i/5^k/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    have : trapdoorBase = 4294971424 := rfl
    have : proofBase = 10804535392 := rfl
    simp only [G, n]
    rw [split] at count
    omega
  have fitsAll : proofBase+8*(114*(o+1)) ≤ MEMORY_BYTES := by
    have : proofBase = 10804535392 := rfl
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have notTop : levelDest o k = proofBase+8*(114*o) := by
    unfold levelDest; rw [if_neg (by omega)]; rfl
  have x30₂ : s₂.getReg .x30 = BitVec.ofNat 64 G := (keep₂ .x30 (by decide)).trans post₀.2.2.1
  have x21₂ : s₂.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(114*o)) :=
    (keep₂ .x21 (by decide)).trans
      ((keep₀ .x21 (by decide) (by decide) (by decide) (nodeNe _ (by decide) (by decide))).trans
        (at_.dest.trans (by rw [notTop])))
  have inv₂ : Inv init s₂ (wordSource positions) (levelWord o k) := by
    refine (at_.inv.of_mem (pure_mem _ _ headPure)).of_mem ?_
    rw [jmem₂]
    exact pure_mem _ _ dispatchPure
  obtain ⟨run₃, inv₃, pc₃, regs₃⟩ := level_block init (wordSource positions) (levelVariantStart k rr) k rr G
    (proofBase+8*(114*o)) (levelWord o k) hk7 hr v₁ Galigned (by have : trapdoorBase = 4294971424 := rfl; omega)
    Ghigh (by unfold storeOffset levelWord; omega) (by unfold levelWord; omega) source 16 le_rfl s₂ pc₂ x30₂ x21₂ inv₂
  let s₃ := (levelPairs k rr 16).foldl execInstrBr s₂
  -- advance the cursor after level 6
  have advancePure : (levelAdvance k).all pureOp = true := by
    by_cases last : k = 6 <;> simp [levelAdvance, last, pureOp]
  have run₄ := runs_pure _ _ s₃ v₂ pc₃ advancePure
  let s₄ := (levelAdvance k).foldl execInstrBr s₃
  have pc₄ : s₄.pc = BitVec.ofNat 64 (4096+4*levelExitWord k rr) := by
    rw [pure_pc _ _ advancePure, pc₃, pc_offset]
    unfold levelExitWord
    rfl
  have keep₄ (r : Reg) (a : r ≠ .x21) (b : r ≠ .x31) : s₄.getReg r = s₂.getReg r := by
    by_cases last : k = 6 <;> simp [s₄, levelAdvance, last, execInstrBr, Ne.symm a] <;> exact regs₃ r b
  have x21₄ : s₄.getReg .x21 = BitVec.ofNat 64 (levelDest o (k+1)) := by
    by_cases last : k = 6
    · simp [s₄, levelAdvance, last, execInstrBr, signExtend12]
      rw [regs₃ .x21 (by decide), x21₂, ← BitVec.ofNat_add]
      unfold levelDest
      rw [if_pos (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · simp [s₄, levelAdvance, last]
      rw [regs₃ .x21 (by decide), x21₂]
      unfold levelDest
      rw [if_neg (by omega)]
      rfl
  -- jump to the next level
  have run₅ := runs_jal s₄ _ _ v₃ pc₄
  let s₅ := execInstrBr s₄ (.JAL .x0 (backJump (levelExitWord k rr) (nextStart k)))
  obtain ⟨jpc₅, jmem₅, jkeep₅⟩ := jal_post s₄ (backJump (levelExitWord k rr) (nextStart k))
  have shape : levelRun k state = s₅ := by
    simp only [levelRun, split₁, x25₁, word_lt rr (by omega)]
    rfl
  have keep (r : Reg) (a : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x21) (e : r ≠ .x25) (f : r ≠ .x30)
      (g : r ≠ .x31) (b : r ≠ nodeReg (k+1)) : (levelRun k state).getReg r = state.getReg r := by
    rw [shape, jkeep₅, keep₄ r d g, keep₂ r a, keep₀ r c e f b]
  have keepAll (r : Reg) (a : r ≠ .x6) (c : r ≠ .x7) (d : r ≠ .x10) (e : r ≠ .x21) (f : r ≠ .x24)
      (g : r ≠ .x25) (h : r ≠ .x30) (l : r ≠ .x31) : (levelRun k state).getReg r = state.getReg r :=
    keep r c d e g h l (nodeNe r a f)
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [shape]
    exact (run₀.trans (run₁.trans (run₂.trans (run₃.trans (run₄.trans run₅))))).cast
      (by by_cases last : k = 6 <;> simp [levelSteps, levelHead, headWith, dispatchCode, levelAdvance, last])
      (by by_cases last : k = 6 <;>
        simp [levelCycles, cost, levelHead, headWith, dispatchCode, levelAdvance, last, instructionCycles])
  · rw [shape, jpc₅, pc₄]
    exact exit_target k hk7 rr hr
  · rw [shape, jkeep₅, keep₄ _ (ne_node_reg _ _ (by decide) (by decide)).symm
      (ne_node_reg _ _ (by decide) (by decide)).symm]
    rw [keep₂ _ (ne_node_reg _ _ (by decide) (by decide)).symm, post₀.1]
    congr 1
    rw [pow_succ, Nat.div_div_eq_div_mul]
  · rw [shape, jkeep₅]
    exact x21₄
  · exact (keepAll .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans at_.heap
  · exact (keepAll .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans at_.five
  · exact (keepAll .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans at_.width
  · intro j hj
    obtain ⟨_, _, a, b, _, c, _, _, d, e, f, g, h⟩ := base_reg_frame j
    exact (keepAll (baseReg j) a b c d e f g h).trans (at_.bases j hj)
  · intro j hj
    obtain ⟨_, _, a, b, _, c, _, _, d, e, f, g, h⟩ := table_reg_frame j
    exact (keepAll (tableReg j) a b c d e f g h).trans (at_.tables j hj)
  · rw [shape]
    have mem : s₅.mem = s₃.mem := by
      rw [jmem₅, pure_mem _ _ advancePure]
    exact (inv₃.of_mem mem).cast_count (by unfold levelWord; omega)
  · intro r _ a b c _ e f g h l
    exact keepAll r a b c e f g h l

end TwoPermutationPrototype.QuadOpening
