import CommitGolfCandidate.QuadOpeningPair

/-! The record levels `(4, 5, 6)` as one triple: one division of the level-4 node by 125 selects one
of 125 copy variants, which copies the four siblings at each of the three levels and advances the
output cursor to the next record. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Arithmetic -/

theorem divu_125 (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 125) = BitVec.ofNat 64 (n/125) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 125 (by decide), word_lt _ (by omega)]

theorem remu_125 (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 125) = BitVec.ofNat 64 (n%125) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 125 (by decide), word_lt _ (by omega)]

theorem triple_prep_post (state : MachineState) (n B4 B5 B6 T : Nat) (small : n < 2^30)
    (node : state.getReg .x6 = BitVec.ofNat 64 n) (div : state.getReg .x28 = BitVec.ofNat 64 125)
    (width : state.getReg .x23 = BitVec.ofNat 64 368)
    (h4 : state.getReg .x13 = BitVec.ofNat 64 B4) (h5 : state.getReg .x14 = BitVec.ofNat 64 B5)
    (h6 : state.getReg .x16 = BitVec.ofNat 64 B6) (ht : state.getReg .x20 = BitVec.ofNat 64 T)
    (s4 : B4 < 2^40) (s5 : B5 < 2^40) (s6 : B6 < 2^40) (sT : T < 2^40) :
    let after := triplePrep.foldl execInstrBr state
    after.getReg .x24 = BitVec.ofNat 64 (n/125) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%125) ∧
      after.getReg .x27 = BitVec.ofNat 64 (B6+368*(n/125)) ∧
      after.getReg .x11 = BitVec.ofNat 64 (B5+1840*(n/125)) ∧
      after.getReg .x30 = BitVec.ofNat 64 (B4+9200*(n/125)) ∧
      after.getReg .x7 = BitVec.ofNat 64 (512*(n%125)+T) ∧
      ∀ r, r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x25 → r ≠ .x27 → r ≠ .x30 →
        after.getReg r = state.getReg r := by
  intro after
  have quotient := divu_125 n (by omega)
  have remainder := remu_125 n (by omega)
  have w := mul_width (n/125) (by omega)
  have f := five_width (368*(n/125)) (by omega)
  have f2 := five_width (5*(368*(n/125))) (by omega)
  have s9 := shift_nine (n%125) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, triplePrep, execInstrBr, node, div, quotient, remainder]
  · simp [after, triplePrep, execInstrBr, node, div, remainder]
  · simp [after, triplePrep, execInstrBr, baseReg, node, div, quotient, remainder, width, w, h6]
    rw [← BitVec.ofNat_add]; congr 1; omega
  · simp [after, triplePrep, execInstrBr, baseReg, node, div, quotient, remainder, width, w, f, h5]
    rw [← BitVec.ofNat_add]; congr 1; omega
  · simp [after, triplePrep, execInstrBr, baseReg, node, div, quotient, remainder, width, w, f, f2, h4]
    rw [← BitVec.ofNat_add]; congr 1; omega
  · simp [after, triplePrep, execInstrBr, baseReg, node, div, quotient, remainder, width, w, f, f2, ht, s9]
    rw [← BitVec.ofNat_add]
  · intro r a b c d e g l
    simp [after, triplePrep, execInstrBr, baseReg, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e,
      Ne.symm g, Ne.symm l]

set_option maxRecDepth 100000 in
theorem triple_low_offsets : ∀ v < 125, ∀ m < 16,
    BitVec.ofNat 64 (4096*tripleHi v) +
      signExtend12 (BitVec.ofNat 12 (368*(v/5)+8192-4096*tripleHi v+variantOffset (v%5) m)) =
      BitVec.ofNat 64 (368*(v/5)+variantOffset (v%5) m) := by
  decide

set_option maxRecDepth 100000 in
theorem triple_lui : ∀ v < 125,
    ((BitVec.ofNat 20 (tripleHi v)).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (4096*tripleHi v) := by
  decide

set_option maxRecDepth 100000 in
theorem triple_dispatch_target : ∀ v < 125,
    (BitVec.ofNat 64 (512*v+tableStart 2) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*tripleStart v) := by decide

set_option maxRecDepth 100000 in
theorem triple_exit_target : ∀ v < 125,
    BitVec.ofNat 64 (4096+4*tripleExitWord v) + signExtend21 (backJump (tripleExitWord v) 104) =
      BitVec.ofNat 64 (4096+4*levelStart 7) := by decide

/-! ### Code placement -/

theorem triple_prep_length : triplePrep.length = 12 := by simp [triplePrep]

theorem triple_head_codes : CodeAt (41+9*4) triplePrep ∧ program[41+9*4+12]? = some (.JALR .x0 .x7 0) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [triple_prep_length] at hi
    rw [show 41+9*4+i = 77+i by omega, program_triple_block i (by omega), tripleBlock, tripleHead,
      List.append_assoc, List.getElem?_append_left (by rw [triple_prep_length]; omega)]
  · rw [show 41+9*4+12 = 77+12 by omega, program_triple_block 12 (by omega), tripleBlock, tripleHead,
      List.append_assoc, List.getElem?_append_right (by rw [triple_prep_length]), triple_prep_length]
    rfl

theorem program_triple_variant (v i : Nat) (hv : v < 125) (hi : i < 128) :
    program[tripleStart v + i]? = (tripleVariantCode v)[i]? := by
  rw [program_variants, List.getElem?_append_right (by rw [variants_head_length]; unfold tripleStart; omega),
    variants_head_length, List.getElem?_append_right (by rw [variants_list_length]; unfold tripleStart; omega),
    variants_list_length, pairTail, List.getElem?_append_right (by rw [List.length_replicate]; unfold tripleStart; omega),
    List.length_replicate]
  unfold pairsList
  rw [List.getElem?_append_right (by
      rw [chunk_length _ 4096 _ (fun p _ => pair_chunk_length p)]; simp; unfold tripleStart; omega),
    chunk_length _ 4096 _ (fun p _ => pair_chunk_length p), List.length_range,
    show tripleStart v + i - 3072 - 2240 - 832 - 4096*2 = 128*v + i by unfold tripleStart; omega,
    chunk_get _ 128 _ (fun v _ => triple_variant_code_length v) v i hi, List.getElem?_range hv, Option.bind_some]

def tripleLui (v : Nat) : List Instr := [.LUI .x10 (BitVec.ofNat 20 (tripleHi v)), .ADD .x30 .x30 .x10]

theorem triple_variant_codes (v : Nat) (hv : v < 125) :
    CodeAt (tripleStart v) (tripleLui v) ∧
    CodeAt (tripleStart v+2) (genPairs .x30 (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) 16) ∧
    CodeAt (tripleStart v+34) (genPairs .x11 (368*(v/25)) 5 (v/5%5) 16) ∧
    CodeAt (tripleStart v+66) (genPairs .x27 0 6 (v/25) 16) ∧
    CodeAt (tripleStart v+98) [.ADDI .x21 .x21 912] ∧
    program[tripleExitWord v]? = some (.JAL .x0 (backJump (tripleExitWord v) 104)) := by
  have l1 := gen_pairs_length .x30 (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) 16
  have l2 := gen_pairs_length .x11 (368*(v/25)) 5 (v/5%5) 16
  have l3 := gen_pairs_length .x27 0 6 (v/25) 16
  have shape : tripleVariantCode v = tripleLui v ++ (genPairs .x30 (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) 16 ++
      (genPairs .x11 (368*(v/25)) 5 (v/5%5) 16 ++ (genPairs .x27 0 6 (v/25) 16 ++
      ([.ADDI .x21 .x21 912] ++ ([.JAL .x0 (backJump (tripleExitWord v) 104)] ++
        List.replicate 28 (.ADDI .x0 .x0 0)))))) := by
    simp only [tripleVariantCode, tripleLui, List.append_assoc, List.cons_append, List.nil_append]
  have ll : (tripleLui v).length = 2 := rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [ll] at hi
    rw [program_triple_variant v i hv (by omega), shape, List.getElem?_append_left (by rw [ll]; omega)]
  · rw [l1] at hi
    rw [Nat.add_assoc, program_triple_variant v _ hv (by omega), shape,
      List.getElem?_append_right (by rw [ll]; omega), ll, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
  · rw [l2] at hi
    rw [Nat.add_assoc, program_triple_variant v _ hv (by omega), shape,
      List.getElem?_append_right (by rw [ll]; omega), ll, List.getElem?_append_right (by omega), l1,
      show 34+i-2-32 = i by omega, List.getElem?_append_left (by omega)]
  · rw [l3] at hi
    rw [Nat.add_assoc, program_triple_variant v _ hv (by omega), shape,
      List.getElem?_append_right (by rw [ll]; omega), ll, List.getElem?_append_right (by omega), l1,
      List.getElem?_append_right (by omega), l2, show 66+i-2-32-32 = i by omega,
      List.getElem?_append_left (by omega)]
  · have i0 : i = 0 := by simp at hi; omega
    subst i0
    rw [Nat.add_assoc, program_triple_variant v _ hv (by omega), shape,
      List.getElem?_append_right (by rw [ll]; omega), ll, List.getElem?_append_right (by omega), l1,
      List.getElem?_append_right (by omega), l2, List.getElem?_append_right (by omega), l3]
    rfl
  · unfold tripleExitWord
    rw [program_triple_variant v 99 hv (by omega), shape,
      List.getElem?_append_right (by rw [ll]; omega), ll, List.getElem?_append_right (by omega), l1,
      List.getElem?_append_right (by omega), l2, List.getElem?_append_right (by omega), l3]
    rfl

/-! ### The triple -/

def tripleRun (state : MachineState) : MachineState :=
  let s₁ := triplePrep.foldl execInstrBr state
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  let v := (s₁.getReg .x25).toNat
  let s₃ := (tripleLui v).foldl execInstrBr s₂
  let s₄ := (genPairs .x30 (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) 16).foldl execInstrBr s₃
  let s₅ := (genPairs .x11 (368*(v/25)) 5 (v/5%5) 16).foldl execInstrBr s₄
  let s₆ := (genPairs .x27 0 6 (v/25) 16).foldl execInstrBr s₅
  let s₇ := ([.ADDI .x21 .x21 912] : List Instr).foldl execInstrBr s₆
  execInstrBr s₇ (.JAL .x0 (backJump (tripleExitWord v) 104))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem triple_level_step (init state : MachineState) (positions : Positions) (o start : Nat)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (c₁ : CodeAt start triplePrep) (c₂ : program[start+12]? = some (.JALR .x0 .x7 0))
    (at_ : LevelAt init state positions o 4 start) :
    Runs state (tripleRun state) 113 122 ∧ LevelAt init (tripleRun state) positions o 7 (levelStart 7) ∧
      ∀ r, r ≠ .x27 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 →
        r ≠ .x30 → r ≠ .x31 → (tripleRun state).getReg r = state.getReg r := by
  let i := ordinalIndex positions o
  let n := i/5^4
  let v := n%125
  have hn : n = i/5^4 := rfl
  have hvn : v = n%125 := rfl
  have hv : v < 125 := Nat.mod_lt _ (by decide)
  have small : n < 2^30 := by
    have := Nat.div_le_self i (5^4); have : i < 2^24 := inside; omega
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅⟩ := triple_variant_codes v hv
  have node : state.getReg .x6 = BitVec.ofNat 64 n := at_.node
  have div : state.getReg .x28 = BitVec.ofNat 64 125 := at_.tables 4 (by decide)
  have hT : state.getReg .x20 = BitVec.ofNat 64 (tableStart 2) := at_.tables 2 (by decide)
  have B4 : state.getReg .x13 = _ := at_.bases 4 (by decide)
  have B5 : state.getReg .x14 = _ := at_.bases 5 (by decide)
  have B6 : state.getReg .x16 = _ := at_.bases 6 (by decide)
  have bkSmall : ∀ j < 11, trapdoorBase+pentaGroupBase j+40 < 2^40 := by decide
  have hTB : trapdoorBase = 4294971424 := rfl
  have hPB : proofBase = 10804535392 := rfl
  have room4 := group_room 4 (by decide)
  have room5 := group_room 5 (by decide)
  have room6 := group_room 6 (by decide)
  have galign : ∀ j < 11, (pentaGroupBase j+40) % 8 = 0 := by decide
  have ga4 := galign 4 (by decide)
  have ga5 := galign 5 (by decide)
  have ga6 := galign 6 (by decide)
  -- head
  let s₁ := triplePrep.foldl execInstrBr state
  have prepPure : triplePrep.all pureOp = true := by simp [triplePrep, pureOp]
  have run₁ := runs_pure _ _ state c₁ at_.pc prepPure
  obtain ⟨p24, p25, p27, p11, p30, p7, pkeep⟩ := triple_prep_post state n _ _ _ _ small node div at_.width
    B4 B5 B6 hT (bkSmall 4 (by decide)) (bkSmall 5 (by decide)) (bkSmall 6 (by decide)) (by decide)
  replace p24 : s₁.getReg .x24 = _ := p24
  replace p25 : s₁.getReg .x25 = _ := p25
  replace p27 : s₁.getReg .x27 = _ := p27
  replace p11 : s₁.getReg .x11 = _ := p11
  replace p30 : s₁.getReg .x30 = _ := p30
  replace p7 : s₁.getReg .x7 = _ := p7
  replace pkeep : ∀ r, r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x25 → r ≠ .x27 → r ≠ .x30 →
      s₁.getReg r = state.getReg r := pkeep
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(start+12)) := by
    rw [pure_pc _ _ prepPure, at_.pc, triple_prep_length, pc_offset]
  -- jump into the variant
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  have run₂ := runs_jalr s₁ .x0 .x7 _ c₂ pc₁
  obtain ⟨jpc₂, jmem₂, _, jkeep₂⟩ := jalr_post s₁ .x0 .x7
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*tripleStart v) := by
    rw [jpc₂, p7]
    exact triple_dispatch_target v hv
  have keep₂ (r : Reg) : s₂.getReg r = s₁.getReg r := by
    by_cases z : r = .x0
    · subst z; rfl
    · exact jkeep₂ r z
  -- page of the level-4 pointer
  let G4 := trapdoorBase+pentaGroupBase 4+40+9200*(n/125)
  let G5 := trapdoorBase+pentaGroupBase 5+40+1840*(n/125)
  let G6 := trapdoorBase+pentaGroupBase 6+40+368*(n/125)
  have hG4 : G4 = trapdoorBase+pentaGroupBase 4+40+9200*(n/125) := rfl
  have hG5 : G5 = trapdoorBase+pentaGroupBase 5+40+1840*(n/125) := rfl
  have hG6 : G6 = trapdoorBase+pentaGroupBase 6+40+368*(n/125) := rfl
  let s₃ := (tripleLui v).foldl execInstrBr s₂
  have luiPure : (tripleLui v).all pureOp = true := rfl
  have run₃ := runs_pure _ _ s₂ v₀ pc₂ luiPure
  have pc₃ : s₃.pc = BitVec.ofNat 64 (4096+4*(tripleStart v+2)) := by
    rw [pure_pc _ _ luiPure, pc₂, pc_offset]; rfl
  have x30₃ : s₃.getReg .x30 = BitVec.ofNat 64 G4 + BitVec.ofNat 64 (4096*tripleHi v) := by
    simp [s₃, tripleLui, execInstrBr, keep₂, p30, triple_lui v hv]
    rfl
  have keep₃ (r : Reg) (a : r ≠ .x10) (b : r ≠ .x30) : s₃.getReg r = s₂.getReg r := by
    simp [s₃, tripleLui, execInstrBr, Ne.symm a, Ne.symm b]
  -- sources
  have count7 := div_lt_count i inside 7
  have count5 := div_lt_count i inside 5
  have count6 := div_lt_count i inside 6
  have e5 : i/5^5 = n/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have e6 : i/5^6 = n/25 := by
    rw [show (5:Nat)^6 = 5^4*25 by norm_num, ← Nat.div_div_eq_div_mul]
  have e7 : i/5^7 = n/125 := by
    rw [show (5:Nat)^7 = 5^4*125 by norm_num, ← Nat.div_div_eq_div_mul]
  rw [e7] at count7; rw [e5] at count5; rw [e6] at count6
  have pc5 : pentaCount 5 = 5369 := by decide
  have pc6 : pentaCount 6 = 1074 := by decide
  have pc7 : pentaCount 7 = 215 := by decide
  have fitsAll : proofBase+8*(114*(o+1)) ≤ MEMORY_BYTES := by
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have source4 (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o 4+m) = G4+368*(v/5)+variantOffset (v%5) m := by
    have level := word_source_level positions o 4 (m/4) (m%4) (by decide) (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i 4 (m/4) inside (by decide) (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*4+m = 114*o+2+16*4+4*(m/4)+m%4 by omega, level, neighbour]
    unfold variantOffset
    rw [hG4, hvn, ← hn]
    omega
  have source5 (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o 4+16+m) = G5+368*(v/25)+variantOffset (v/5%5) m := by
    have level := word_source_level positions o 5 (m/4) (m%4) (by decide) (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i 5 (m/4) inside (by decide) (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*4+16+m = 114*o+2+16*5+4*(m/4)+m%4 by omega, level, neighbour, e5]
    unfold variantOffset
    rw [hG5, hvn]
    omega
  have source6 (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o 4+32+m) = G6+0+variantOffset (v/25) m := by
    have level := word_source_level positions o 6 (m/4) (m%4) (by decide) (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i 6 (m/4) inside (by decide) (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*4+32+m = 114*o+2+16*6+4*(m/4)+m%4 by omega, level, neighbour, e6]
    unfold variantOffset
    rw [hG6, hvn]
    omega
  have notTop : levelDest o 4 = proofBase+8*(114*o) := by
    unfold levelDest; rw [if_neg (by omega)]; rfl
  have x21₃ : s₃.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(114*o)) := by
    rw [keep₃ _ (by decide) (by decide), keep₂, pkeep .x21 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), at_.dest, notTop]
  have inv₃ : Inv init s₃ (wordSource positions) (levelWord o 4) := by
    refine ((at_.inv.of_mem (pure_mem _ _ prepPure)).of_mem ?_).of_mem (pure_mem _ _ luiPure)
    rw [jmem₂]
  have r0 : v%5 < 5 := Nat.mod_lt _ (by decide)
  have r1 : v/5%5 < 5 := Nat.mod_lt _ (by decide)
  have r2 : v/25 < 5 := by omega
  -- level 4
  have addr4 : ∀ w < 16, BitVec.ofNat 64 (G4+4096*tripleHi v) +
      signExtend12 (BitVec.ofNat 12 (368*(v/5)+8192-4096*tripleHi v+variantOffset (v%5) w)) =
      BitVec.ofNat 64 (G4+368*(v/5)+variantOffset (v%5) w) := by
    intro w hw
    rw [← BitVec.ofNat_add_ofNat, BitVec.add_assoc, triple_low_offsets v hv w hw, ← BitVec.ofNat_add]
    congr 1
    omega
  have x30₃' : s₃.getReg .x30 = BitVec.ofNat 64 (G4+4096*tripleHi v) := by
    rw [x30₃, BitVec.ofNat_add_ofNat]
  obtain ⟨run₄, inv₄, pc₄, regs₄⟩ := gen_block init (wordSource positions) .x30 (tripleStart v+2)
    (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) (G4+4096*tripleHi v) (G4+368*(v/5))
    (proofBase+8*(114*o)) (levelWord o 4) (by decide) (by decide) v₁ addr4
    (by rw [hG4]; omega) (by rw [hG4]; omega) (by rw [hG4, hvn]; omega)
    (by unfold storeOffset levelWord; omega) (by unfold levelWord; omega) source4
    16 le_rfl s₃ pc₃ x30₃' x21₃ inv₃
  let s₄ := (genPairs .x30 (368*(v/5)+8192-4096*tripleHi v) 4 (v%5) 16).foldl execInstrBr s₃
  -- level 5
  have x11₄ : s₄.getReg .x11 = BitVec.ofNat 64 G5 := by
    rw [regs₄ _ (by decide), keep₃ _ (by decide) (by decide), keep₂, p11]
  have fits5 : proofBase+8*(levelWord o 4+16+16) ≤ MEMORY_BYTES := by
    have e : levelWord o 4+16+16 = 114*o+2+16*4+32 := by unfold levelWord; omega
    rw [e]; omega
  obtain ⟨run₅, inv₅, pc₅, regs₅⟩ := gen_block init (wordSource positions) .x11 (tripleStart v+34)
    (368*(v/25)) 5 (v/5%5) G5 (G5+368*(v/25)) (proofBase+8*(114*o)) (levelWord o 4+16) (by decide) (by decide) v₂
    (fun w hw => by rw [addr_small _ _ (gen_offset_value _ r2 _ r1 w hw), ← Nat.add_assoc])
    (by rw [hG5]; omega) (by rw [hG5]; omega) (by rw [hG5, hvn]; omega)
    (by unfold storeOffset levelWord; omega) fits5 source5
    16 le_rfl s₄ (by rw [pc₄]) x11₄ ((regs₄ .x21 (by decide)).trans x21₃) (inv₄.cast_count rfl)
  let s₅ := (genPairs .x11 (368*(v/25)) 5 (v/5%5) 16).foldl execInstrBr s₄
  -- level 6
  have x27₅ : s₅.getReg .x27 = BitVec.ofNat 64 G6 := by
    rw [regs₅ _ (by decide), regs₄ _ (by decide), keep₃ _ (by decide) (by decide), keep₂, p27]
  have fits6 : proofBase+8*(levelWord o 4+16+16+16) ≤ MEMORY_BYTES := by
    have e : levelWord o 4+16+16+16 = 114*o+2+16*4+48 := by unfold levelWord; omega
    rw [e]; omega
  have offv6 : ∀ w < 16, signExtend12 (BitVec.ofNat 12 (0+variantOffset (v/25) w)) =
      BitVec.ofNat 64 (0+variantOffset (v/25) w) := by
    intro w hw
    have := gen_offset_value 0 (by decide) (v/25) r2 w hw
    rwa [Nat.mul_zero] at this
  obtain ⟨run₆, inv₆, pc₆, regs₆⟩ := gen_block init (wordSource positions) .x27 (tripleStart v+66)
    0 6 (v/25) G6 (G6+0) (proofBase+8*(114*o)) (levelWord o 4+16+16) (by decide) (by decide) v₃
    (fun w hw => by rw [addr_small _ _ (offv6 w hw), ← Nat.add_assoc])
    (by rw [hG6]; omega) (by rw [hG6]; omega) (by rw [hG6]; omega)
    (by unfold storeOffset levelWord; omega) fits6
    (fun m hm => by rw [show levelWord o 4+16+16+m = levelWord o 4+32+m by omega]; exact source6 m hm)
    16 le_rfl s₅ (by rw [pc₅]) x27₅ ((regs₅ .x21 (by decide)).trans ((regs₄ .x21 (by decide)).trans x21₃))
    (inv₅.cast_count rfl)
  let s₆ := (genPairs .x27 0 6 (v/25) 16).foldl execInstrBr s₅
  -- advance the cursor
  have advPure : ([.ADDI .x21 .x21 912] : List Instr).all pureOp = true := rfl
  have run₇ := runs_pure _ _ s₆ v₄ (by rw [pc₆]) advPure
  let s₇ := ([.ADDI .x21 .x21 912] : List Instr).foldl execInstrBr s₆
  have pc₇ : s₇.pc = BitVec.ofNat 64 (4096+4*tripleExitWord v) := by
    rw [pure_pc _ _ advPure, pc₆, pc_offset]; unfold tripleExitWord; rfl
  have x21₇ : s₇.getReg .x21 = BitVec.ofNat 64 (levelDest o 7) := by
    simp [s₇, execInstrBr, signExtend12]
    rw [regs₆ .x21 (by decide), regs₅ .x21 (by decide), regs₄ .x21 (by decide), x21₃, ← BitVec.ofNat_add]
    unfold levelDest
    rw [if_pos rfl]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have keep₇ (r : Reg) (a : r ≠ .x21) : s₇.getReg r = s₆.getReg r := by
    simp [s₇, execInstrBr, Ne.symm a]
  -- jump to the latch
  have run₈ := runs_jal s₇ _ _ v₅ pc₇
  let s₈ := execInstrBr s₇ (.JAL .x0 (backJump (tripleExitWord v) 104))
  obtain ⟨jpc₈, jmem₈, jkeep₈⟩ := jal_post s₇ (backJump (tripleExitWord v) 104)
  have x25e : (triplePrep.foldl execInstrBr state).getReg .x25 = BitVec.ofNat 64 v := p25
  have shape : tripleRun state = s₈ := by
    simp only [tripleRun, x25e, word_lt v (by omega)]
    rfl
  have keepAll (r : Reg) (a : r ≠ .x7) (b : r ≠ .x10) (c : r ≠ .x11) (d : r ≠ .x24) (e : r ≠ .x25)
      (f : r ≠ .x27) (g : r ≠ .x30) (h : r ≠ .x31) (l : r ≠ .x21) : (tripleRun state).getReg r = state.getReg r := by
    rw [shape, jkeep₈, keep₇ r l, regs₆ r h, regs₅ r h, regs₄ r h, keep₃ r b g, keep₂, pkeep r a b c d e f g]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [shape]
    exact (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans (run₆.trans (run₇.trans run₈))))))).cast
      (by simp [triple_prep_length, tripleLui])
      (by simp [cost, triplePrep, tripleLui, instructionCycles])
  · rw [shape, jpc₈, pc₇]
    exact triple_exit_target v hv
  · rw [shape, jkeep₈, keep₇ _ (by decide), regs₆ _ (by decide), regs₅ _ (by decide), regs₄ _ (by decide),
      keep₃ _ (by decide) (by decide), keep₂]
    have e : nodeReg 7 = .x24 := rfl
    rw [e, p24]
    congr 1
    exact e7.symm
  · rw [shape, jkeep₈]
    exact x21₇
  · exact (keepAll .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.heap
  · exact (keepAll .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.five
  · exact (keepAll .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.width
  · intro j hj
    have frame : baseReg j ≠ .x7 ∧ baseReg j ≠ .x10 ∧ baseReg j ≠ .x11 ∧ baseReg j ≠ .x24 ∧ baseReg j ≠ .x25 ∧
        baseReg j ≠ .x27 ∧ baseReg j ≠ .x30 ∧ baseReg j ≠ .x31 ∧ baseReg j ≠ .x21 := by
      unfold baseReg; split <;> decide
    obtain ⟨a, b, c, d, e, f, g, h, l⟩ := frame
    exact (keepAll (baseReg j) a b c d e f g h l).trans (at_.bases j hj)
  · intro j hj
    have frame : tableReg j ≠ .x7 ∧ tableReg j ≠ .x10 ∧ tableReg j ≠ .x11 ∧ tableReg j ≠ .x24 ∧
        tableReg j ≠ .x25 ∧ tableReg j ≠ .x27 ∧ tableReg j ≠ .x30 ∧ tableReg j ≠ .x31 ∧ tableReg j ≠ .x21 := by
      unfold tableReg; split <;> decide
    obtain ⟨a, b, c, d, e, f, g, h, l⟩ := frame
    exact (keepAll (tableReg j) a b c d e f g h l).trans (at_.tables j hj)
  · rw [shape]
    have mem : s₈.mem = s₆.mem := by rw [jmem₈, pure_mem _ _ advPure]
    exact (inv₆.of_mem mem).cast_count (by unfold levelWord; omega)
  · intro r z _ a b c l d e g h
    exact keepAll r a b c d e z g h l

end TwoPermutationPrototype.QuadOpening
