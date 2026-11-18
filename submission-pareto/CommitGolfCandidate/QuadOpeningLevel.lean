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

/-- Initial address of doubleword `d < 178` of the record of position `i`. -/
def recordSource (i d : Nat) : Nat :=
  if d < 2 then nonceBase+16*i+8*d
  else trapdoorBase+pentaSlotOffset ((d-2)/16) (neighbourNat i ((d-2)/16) ((d-2)%16/4))+8*((d-2)%4)

/-- The position written by record `o` (0 past the end). -/
def ordinalIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

def wordSource (positions : Positions) (u : Nat) : Nat := recordSource (ordinalIndex positions (u/178)) (u%178)

theorem word_source_level (positions : Positions) (o k j w : Nat) (hk : k < 11) (hj : j < 4) (hw : w < 4) :
    wordSource positions (178*o+2+16*k+4*j+w) =
      trapdoorBase+pentaSlotOffset k (neighbourNat (ordinalIndex positions o) k j)+8*w := by
  unfold wordSource recordSource
  have q : (178*o+2+16*k+4*j+w)/178 = o := by omega
  have r : (178*o+2+16*k+4*j+w)%178 = 2+16*k+4*j+w := by omega
  rw [q, r, if_neg (by omega)]
  have a : (2+16*k+4*j+w-2)/16 = k := by omega
  have b : (2+16*k+4*j+w-2)%16/4 = j := by omega
  have c : (2+16*k+4*j+w-2)%4 = w := by omega
  rw [a, b, c]

theorem word_source_salt (positions : Positions) (o w : Nat) (hw : w < 2) :
    wordSource positions (178*o+w) = nonceBase+16*ordinalIndex positions o+8*w := by
  unfold wordSource recordSource
  have q : (178*o+w)/178 = o := by omega
  have r : (178*o+w)%178 = w := by omega
  rw [q, r, if_pos hw]

theorem div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i/5^k < pentaCount k
  | 0 => by simpa [pentaCount] using inside
  | k+1 => by
    have ih := div_lt_count i inside k
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    show i/5^k/5 < (pentaCount k+4)/5
    omega

private theorem group_room : ∀ k < 11, pentaGroupBase k+368*pentaCount (k+1) ≤ 1543577600 := by decide
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

theorem level_head_post (state : MachineState) (k n : Nat) (hk : k < 11) (small : n < 2^30)
    (node : state.getReg .x6 = BitVec.ofNat 64 n) (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (width : state.getReg .x23 = BitVec.ofNat 64 368) (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase) :
    let after := (levelHead k).foldl execInstrBr state
    after.getReg .x24 = BitVec.ofNat 64 (n/5) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%5) ∧
      after.getReg .x30 = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40+368*(n/5)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 → after.getReg r = state.getReg r := by
  intro after
  have quotient := divu_five n (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [after, levelHead, execInstrBr, node, five, quotient]
  · simp [after, levelHead, execInstrBr, node, five, quotient]
    exact rem_by_shift n (by omega)
  · simp [after, levelHead, execInstrBr, node, five, quotient, width, heap, lui_page k hk]
    rw [mul_width _ (by omega), ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  · intro r a b c d e
    simp [after, levelHead, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e]

theorem neighbour_head_post (state : MachineState) (j r G : Nat) (hj : j < 4) (hr : r < 5) (hG : G < 2^40)
    (rest : state.getReg .x25 = BitVec.ofNat 64 r) (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (group : state.getReg .x30 = BitVec.ofNat 64 G) :
    let after := (neighbourHead j).foldl execInstrBr state
    after.getReg .x7 = BitVec.ofNat 64 (G+32*((r+j+1)%5)) ∧
      ∀ reg, reg ≠ .x7 → after.getReg reg = state.getReg reg := by
  intro after
  refine ⟨?_, ?_⟩
  · have sum : state.getReg .x25 + signExtend12 (BitVec.ofNat 12 (j+1)) = BitVec.ofNat 64 (r+j+1) := by
      rw [rest, addi_small j hj, ← BitVec.ofNat_add, Nat.add_assoc]
    simp [after, neighbourHead, execInstrBr, sum, five, group]
    rw [remu_five _ (by omega), shift_slot _ (by omega), ← BitVec.ofNat_add]
  · intro reg a
    simp [after, neighbourHead, execInstrBr, Ne.symm a]

/-! ### One level -/

def levelStart (k : Nat) : Nat := 18+61*k

/-- Output doubleword index at which level `k` of record `o` starts. -/
def levelWord (o k : Nat) : Nat := 178*o+2+16*k

set_option maxRecDepth 100000 in
theorem head_code : ∀ k < 11, CodeAt (levelStart k) (levelHead k) := by decide +kernel
set_option maxRecDepth 100000 in
theorem neighbour_head_code : ∀ k < 11, ∀ j < 4, CodeAt (levelStart k+8+13*j) (neighbourHead j) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem neighbour_pair_code : ∀ k < 11, ∀ j < 4, CodeAt (levelStart k+8+13*j+4) (pairCode 4) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem neighbour_tail_code : ∀ k < 11, ∀ j < 4, CodeAt (levelStart k+8+13*j+12) [.ADDI .x21 .x21 32] := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem level_tail_code : ∀ k < 11, CodeAt (levelStart k+60) [.ADDI .x6 .x24 0] := by decide +kernel

theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

structure LevelAt (init state : MachineState) (positions : Positions) (o k : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*levelStart k)
  node : state.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o / 5^k)
  dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*levelWord o k)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  five : state.getReg .x19 = BitVec.ofNat 64 5
  width : state.getReg .x23 = BitVec.ofNat 64 368
  inv : Inv init state (wordSource positions) (levelWord o k)

theorem neighbour_block (init state : MachineState) (positions : Positions) (o k j : Nat)
    (hk : k < 11) (hj : j < 4) (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8+13*j)))
    (rest : state.getReg .x25 = BitVec.ofNat 64 (ordinalIndex positions o / 5^k % 5))
    (group : state.getReg .x30 =
      BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40+368*(ordinalIndex positions o / 5^k / 5)))
    (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(levelWord o k+4*j)))
    (inv : Inv init state (wordSource positions) (levelWord o k+4*j)) :
    let after := (neighbourCode j).foldl execInstrBr state
    Runs state after 13 16 ∧ after.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8+13*(j+1))) ∧
      after.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(levelWord o k+4*(j+1))) ∧
      Inv init after (wordSource positions) (levelWord o k+4*(j+1)) ∧
      ∀ r, r ≠ .x7 → r ≠ .x21 → r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  let i := ordinalIndex positions o
  let start := levelStart k+8+13*j
  have source := neighbour_source i k j inside hk hj
  have small : i < 2^24 := inside
  have quotient : i/5^k/5 < 2^24 := by
    have := Nat.div_le_self (i/5^k) 5; have := Nat.div_le_self i (5^k); omega
  let S := trapdoorBase+pentaSlotOffset k (neighbourNat i k j)
  let s₁ := (neighbourHead j).foldl execInstrBr state
  have headPure : (neighbourHead j).all pureOp = true := by simp [neighbourHead, pureOp]
  have run₁ := runs_pure (neighbourHead j) start state (neighbour_head_code k hk j hj) pc headPure
  have post₁ := neighbour_head_post state j (i/5^k%5) (trapdoorBase+pentaGroupBase k+40+368*(i/5^k/5))
    hj (Nat.mod_lt _ (by decide)) (by
      have := group_room k hk; have : trapdoorBase = 4294971424 := rfl
      have := div_lt_count i inside (k+1)
      omega) rest five group
  have source₁ : s₁.getReg .x7 = BitVec.ofNat 64 S := by
    rw [post₁.1]
    show _ = BitVec.ofNat 64 (trapdoorBase+pentaSlotOffset k (neighbourNat i k j))
    rw [source.1]
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(start+4)) := by
    rw [pure_pc _ _ headPure, pc]
    exact pc_offset start 4
  have dest₁ : s₁.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(levelWord o k+4*j)) :=
    (post₁.2 .x21 (by decide)).trans dest
  have inv₁ : Inv init s₁ (wordSource positions) (levelWord o k+4*j) := inv.of_mem (pure_mem _ _ headPure)
  have fitsAll : proofBase+8*(178*(o+1)) ≤ MEMORY_BYTES := by
    have : proofBase = 10804535392 := rfl
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have block := pair_block init (wordSource positions) (start+4) 4 S
    (proofBase+8*(levelWord o k+4*j)) (levelWord o k+4*j) le_rfl
    (neighbour_pair_code k hk j hj) source.2.1 (by omega) (by omega) rfl
    (by unfold levelWord; omega)
    (fun w hw => by
      have := word_source_level positions o k j w hk hj hw
      unfold levelWord
      exact this)
    4 le_rfl s₁ pc₁ source₁ dest₁ inv₁
  obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := block
  let s₂ := (pairCode 4).foldl execInstrBr s₁
  have tailPure : ([.ADDI .x21 .x21 32] : List Instr).all pureOp = true := rfl
  have run₃ := runs_pure [.ADDI .x21 .x21 32] (start+12) s₂ (neighbour_tail_code k hk j hj) pc₂ tailPure
  have shape : after = [.ADDI .x21 .x21 32].foldl execInstrBr s₂ := by
    simp only [after, s₂, s₁, neighbourCode, List.foldl_append]
  rw [shape]
  refine ⟨(run₁.trans (run₂.trans run₃)).cast (by simp [neighbourHead]) (by
      simp [cost, neighbourHead, instructionCycles]), ?_, ?_, ?_, ?_⟩
  · rw [pure_pc _ _ tailPure, pc₂, pc_offset]
    congr 2
  · have keep : s₂.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(levelWord o k+4*j)) :=
      (regs₂ .x21 (by decide)).trans dest₁
    simp [execInstrBr, keep, signExtend12]
    rw [← BitVec.ofNat_add]
    congr 1
  · exact (inv₂.of_mem (pure_mem _ _ tailPure)).cast_count (by omega)
  · intro r a b c
    simp [execInstrBr, Ne.symm b]
    rw [regs₂ r c, post₁.2 r a]

end TwoPermutationPrototype.QuadOpening
