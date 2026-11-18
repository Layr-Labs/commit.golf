import CommitGolfCandidate.TwoPermutationPackedUnpackSteps
import CommitGolfCandidate.TwoPermutationCollectInput
import CommitGolfCandidate.ProofCodec

/-! The unpacking wrapper's length checks (words 1 and 377-402). -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

@[simp] theorem se12_0 : (signExtend12 0).toNat = 0 := rfl
@[simp] theorem se12_1 : (signExtend12 1).toNat = 1 := rfl
@[simp] theorem se12_3 : (signExtend12 3).toNat = 3 := rfl
@[simp] theorem se12_15 : (signExtend12 15).toNat = 15 := rfl
@[simp] theorem se12_29 : (signExtend12 29).toNat = 29 := rfl
@[simp] theorem se12_30 : (signExtend12 30).toNat = 30 := rfl
@[simp] theorem se12_48 : (signExtend12 48).toNat = 48 := rfl
@[simp] theorem se12_63 : (signExtend12 63).toNat = 63 := rfl
@[simp] theorem se12_119 : (signExtend12 119).toNat = 119 := rfl
@[simp] theorem se12_483 : (signExtend12 483).toNat = 483 := rfl
@[simp] theorem se12_498 : (signExtend12 498).toNat = 498 := rfl
@[simp] theorem se12_m1 : (signExtend12 4095).toNat = 2^64-1 := rfl
@[simp] theorem se12_m48 : (signExtend12 4048).toNat = 2^64-48 := rfl
@[simp] theorem sh_2 : (2 : BitVec 6).toNat = 2 := rfl
@[simp] theorem sh_8 : (8 : BitVec 6).toNat = 8 := rfl
@[simp] theorem sh_16 : (16 : BitVec 6).toNat = 16 := rfl
@[simp] theorem sh_33 : (33 : BitVec 6).toNat = 33 := rfl

def proofBase : Nat := 10334769248
def scratchBase : Nat := 10334769248 + 2^33

def unpackStart (input : CheckInput) : MachineState :=
  execInstrBr (Assembly.submission.initialState .check input) (.ADDI .x6 .x0 498)

/-- Register values at the wrapper's entry. -/
def startView (input : CheckInput) : Reg → Nat := fun r => ((unpackStart input).getReg r).toNat

theorem start_view (input : CheckInput) : View (unpackStart input) (startView input) := fun _ => rfl

theorem start_pc (input : CheckInput) : (unpackStart input).pc = 4100 := rfl

def unpackTemps : List Reg :=
  [.x5,.x7,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]

theorem start_temps (input : CheckInput) : ∀ r ∈ unpackTemps, startView input r = 0 := by
  intro r hr
  simp only [unpackTemps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem start_x0 (input : CheckInput) : startView input .x0 = 0 := rfl
theorem start_x15 (input : CheckInput) : startView input .x15 = proofBase := rfl
theorem start_x16 (input : CheckInput) : startView input .x16 = input.positions.card := by
  have := checker_positions_bound input
  change (BitVec.ofNat 64 input.positions.card).toNat = _
  rw [BitVec.toNat_ofNat]; omega
theorem start_x17 (input : CheckInput) (fits : input.proof.length < 2^64) :
    startView input .x17 = input.proof.length := by
  change (BitVec.ofNat 64 input.proof.length).toNat = _
  rw [BitVec.toNat_ofNat]; omega

theorem sub_mod64 (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    (18446744073709551616 - b + a) % 18446744073709551616 = a - b := by omega

/-- Rewrite `% 2^64` away wherever `omega` proves the operand is small. -/
macro "vmod" : tactic => `(tactic| try simp (disch := omega) only [Nat.mod_eq_of_lt, sub_mod64])

macro "vsimp" : tactic => `(tactic| ((repeat rw [List.foldl_cons]); (try rw [List.foldl_nil]); simp only [stepV, setV, aluDest, aluVal,
  ne_eq, reduceCtorEq, not_false_eq_true, and_true, and_false, ite_true, ite_false,
  se12_0, se12_1, se12_3, se12_15, se12_29, se12_30, se12_48, se12_63, se12_119, se12_483,
  se12_498, se12_m1, se12_m48, sh_2, sh_8, sh_16, sh_33, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
  true_and, false_and, Nat.zero_add, Nat.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd,
  Nat.reduceMul, Nat.reduceDiv]))

macro "vnorm" : tactic => `(tactic| try simp only [Nat.zero_add, Nat.add_zero, Nat.reduceMod, Nat.reducePow,
  Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceEqDiff, reduceIte])

/-! ### The jump and the guards -/

theorem jump_hop (input : CheckInput) :
    Hop (unpackStart input) ((unpackStart input).setPC (BitVec.ofNat 64 (4096+4*377))) 1 1 := by
  have h := hop_one (unpackStart input) 1 (.JAL .x0 1504) (by decide) (start_pc input) rfl
    (branch_ordinary _ _ rfl)
  rw [jal0_exec, start_pc] at h
  exact h

/-- The common shape of the four length guards: a branch to the reject block at word 364. -/
theorem guard_hop (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (a b : Reg)
    (off : BitVec 13) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.BLTU a b off)))
    (target : BitVec.ofNat 64 (4096+4*index) + signExtend13 off = 0x15b0) :
    Hop s (s.setPC (if v a < v b then 0x15b0 else BitVec.ofNat 64 (4096+4*(index+1)))) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [bltu_exec s v hv, pc, target, pc_next] at h
  exact h


theorem bne_hop (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (a b : Reg)
    (off : BitVec 13) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.BNE a b off)))
    (target : BitVec.ofNat 64 (4096+4*index) + signExtend13 off = 0x15b0) :
    Hop s (s.setPC (if v a = v b then BitVec.ofNat 64 (4096+4*(index+1)) else 0x15b0)) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [bne_exec s v hv, pc, target, pc_next] at h
  exact h

theorem foldl_stepV_other (is : List Instr) (v : Reg → Nat) (r : Reg)
    (h : ∀ i ∈ is, aluDest i ≠ r) : is.foldl stepV v r = v r := by
  induction is generalizing v with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, ih _ (fun j hj => h j (by simp [hj]))]
    have := h i (by simp)
    simp only [stepV, setV]
    rw [if_neg (fun h' => this h'.1.symm)]

theorem foldl_stepV_notin (is : List Instr) (v : Reg → Nat) (r : Reg)
    (h : r ∉ is.map aluDest) : is.foldl stepV v r = v r :=
  foldl_stepV_other is v r (fun i hi e => h (e ▸ List.mem_map_of_mem hi))

def prefixBlock1 : List Instr := [.ADDI .x5 .x0 1, .SLLI .x5 .x5 33]
def prefixBlock2 : List Instr := [.ADDI .x7 .x0 48, .MUL .x7 .x16 .x7]
def prefixBlock3 : List Instr :=
  [.SUB .x8 .x17 .x7, .SLLI .x8 .x8 2, .ADDI .x9 .x0 119, .DIVU .x8 .x8 .x9, .ADDI .x9 .x0 15,
   .MUL .x9 .x16 .x9]
def prefixBlock4 : List Instr :=
  [.ADDI .x18 .x0 29, .MUL .x18 .x8 .x18, .ADD .x18 .x18 .x7, .ADDI .x19 .x8 3, .SRLI .x19 .x19 2,
   .ADDI .x20 .x0 3, .MUL .x19 .x19 .x20, .ADD .x19 .x19 .x18]
def prefixBlock5 : List Instr := [.ADDI .x21 .x0 1, .SLLI .x21 .x21 33, .ADD .x21 .x21 .x15, .ADDI .x22 .x0 0]

def prefixWrites : List Reg := [.x5,.x7,.x8,.x9,.x18,.x19,.x20,.x21,.x22]

/-- Registers at the decode loop entry. -/
structure PrefixView (input : CheckInput) (v : Reg → Nat) : Prop where
  x0 : v .x0 = 0
  x7 : v .x7 = 48*input.positions.card
  x8 : v .x8 = packedCount input.positions.card input.proof.length
  x15 : v .x15 = proofBase
  x16 : v .x16 = input.positions.card
  x17 : v .x17 = input.proof.length
  x18 : v .x18 = bodyLength input.positions.card (packedCount input.positions.card input.proof.length)
  x21 : v .x21 = scratchBase
  x22 : v .x22 = 0
  other : ∀ r, r ∉ prefixWrites → v r = startView input r

theorem view_x0 {s : MachineState} {v : Reg → Nat} (h : View s v) : v .x0 = 0 := (h .x0).symm

theorem b1_x5 (v : Reg → Nat) (h0 : v .x0 = 0) : prefixBlock1.foldl stepV v .x5 = 2^33 := by
  simp only [prefixBlock1]; vsimp; rw [h0]

theorem b2_x7 (v : Reg → Nat) (k : Nat) (h0 : v .x0 = 0) (h16 : v .x16 = k) (kb : k ≤ 2^24) :
    prefixBlock2.foldl stepV v .x7 = 48*k := by
  simp only [prefixBlock2]; vsimp; rw [h0, h16]; vnorm; omega

theorem b3_x8 (v : Reg → Nat) (k L : Nat) (h0 : v .x0 = 0) (h7 : v .x7 = 48*k) (h17 : v .x17 = L)
    (kb : k ≤ 2^24) (le : 48*k ≤ L) (lb : L ≤ 2^33) :
    prefixBlock3.foldl stepV v .x8 = packedCount k L := by
  simp only [prefixBlock3]; vsimp; rw [h7, h17, h0]; vnorm; unfold packedCount; omega

theorem b3_x9 (v : Reg → Nat) (k : Nat) (h0 : v .x0 = 0) (h16 : v .x16 = k) (kb : k ≤ 2^24) :
    prefixBlock3.foldl stepV v .x9 = 15*k := by
  simp only [prefixBlock3]; vsimp; rw [h16, h0]; vnorm; omega

theorem b4_x18 (v : Reg → Nat) (k n : Nat) (h0 : v .x0 = 0) (h7 : v .x7 = 48*k) (h8 : v .x8 = n)
    (kb : k ≤ 2^24) (nb : n ≤ 2^33) :
    prefixBlock4.foldl stepV v .x18 = bodyLength k n := by
  simp only [prefixBlock4]; vsimp; rw [h8, h7, h0]; vnorm; simp only [bodyLength]; omega

theorem b4_x19 (v : Reg → Nat) (k n : Nat) (h0 : v .x0 = 0) (h7 : v .x7 = 48*k) (h8 : v .x8 = n)
    (kb : k ≤ 2^24) (nb : n ≤ 2^33) :
    prefixBlock4.foldl stepV v .x19 = packedLength k n := by
  simp only [prefixBlock4]; vsimp; rw [h8, h7, h0]; vnorm; simp only [packedLength, bodyLength]
  have e1 : (n + 3) % 18446744073709551616 = n + 3 := Nat.mod_eq_of_lt (by omega)
  have e2 : n * 29 % 18446744073709551616 = n * 29 := Nat.mod_eq_of_lt (by omega)
  have e3 : (n * 29 + 48 * k) % 18446744073709551616 = n * 29 + 48 * k := Nat.mod_eq_of_lt (by omega)
  have e4 : (n + 3) / 4 * 3 % 18446744073709551616 = (n + 3) / 4 * 3 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, e4]; omega

theorem b5_x21 (v : Reg → Nat) (h0 : v .x0 = 0) (h15 : v .x15 = proofBase) :
    prefixBlock5.foldl stepV v .x21 = scratchBase := by
  simp only [prefixBlock5]; vsimp; rw [h0, h15]; vnorm; unfold scratchBase proofBase; omega

theorem b5_x22 (v : Reg → Nat) (h0 : v .x0 = 0) : prefixBlock5.foldl stepV v .x22 = 0 := by
  simp only [prefixBlock5]; vsimp; rw [h0]

theorem prefix_run (input : CheckInput) (fits : input.proof.length ≤ 8355061248) :
    (¬ WellFormed input.positions.card input.proof.length →
      ∃ t steps cycles, steps ≤ 27 ∧ Hop (unpackStart input) t steps cycles ∧ t.pc = 0x15b0) ∧
    (WellFormed input.positions.card input.proof.length →
      ∃ t v, Hop (unpackStart input) t 27 42 ∧ View t v ∧ t.pc = BitVec.ofNat 64 (4096+4*403) ∧
        t.mem = (unpackStart input).mem ∧ PrefixView input v) := by
  have kb := checker_positions_bound input
  generalize hk : input.positions.card = k at kb
  generalize hL : input.proof.length = L at fits
  have v0 := start_view input
  have z0 := start_x0 input
  have z15 := start_x15 input
  have z16 : startView input .x16 = k := hk ▸ start_x16 input
  have z17 : startView input .x17 = L := hL ▸ start_x17 input (by omega)
  -- jump
  have j := jump_hop input
  have vj := view_pc_only _ _ (BitVec.ofNat 64 (4096+4*377)) v0
  -- block 1
  obtain ⟨h1, w1, p1, m1⟩ := block_run _ 377 prefixBlock1 _ vj (by decide) rfl
    (by intro j hj; simp only [prefixBlock1, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hs1 : prefixBlock1.foldl execInstrBr ((unpackStart input).setPC (BitVec.ofNat 64 (4096+4*377))) = s1 at h1 w1 p1 m1
  generalize hv1 : prefixBlock1.foldl stepV (startView input) = v1 at w1
  have e1x5 : v1 .x5 = 2^33 := hv1 ▸ b1_x5 _ z0
  have e1x17 : v1 .x17 = L := by rw [← hv1, foldl_stepV_notin _ _ _ (by decide)]; exact z17
  have e1x16 : v1 .x16 = k := by rw [← hv1, foldl_stepV_notin _ _ _ (by decide)]; exact z16
  have e1x15 : v1 .x15 = proofBase := by rw [← hv1, foldl_stepV_notin _ _ _ (by decide)]; exact z15
  have g1 := guard_hop s1 v1 w1 379 .x5 .x17 8132 (by decide) p1 rfl rfl
  rw [e1x5, e1x17] at g1
  by_cases r1 : 2^33 < L
  · have nwf : ¬ WellFormed k L := fun w => by unfold WellFormed at w; omega
    refine ⟨fun _ => ⟨_, 4, 4, by omega, (j.thenDo h1).thenDo g1, ?_⟩, fun w => (nwf w).elim⟩
    rw [if_pos r1]; rfl
  rw [if_neg r1] at g1
  have q1 := view_pc_only s1 v1 (BitVec.ofNat 64 (4096+4*(379+1))) w1
  -- block 2
  obtain ⟨h2, w2, p2, m2⟩ := block_run _ 380 prefixBlock2 _ q1 (by decide) rfl
    (by intro j hj; simp only [prefixBlock2, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hs2 : prefixBlock2.foldl execInstrBr (s1.setPC (BitVec.ofNat 64 (4096+4*(379+1)))) = s2 at h2 w2 p2 m2
  generalize hv2 : prefixBlock2.foldl stepV v1 = v2 at w2
  have x01 := view_x0 w1
  have e2x7 : v2 .x7 = 48*k := hv2 ▸ b2_x7 _ _ x01 e1x16 kb
  have e2x17 : v2 .x17 = L := by rw [← hv2, foldl_stepV_notin _ _ _ (by decide)]; exact e1x17
  have e2x16 : v2 .x16 = k := by rw [← hv2, foldl_stepV_notin _ _ _ (by decide)]; exact e1x16
  have e2x15 : v2 .x15 = proofBase := by rw [← hv2, foldl_stepV_notin _ _ _ (by decide)]; exact e1x15
  have g2 := guard_hop s2 v2 w2 382 .x17 .x7 8120 (by decide) p2 rfl rfl
  rw [e2x7, e2x17] at g2
  by_cases r2 : L < 48*k
  · have nwf : ¬ WellFormed k L := fun w => by unfold WellFormed at w; omega
    refine ⟨fun _ => ⟨_, 7, 10, by omega, (((j.thenDo h1).thenDo g1).thenDo h2).thenDo g2, ?_⟩,
      fun w => (nwf w).elim⟩
    rw [if_pos r2]; rfl
  rw [if_neg r2] at g2
  have q2 := view_pc_only s2 v2 (BitVec.ofNat 64 (4096+4*(382+1))) w2
  -- block 3
  obtain ⟨h3, w3, p3, m3⟩ := block_run _ 383 prefixBlock3 _ q2 (by decide) rfl
    (by intro j hj; simp only [prefixBlock3, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hs3 : prefixBlock3.foldl execInstrBr (s2.setPC (BitVec.ofNat 64 (4096+4*(382+1)))) = s3 at h3 w3 p3 m3
  generalize hv3 : prefixBlock3.foldl stepV v2 = v3 at w3
  have x02 := view_x0 w2
  have e3x8 : v3 .x8 = packedCount k L := hv3 ▸ b3_x8 _ _ _ x02 e2x7 e2x17 kb (by omega) (by omega)
  have e3x9 : v3 .x9 = 15*k := hv3 ▸ b3_x9 _ _ x02 e2x16 kb
  have e3x7 : v3 .x7 = 48*k := by rw [← hv3, foldl_stepV_notin _ _ _ (by decide)]; exact e2x7
  have e3x17 : v3 .x17 = L := by rw [← hv3, foldl_stepV_notin _ _ _ (by decide)]; exact e2x17
  have e3x16 : v3 .x16 = k := by rw [← hv3, foldl_stepV_notin _ _ _ (by decide)]; exact e2x16
  have e3x15 : v3 .x15 = proofBase := by rw [← hv3, foldl_stepV_notin _ _ _ (by decide)]; exact e2x15
  have g3 := guard_hop s3 v3 w3 389 .x8 .x9 8092 (by decide) p3 rfl rfl
  rw [e3x8, e3x9] at g3
  by_cases r3 : packedCount k L < 15*k
  · have nwf : ¬ WellFormed k L := fun w => by unfold WellFormed at w; omega
    refine ⟨fun _ => ⟨_, 14, 23, by omega,
      (((((j.thenDo h1).thenDo g1).thenDo h2).thenDo g2).thenDo h3).thenDo g3, ?_⟩,
      fun w => (nwf w).elim⟩
    rw [if_pos r3]; rfl
  rw [if_neg r3] at g3
  have q3 := view_pc_only s3 v3 (BitVec.ofNat 64 (4096+4*(389+1))) w3
  -- block 4
  obtain ⟨h4, w4, p4, m4⟩ := block_run _ 390 prefixBlock4 _ q3 (by decide) rfl
    (by intro j hj; simp only [prefixBlock4, List.length] at hj; interval_cases j <;> rfl) rfl
  generalize hs4 : prefixBlock4.foldl execInstrBr (s3.setPC (BitVec.ofNat 64 (4096+4*(389+1)))) = s4 at h4 w4 p4 m4
  generalize hv4 : prefixBlock4.foldl stepV v3 = v4 at w4
  have x03 := view_x0 w3
  have cnt : packedCount k L ≤ 2^33 := by unfold packedCount; omega
  have e4x18 : v4 .x18 = bodyLength k (packedCount k L) := hv4 ▸ b4_x18 _ _ _ x03 e3x7 e3x8 kb cnt
  have e4x19 : v4 .x19 = packedLength k (packedCount k L) := hv4 ▸ b4_x19 _ _ _ x03 e3x7 e3x8 kb cnt
  have e4x17 : v4 .x17 = L := by rw [← hv4, foldl_stepV_notin _ _ _ (by decide)]; exact e3x17
  have e4x16 : v4 .x16 = k := by rw [← hv4, foldl_stepV_notin _ _ _ (by decide)]; exact e3x16
  have e4x15 : v4 .x15 = proofBase := by rw [← hv4, foldl_stepV_notin _ _ _ (by decide)]; exact e3x15
  have e4x8 : v4 .x8 = packedCount k L := by rw [← hv4, foldl_stepV_notin _ _ _ (by decide)]; exact e3x8
  have e4x7 : v4 .x7 = 48*k := by rw [← hv4, foldl_stepV_notin _ _ _ (by decide)]; exact e3x7
  have g4 := bne_hop s4 v4 w4 398 .x19 .x17 8056 (by decide) p4 rfl rfl
  rw [e4x19, e4x17] at g4
  by_cases r4 : packedLength k (packedCount k L) = L
  swap
  · have nwf : ¬ WellFormed k L := fun w => r4 (w.2.2.2.symm)
    refine ⟨fun _ => ⟨_, 23, 38, by omega,
      (((((((j.thenDo h1).thenDo g1).thenDo h2).thenDo g2).thenDo h3).thenDo g3).thenDo h4).thenDo g4,
      ?_⟩, fun w => (nwf w).elim⟩
    rw [if_neg r4]; rfl
  have wf : WellFormed k L := ⟨by omega, by omega, by omega, r4.symm⟩
  refine ⟨fun h => (h wf).elim, fun _ => ?_⟩
  rw [if_pos r4] at g4
  have q4 := view_pc_only s4 v4 (BitVec.ofNat 64 (4096+4*(398+1))) w4
  obtain ⟨h5, w5, p5, m5⟩ := block_run _ 399 prefixBlock5 _ q4 (by decide) rfl
    (by intro j hj; simp only [prefixBlock5, List.length] at hj; interval_cases j <;> rfl) rfl
  have x04 := view_x0 w4
  refine ⟨_, _, ((((((((j.thenDo h1).thenDo g1).thenDo h2).thenDo g2).thenDo h3).thenDo g3).thenDo h4).thenDo
    g4).thenDo h5, w5, p5, ?_, ?_⟩
  · rw [m5]; change s4.mem = _; rw [m4]; change s3.mem = _; rw [m3]; change s2.mem = _
    rw [m2]; change s1.mem = _; rw [m1]; rfl
  have other : ∀ r, r ∉ prefixWrites → v4 r = startView input r := by
    intro r hr
    simp only [prefixWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hv4, ← hv3, ← hv2, ← hv1]
    repeat rw [foldl_stepV_notin _ _ r (by
      simp only [prefixBlock1, prefixBlock2, prefixBlock3, prefixBlock4, List.map, aluDest,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      tauto)]
  constructor <;> (try simp only [hk, hL])
  · exact view_x0 w5
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x7
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x8
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x15
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x16
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x17
  · rw [foldl_stepV_notin _ _ _ (by decide)]; exact e4x18
  · exact b5_x21 _ x04 e4x15
  · exact b5_x22 _ x04
  · intro r hr
    have hr' := hr
    simp only [prefixWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [foldl_stepV_notin _ _ r (by
      simp only [prefixBlock5, List.map, aluDest, List.mem_cons, List.not_mem_nil, or_false, not_or]
      tauto)]
    exact other r hr


end TwoPermutationPrototype.Packed.Checker
