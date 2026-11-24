import CommitGolfCandidate.TwoPermutationPackedSearchClimb
import CommitGolfCandidate.TwoPermutationPackedCapRootRun

/-! # One-byte search: the trial's root compare (1202..1213), accept (1214..1216) and next (1217..1220) -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt write_bits_word_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

attribute [local irreducible] execute

@[local simp] private theorem search_reg_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl
@[local simp] private theorem search_sext_zero : signExtend12 (0#12) = 0#64 := by decide
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem pc_after (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl
private theorem getMem_pc (s : MachineState) (p a : Word) : (s.setPC p).getMem a=s.getMem a := rfl
private theorem getMem_reg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getMem a=s.getMem a := by
  cases r <;> rfl
attribute [local simp] getMem_pc getMem_reg

private theorem reg_setReg (s : MachineState) (rd rs : Reg) (v : Word) :
    (s.setReg rd v).getReg rs = if rd = rs ∧ rd ≠ .x0 then v else s.getReg rs :=
  Opening.getReg_setReg s rd rs v

/-! ### The trial's root compare (1202..1213), accept (1214..1216) and next (1217..1220) -/

def searchCompareCode (i : Fin 4) : List Instr :=
  [.LD .x29 .x25 (BitVec.ofNat 12 (32+8*i.val)),
   .LD .x30 .x9 (BitVec.ofNat 12 (8*i.val)),
   .BNE .x29 .x30 (BitVec.ofNat 13 (52-12*i.val))]

def searchCompare (s : MachineState) (i : Fin 4) : MachineState := (searchCompareCode i).foldl execInstrBr s

theorem search_compare_code (i : Fin 4) (j : Nat) (small : j < 3) :
    (packedImage.code[1202+3*i.val+j]?).bind decodeInstruction = some (.base ((searchCompareCode i)[j]?.getD .EBREAK)) := by
  fin_cases i <;> interval_cases j <;> rfl

theorem execute_search_compare (s : MachineState) (i : Fin 4)
    (pc : s.pc = spc (1202+3*i.val))
    (cap : accessValid (s.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true)
    (claim : accessValid (s.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true) :
    Hop s (searchCompare s i) 3 3 := by
  intro fuel
  apply execute_unit_steps (states := fun j => ((searchCompareCode i).take j).foldl execInstrBr s)
  intro j bounded
  refine ⟨.base ((searchCompareCode i)[j]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply wide_image_fetch _ _ (1202+3*i.val+j) _ (by omega)
    · fin_cases i <;> interval_cases j <;>
        simp [searchCompareCode, execInstrBr, pc, spc, MachineState.setPC]
    · exact search_compare_code i j bounded
  · fin_cases i <;> interval_cases j <;>
      simp_all [searchCompareCode, execInstrBr, ordinaryStep, memoryArgumentsValid, memAccess, signExtend12]
  · interval_cases j <;> rfl

theorem search_compare_post (s : MachineState) (i : Fin 4) (pc : s.pc = spc (1202+3*i.val)) :
    let t := searchCompare s i
    t.pc = (if rootWordMatches s i then spc (1205+3*i.val) else spc 1217) ∧
      t.mem = s.mem ∧ ∀ r : Reg, r ≠ .x29 → r ≠ .x30 → t.getReg r = s.getReg r := by
  dsimp only
  simp only [searchCompare, searchCompareCode, List.foldl_cons, List.foldl_nil, bne_pc,
    (branch_reg _ _ _ _ _).1, (branch_mem _ _ _ _).1]
  fin_cases i <;> simp [rootWordMatches, execInstrBr, signExtend12, signExtend13, pc, spc]
  all_goals first
    | (refine ⟨rfl, rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (refine ⟨rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (intro r m p; simp [Ne.symm m, Ne.symm p])

/-- The trial's compare: all four root words match (to 1214) or a mismatch (to 1217), memory unchanged. -/
theorem search_compare_scan (s : MachineState) (left : Nat) (bounded : left ≤ 4)
    (pc : s.pc = spc (1202+3*(4-left))) (roots : s.getReg .x25 = 16384#64) (claimReg : ∃ claim, claim+4 ≤ 2^33 ∧
      s.getReg .x9 = wordAddress claim) :
    ∃ (t : MachineState) (c : Nat), c ≤ 3*left ∧ Hop s t c c ∧ t.mem = s.mem ∧
      (∀ r : Reg, r ≠ .x29 → r ≠ .x30 → t.getReg r = s.getReg r) ∧
      t.pc = (if ∀ i : Fin 4, 4-left ≤ i.val → rootWordMatches s i then spc 1214 else spc 1217) := by
  induction left generalizing s with
  | zero =>
    refine ⟨s, 0, le_refl _, fun fuel => by simp [Execution.charge], rfl, fun _ _ _ => rfl, ?_⟩
    rw [if_pos (fun i h => by have := i.isLt; omega), pc]
  | succ left ih =>
    obtain ⟨claim, claimBound, claimReg⟩ := claimReg
    let i : Fin 4 := ⟨4-(left+1), by omega⟩
    let next := searchCompare s i
    have pci : s.pc = spc (1202+3*i.val) := pc
    have capV : accessValid (s.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true := by
      rw [roots, ← BitVec.ofNat_add]
      exact access_ofNat _ 8 (by unfold MEMORY_BYTES; have := i.isLt; omega) (by omega)
    have claimV : accessValid (s.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true := by
      rw [claimReg, wordAddress, ← BitVec.ofNat_add]
      exact access_ofNat _ 8 (by unfold MEMORY_BYTES; have := i.isLt; omega) (by omega)
    have hop := execute_search_compare s i pci capV claimV
    obtain ⟨npc, nmem, nregs⟩ := search_compare_post s i pci
    have stable (j : Fin 4) : rootWordMatches next j ↔ rootWordMatches s j :=
      root_word_unchanged s next nmem (nregs .x25 (by decide) (by decide)) (nregs .x9 (by decide) (by decide)) j
    by_cases same : rootWordMatches s i
    · have npc' : next.pc = spc (1202+3*(4-left)) := by
        change next.pc = _ at npc
        rw [npc, if_pos same]
        show spc (1205+3*(4-(left+1))) = _
        congr 1
        omega
      obtain ⟨t, c, cb, thop, tmem, tregs, tpc⟩ := ih next (by omega) npc'
        ((nregs .x25 (by decide) (by decide)).trans roots)
        ⟨claim, claimBound, (nregs .x9 (by decide) (by decide)).trans claimReg⟩
      refine ⟨t, 3+c, by omega, hop.thenDo thop, tmem.trans nmem, fun r a b => (tregs r a b).trans (nregs r a b), ?_⟩
      rw [tpc]
      have iff : (∀ j : Fin 4, 4-left ≤ j.val → rootWordMatches next j) ↔
          (∀ j : Fin 4, 4-(left+1) ≤ j.val → rootWordMatches s j) := by
        constructor
        · intro tail j valid
          by_cases first : j = i
          · rwa [first]
          · have jAfter : 4-left ≤ j.val := by
              have : j.val ≠ i.val := fun eq => first (Fin.ext eq)
              have : i.val = 4-(left+1) := rfl
              omega
            exact (stable j).mp (tail j jAfter)
        · intro all j valid
          exact (stable j).mpr (all j (by omega))
      by_cases all : ∀ j : Fin 4, 4-left ≤ j.val → rootWordMatches next j
      · rw [if_pos all, if_pos (iff.mp all)]
      · rw [if_neg all, if_neg (fun h => all (iff.mpr h))]
    · refine ⟨next, 3, by omega, hop, nmem, nregs, ?_⟩
      change next.pc = _ at npc
      rw [npc, if_neg same, if_neg (fun all => same (all i (by rfl)))]

def searchAcceptState (s : MachineState) : MachineState :=
  ((s.setReg .x5 1).setReg .x10 0).setPC (spc 1216)

theorem execute_search_accept (s : MachineState) (pc : s.pc = spc 1214) (fuel : Nat) :
    execute packedImage (3+fuel) s false = pure ⟨.success, searchAcceptState s, 3, 0⟩ := by
  let first := (s.setReg .x5 1).setPC (spc 1215)
  have a := wide_image_fetch packedImage s 1214 (.ADDI .x5 .x0 1) (by decide) pc searchCode1214
  have b := wide_image_fetch packedImage first 1215 (.ADDI .x10 .x0 0) (by decide) rfl searchCode1215
  have c := wide_image_fetch packedImage (searchAcceptState s) 1216 .ECALL (by decide) rfl searchCode1216
  have r : ordinaryStep s (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 0)) = some (searchAcceptState s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, searchAcceptState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

def nextState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (.ADDI .x19 .x19 1)) (.ADDI .x7 .x0 256)) (.BNE .x19 .x7 8044)

theorem next_trial (s : MachineState) (g : Nat) (pc : s.pc = spc 1217) (trial : s.getReg .x19 = BitVec.ofNat 64 g)
    (small : g < 256) :
    Hop s (nextState s) 3 3 ∧ (nextState s).mem = s.mem ∧ (nextState s).getReg .x19 = BitVec.ofNat 64 (g+1) ∧
      (nextState s).pc = (if g+1 = 256 then spc 1220 else spc 1182) ∧
      ∀ r, r ≠ .x7 → r ≠ .x19 → (nextState s).getReg r = s.getReg r := by
  let s1 := execInstrBr s (.ADDI .x19 .x19 1)
  let s2 := execInstrBr s1 (.ADDI .x7 .x0 256)
  have p1 : s1.pc = spc 1218 := by rw [straight_pc _ _ (by rfl), pc]; decide
  have p2 : s2.pc = spc 1219 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have a := search_step s 1217 _ pc (by decide) searchCode1217 rfl rfl
  have b := search_step s1 1218 _ p1 (by decide) searchCode1218 rfl rfl
  have c := search_step s2 1219 _ p2 (by decide) searchCode1219 rfl rfl
  have x19 : s2.getReg .x19 = BitVec.ofNat 64 (g+1) := by
    simp [s2, s1, execInstrBr, reg_setReg, trial, signExtend12, ← BitVec.ofNat_add]
  have x7 : s2.getReg .x7 = 256#64 := by simp [s2, execInstrBr, reg_setReg] <;> decide
  refine ⟨(a.thenDo b).thenDo c, ((branch_mem _ _ _ _).1).trans rfl, ?_, ?_, ?_⟩
  · show (execInstrBr s2 _).getReg .x19 = _
    rw [(branch_reg _ _ _ _ _).1, x19]
  · show (execInstrBr s2 _).pc = _
    rw [bne_pc, x19, x7, p2]
    by_cases top : g+1 = 256
    · rw [if_pos (by rw [top]), if_pos top]; decide
    · have ne : BitVec.ofNat 64 (g+1) ≠ 256#64 := by
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      rw [if_neg ne, if_neg top]; decide
  · intro r a b
    show (execInstrBr s2 _).getReg r = _
    rw [(branch_reg _ _ _ _ _).1]
    simp [s2, s1, execInstrBr, reg_setReg, Ne.symm a, Ne.symm b]

theorem last_jump (s : MachineState) (pc : s.pc = spc 1220) :
    Hop s (execInstrBr s (.JAL .x0 2093728)) 1 1 ∧ (execInstrBr s (.JAL .x0 2093728)).pc = 0x15b0 := by
  refine ⟨search_step s 1220 _ pc (by decide) searchCode1220 rfl rfl, ?_⟩
  rw [jal_pc, pc]
  decide
