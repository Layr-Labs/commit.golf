import CommitGolfCandidate.TwoPermutationPackedPostorderProgram

namespace TwoPermutationPrototype.Opening.Postorder
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem
attribute [local irreducible] execute

private theorem run_leaf (s : MachineState) (n d i fuel : Nat) (coins : Bool)
    (code : CodeAt i (words n 0 d)) (span : CapSpan n 0) (within : i+1 ≤ 1441)
    (base : s.getReg .x6 = 6143#64) (pc : s.pc = pcOf i) :
    execute TwoPermutationPrototype.PackedOpening.openingImage (1+fuel) s coins =
      (do let r ← execute TwoPermutationPrototype.PackedOpening.openingImage fuel (eval s n 0 d) coins
          return r.charge 1 0) := by
  have nbound := (cap_span_node n 0 span).2
  have decoded := code ⟨0,by change 0 < 1; decide⟩
  have fetched := TwoPermutationPrototype.PackedOpening.packed_fetch_raw s i (.LD (reg d) .x6 (offset n)) (by omega) pc decoded
  have decodedAddr := offset_ok ⟨n, nbound⟩
  have valid := addr_valid n nbound
  have step : ordinaryStep s (.base (.LD (reg d) .x6 (offset n))) = some (eval s n 0 d) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, eval, base, decodedAddr, valid]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

private theorem run_finish (s : MachineState) (n d i fuel : Nat) (coins : Bool)
    (code : CodeAt i [.OR (reg d) (reg d) (reg (d+1)), .SD .x6 (reg d) (offset n)])
    (nbound : n < 512) (dbound : d < 9) (within : i+2 ≤ 1441)
    (base : s.getReg .x6 = 6143#64) (pc : s.pc = pcOf i) :
    execute TwoPermutationPrototype.PackedOpening.openingImage (2+fuel) s coins =
      (do let r ← execute TwoPermutationPrototype.PackedOpening.openingImage fuel (finish s n d) coins
          return r.charge 2 0) := by
  let w := s.getReg (reg d) ||| s.getReg (reg (d+1))
  let mid := (s.setReg (reg d) w).setPC (s.pc+4)
  have f1 := TwoPermutationPrototype.PackedOpening.packed_fetch_raw s i (.OR (reg d) (reg d) (reg (d+1))) (by omega) pc (code ⟨0,by change 0 < 2; decide⟩)
  have s1 : ordinaryStep s (.base (.OR (reg d) (reg d) (reg (d+1)))) = some mid := rfl
  have pc' : mid.pc = pcOf (i+1) := by change s.pc+4 = _; rw [pc]; exact add_pc i 1
  have f2 := TwoPermutationPrototype.PackedOpening.packed_fetch_raw mid (i+1) (.SD .x6 (reg d) (offset n)) (by omega) pc' (code ⟨1,by change 1 < 2; decide⟩)
  have value : mid.getReg (reg d) = w := by simp [mid, reg_ne_zero ⟨d,dbound⟩]
  have midBase : mid.getReg .x6 = 6143#64 := by simp [mid, reg_ne_base ⟨d,dbound⟩, base]
  have decodedAddr := offset_ok ⟨n,nbound⟩
  have valid := addr_valid n nbound
  have s2 : ordinaryStep mid (.base (.SD .x6 (reg d) (offset n))) = some (finish s n d) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      midBase, value, decodedAddr, valid]
    simp [finish, mid, w, MachineState.setMem, MachineState.setPC, BitVec.add_assoc]
  rw [show 2+fuel = fuel+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 s1,
    execute_ordinary_step _ _ _ _ _ _ f2 s2]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem run (s : MachineState) (n h d i fuel : Nat) (coins : Bool)
    (code : CodeAt i (words n h d)) (span : CapSpan n h)
    (space : d+h < 9) (within : i+cost h ≤ 1441)
    (base : s.getReg .x6 = 6143#64) (pc : s.pc = pcOf i) :
    execute TwoPermutationPrototype.PackedOpening.openingImage (cost h+fuel) s coins =
      (do let r ← execute TwoPermutationPrototype.PackedOpening.openingImage fuel (eval s n h d) coins
          return r.charge (cost h) 0) := by
  induction h generalizing s n d i fuel with
  | zero => exact run_leaf s n d i fuel coins code span within base pc
  | succ h ih =>
    obtain ⟨ls,rs⟩ := cap_span_children n h span
    obtain ⟨lc,tail⟩ := split_code (a := words (2*n) h d) code
    obtain ⟨rc,fc⟩ := split_code (a := words (2*n+1) h (d+1)) tail
    simp only [words_length] at rc fc
    change i+(cost h + cost h + 2) ≤ 1441 at within
    let l := eval s (2*n) h d
    let r := eval l (2*n+1) h (d+1)
    have lb : l.getReg .x6 = 6143#64 :=
      (eval_register s _ _ _ _ (by intro j lo hi; exact reg_ne_base ⟨j, by omega⟩)).trans base
    have rb : r.getReg .x6 = 6143#64 :=
      (eval_register l _ _ _ _ (by intro j lo hi; exact reg_ne_base ⟨j, by omega⟩)).trans lb
    have lp := eval_pc s (2*n) h d i pc
    have rp := eval_pc l (2*n+1) h (d+1) (i+cost h) lp
    have left := ih s (2*n) d i (cost h+(2+fuel)) lc ls (by omega) (by omega) base pc
    have right := ih l (2*n+1) (d+1) (i+cost h) (2+fuel) rc rs (by omega) (by omega) lb lp
    have last := run_finish r n d (i+cost h+cost h) fuel coins fc
      (cap_span_node n _ span).2 (by omega) (by omega) rb rp
    change execute TwoPermutationPrototype.PackedOpening.openingImage ((cost h+cost h+2)+fuel) s coins = _
    rw [show cost h+cost h+2+fuel = cost h+(cost h+(2+fuel)) by omega, left]
    change (do let out ← execute TwoPermutationPrototype.PackedOpening.openingImage (cost h+(2+fuel)) l coins; return out.charge (cost h) 0) = _
    rw [right]
    simp only [bind_pure_comp, Functor.map_map]
    change (fun out => (out.charge (cost h) 0).charge (cost h) 0) <$>
      execute TwoPermutationPrototype.PackedOpening.openingImage (2+fuel) r coins = _
    rw [last]
    simp [eval, cost, l, r, Execution.charge, ← Nat.add_assoc]

end TwoPermutationPrototype.Opening.Postorder
