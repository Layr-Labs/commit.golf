import CommitGolfCandidate.LateSaltRead

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def setup : List Instr :=
  [.ADDI .x8 .x10 0, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0,
   .ADDI .x6 .x0 384, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 0, .ADD .x18 .x9 .x6, .ADDI .x23 .x9 0, .ADDI .x10 .x18 72,
   .ADDI .x11 .x0 48, .ADDI .x5 .x0 2, .ADDI .x20 .x0 16, .SLLI .x20 .x20 11,
   .ADDI .x20 .x20 0]

def setupState (s : MachineState) (n : Nat) :=
  (setup.take n).foldl execInstrBr s

set_option maxRecDepth 8000 in
theorem setup_pair (s : MachineState) (ip : s.pc = 4096) (td : s.getReg .x12 = 4294971424) :
    AtPair (setupState s 16) 0 := by
  have h14_20 : (setupState s 14).getReg .x20 = (0 + 16) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x20 = (q.getReg .x0 + 16) := rfl
    rw [step, get] <;> rfl
  have h15_20 : (setupState s 15).getReg .x20 = ((0 + 16) <<< 11) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x20 = (q.getReg .x20 <<< 11) := rfl
    rw [step, get, h14_20] <;> rfl
  have h16_20 : (setupState s 16).getReg .x20 = (((0 + 16) <<< 11) + 0) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x20 = (q.getReg .x20 + 0) := rfl
    rw [step, get, h15_20] <;> rfl
  have h13_5 : (setupState s 13).getReg .x5 = (0 + 2) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x5 = (q.getReg .x0 + 2) := rfl
    rw [step, get] <;> rfl
  have h14_5 : (setupState s 14).getReg .x5 = (0 + 2) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x5 = q.getReg .x5 := rfl
    rw [step, get, h13_5] <;> rfl
  have h15_5 : (setupState s 15).getReg .x5 = (0 + 2) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x5 = q.getReg .x5 := rfl
    rw [step, get, h14_5] <;> rfl
  have h16_5 : (setupState s 16).getReg .x5 = (0 + 2) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x5 = q.getReg .x5 := rfl
    rw [step, get, h15_5] <;> rfl
  have h12_11 : (setupState s 12).getReg .x11 = (0 + 48) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x11 = (q.getReg .x0 + 48) := rfl
    rw [step, get] <;> rfl
  have h13_11 : (setupState s 13).getReg .x11 = (0 + 48) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x11 = q.getReg .x11 := rfl
    rw [step, get, h12_11] <;> rfl
  have h14_11 : (setupState s 14).getReg .x11 = (0 + 48) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x11 = q.getReg .x11 := rfl
    rw [step, get, h13_11] <;> rfl
  have h15_11 : (setupState s 15).getReg .x11 = (0 + 48) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x11 = q.getReg .x11 := rfl
    rw [step, get, h14_11] <;> rfl
  have h16_11 : (setupState s 16).getReg .x11 = (0 + 48) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x11 = q.getReg .x11 := rfl
    rw [step, get, h15_11] <;> rfl
  have h1_12 : (setupState s 1).getReg .x12 = (s.getReg .x12) := by
    have step : setupState s 1 = execInstrBr (setupState s 0) (.ADDI .x8 .x10 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x8 .x10 0)).getReg .x12 = q.getReg .x12 := rfl
    rw [step, get] <;> rfl
  have h2_12 : (setupState s 2).getReg .x12 = (s.getReg .x12) := by
    have step : setupState s 2 = execInstrBr (setupState s 1) (.ADDI .x26 .x11 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x12 = q.getReg .x12 := rfl
    rw [step, get, h1_12] <;> rfl
  have h3_9 : (setupState s 3).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 3 = execInstrBr (setupState s 2) (.ADDI .x9 .x12 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x9 .x12 0)).getReg .x9 = (q.getReg .x12 + 0) := rfl
    rw [step, get, h2_12] <;> rfl
  have h4_9 : (setupState s 4).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 4 = execInstrBr (setupState s 3) (.ADDI .x6 .x0 384) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 384)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h3_9] <;> rfl
  have h5_9 : (setupState s 5).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 5 = execInstrBr (setupState s 4) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h4_9] <;> rfl
  have h6_9 : (setupState s 6).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 6 = execInstrBr (setupState s 5) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h5_9] <;> rfl
  have h7_9 : (setupState s 7).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 7 = execInstrBr (setupState s 6) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h6_9] <;> rfl
  have h8_9 : (setupState s 8).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 8 = execInstrBr (setupState s 7) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h7_9] <;> rfl
  have h4_6 : (setupState s 4).getReg .x6 = (0 + 384) := by
    have step : setupState s 4 = execInstrBr (setupState s 3) (.ADDI .x6 .x0 384) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 384)).getReg .x6 = (q.getReg .x0 + 384) := rfl
    rw [step, get] <;> rfl
  have h5_6 : (setupState s 5).getReg .x6 = ((0 + 384) <<< 11) := by
    have step : setupState s 5 = execInstrBr (setupState s 4) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x6 = (q.getReg .x6 <<< 11) := rfl
    rw [step, get, h4_6] <;> rfl
  have h6_6 : (setupState s 6).getReg .x6 = (((0 + 384) <<< 11) + 0) := by
    have step : setupState s 6 = execInstrBr (setupState s 5) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x6 = (q.getReg .x6 + 0) := rfl
    rw [step, get, h5_6] <;> rfl
  have h7_6 : (setupState s 7).getReg .x6 = ((((0 + 384) <<< 11) + 0) <<< 11) := by
    have step : setupState s 7 = execInstrBr (setupState s 6) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x6 = (q.getReg .x6 <<< 11) := rfl
    rw [step, get, h6_6] <;> rfl
  have h8_6 : (setupState s 8).getReg .x6 = (((((0 + 384) <<< 11) + 0) <<< 11) + 0) := by
    have step : setupState s 8 = execInstrBr (setupState s 7) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x6 = (q.getReg .x6 + 0) := rfl
    rw [step, get, h7_6] <;> rfl
  have h9_18 : (setupState s 9).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 9 = execInstrBr (setupState s 8) (.ADD .x18 .x9 .x6) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADD .x18 .x9 .x6)).getReg .x18 = (q.getReg .x9 + q.getReg .x6) := rfl
    rw [step, get, h8_9, h8_6] <;> rfl
  have h10_18 : (setupState s 10).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 10 = execInstrBr (setupState s 9) (.ADDI .x23 .x9 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x23 .x9 0)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h9_18] <;> rfl
  have h11_10 : (setupState s 11).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x10 = (q.getReg .x18 + 72) := rfl
    rw [step, get, h10_18] <;> rfl
  have h12_10 : (setupState s 12).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x10 = q.getReg .x10 := rfl
    rw [step, get, h11_10] <;> rfl
  have h13_10 : (setupState s 13).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x10 = q.getReg .x10 := rfl
    rw [step, get, h12_10] <;> rfl
  have h14_10 : (setupState s 14).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x10 = q.getReg .x10 := rfl
    rw [step, get, h13_10] <;> rfl
  have h15_10 : (setupState s 15).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x10 = q.getReg .x10 := rfl
    rw [step, get, h14_10] <;> rfl
  have h16_10 : (setupState s 16).getReg .x10 = ((((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) + 72) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x10 = q.getReg .x10 := rfl
    rw [step, get, h15_10] <;> rfl
  constructor
  · change (s.pc+4+4+4+4+4+4+4+4+4+4+4+4+4+4+4+4) = (4160 : Word)
    rw [ip]; rfl
  · exact h16_20
  · exact h16_5
  · exact h16_11
  · rw [h16_10, td]; rfl

set_option maxHeartbeats 1200000 in
theorem execute_setup (s : MachineState) (ip : s.pc = 4096) (fuel : Nat) :
    execute commitImage (16+fuel) s true =
      (do let r ← execute commitImage fuel (setupState s 16) true
          return r.charge 16 0) := by
  apply execute_unit_steps (states := setupState s)
  intro i hi
  refine ⟨.base (setup[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply (fetch_word (i := i) (w := setupWords[i]?.getD 0) _ (by omega) _).trans
    · interval_cases i <;> rfl
    · interval_cases i <;> simp [setupState, setup, execInstrBr, MachineState.setPC, ip, pcAt]
    · change (setupWords ++ _)[i]? = _
      rw [List.getElem?_append_left (by change i < 16; omega)]
      interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/- The entire 2^23-draw loop, including setup, can be replaced by its actual
ordered word sampler and a deterministic state update before the hash phase. -/
attribute [local irreducible] List.range execute commitImage

theorem commit_through_sampling (s : MachineState) (ip : s.pc = 4096)
    (td : s.getReg .x12 = 4294971424) (fuel : Nat) :
    execute commitImage (16842768 + fuel) s true =
      (do let ws ← (List.range (LENGTH/2)).mapM fun _ => drawPair
          let r ← execute commitImage fuel (applyPairs 0 (setupState s 16) ws) true
          return r.charge 67174416 0) := by
  let xs := List.range (LENGTH/2)
  have hlen : xs.length = pairCount := List.length_range
  have loop := execute_pairs xs 0 (setupState s 16) (setup_pair s ip td) (by rw [hlen]; omega) fuel
  rw [hlen] at loop
  change execute commitImage (fuel + 16842752) (setupState s 16) true = _ at loop
  rw [show 16842768+fuel = 16+(fuel+16842752) by omega, execute_setup s ip, loop]
  simp only [bind_assoc, pure_bind]
  change (do let ws ← xs.mapM fun _ => drawPair
             let r ← execute commitImage fuel (applyPairs 0 (setupState s 16) ws) true
             return (r.charge 67174400 0).charge 16 0) = _
  simp only [Execution.charge, ← Nat.add_assoc, Nat.zero_add]
  rfl

end CommitGolfCandidate.Late
