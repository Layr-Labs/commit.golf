import CommitGolfCandidate.LateInitial
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem setup_frame (s : MachineState) (msg : s.getReg .x10 = 4096)
    (root : s.getReg .x11 = 4294971392) (td : s.getReg .x12 = 4294971424) :
    let t := setupState s 16
    t.getReg .x8 = 4096 ∧ t.getReg .x9 = 4294971424 ∧ t.getReg .x18 = 5905584160 ∧
      t.getReg .x23 = 4294971424 ∧ t.getReg .x26 = 4294971392 := by
  have h1_8 : (setupState s 1).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 1 = execInstrBr (setupState s 0) (.ADDI .x8 .x10 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x8 .x10 0)).getReg .x8 = (q.getReg .x10 + 0) := rfl
    rw [step, get] <;> rfl
  have h2_8 : (setupState s 2).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 2 = execInstrBr (setupState s 1) (.ADDI .x26 .x11 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h1_8] <;> rfl
  have h3_8 : (setupState s 3).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 3 = execInstrBr (setupState s 2) (.ADDI .x9 .x12 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x9 .x12 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h2_8] <;> rfl
  have h4_8 : (setupState s 4).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 4 = execInstrBr (setupState s 3) (.ADDI .x6 .x0 384) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 384)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h3_8] <;> rfl
  have h5_8 : (setupState s 5).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 5 = execInstrBr (setupState s 4) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h4_8] <;> rfl
  have h6_8 : (setupState s 6).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 6 = execInstrBr (setupState s 5) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h5_8] <;> rfl
  have h7_8 : (setupState s 7).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 7 = execInstrBr (setupState s 6) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h6_8] <;> rfl
  have h8_8 : (setupState s 8).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 8 = execInstrBr (setupState s 7) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h7_8] <;> rfl
  have h9_8 : (setupState s 9).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 9 = execInstrBr (setupState s 8) (.ADD .x18 .x9 .x6) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADD .x18 .x9 .x6)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h8_8] <;> rfl
  have h10_8 : (setupState s 10).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 10 = execInstrBr (setupState s 9) (.ADDI .x23 .x9 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x23 .x9 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h9_8] <;> rfl
  have h11_8 : (setupState s 11).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h10_8] <;> rfl
  have h12_8 : (setupState s 12).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h11_8] <;> rfl
  have h13_8 : (setupState s 13).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h12_8] <;> rfl
  have h14_8 : (setupState s 14).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h13_8] <;> rfl
  have h15_8 : (setupState s 15).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h14_8] <;> rfl
  have h16_8 : (setupState s 16).getReg .x8 = ((s.getReg .x10) + 0) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x8 = q.getReg .x8 := rfl
    rw [step, get, h15_8] <;> rfl
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
  have h9_9 : (setupState s 9).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 9 = execInstrBr (setupState s 8) (.ADD .x18 .x9 .x6) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADD .x18 .x9 .x6)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h8_9] <;> rfl
  have h10_9 : (setupState s 10).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 10 = execInstrBr (setupState s 9) (.ADDI .x23 .x9 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x23 .x9 0)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h9_9] <;> rfl
  have h11_9 : (setupState s 11).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h10_9] <;> rfl
  have h12_9 : (setupState s 12).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h11_9] <;> rfl
  have h13_9 : (setupState s 13).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h12_9] <;> rfl
  have h14_9 : (setupState s 14).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h13_9] <;> rfl
  have h15_9 : (setupState s 15).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h14_9] <;> rfl
  have h16_9 : (setupState s 16).getReg .x9 = ((s.getReg .x12) + 0) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x9 = q.getReg .x9 := rfl
    rw [step, get, h15_9] <;> rfl
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
  have h11_18 : (setupState s 11).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h10_18] <;> rfl
  have h12_18 : (setupState s 12).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h11_18] <;> rfl
  have h13_18 : (setupState s 13).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h12_18] <;> rfl
  have h14_18 : (setupState s 14).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h13_18] <;> rfl
  have h15_18 : (setupState s 15).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h14_18] <;> rfl
  have h16_18 : (setupState s 16).getReg .x18 = (((s.getReg .x12) + 0) + (((((0 + 384) <<< 11) + 0) <<< 11) + 0)) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x18 = q.getReg .x18 := rfl
    rw [step, get, h15_18] <;> rfl
  have h10_23 : (setupState s 10).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 10 = execInstrBr (setupState s 9) (.ADDI .x23 .x9 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x23 .x9 0)).getReg .x23 = (q.getReg .x9 + 0) := rfl
    rw [step, get, h9_9] <;> rfl
  have h11_23 : (setupState s 11).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h10_23] <;> rfl
  have h12_23 : (setupState s 12).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h11_23] <;> rfl
  have h13_23 : (setupState s 13).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h12_23] <;> rfl
  have h14_23 : (setupState s 14).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h13_23] <;> rfl
  have h15_23 : (setupState s 15).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h14_23] <;> rfl
  have h16_23 : (setupState s 16).getReg .x23 = (((s.getReg .x12) + 0) + 0) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x23 = q.getReg .x23 := rfl
    rw [step, get, h15_23] <;> rfl
  have h1_11 : (setupState s 1).getReg .x11 = (s.getReg .x11) := by
    have step : setupState s 1 = execInstrBr (setupState s 0) (.ADDI .x8 .x10 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x8 .x10 0)).getReg .x11 = q.getReg .x11 := rfl
    rw [step, get] <;> rfl
  have h2_26 : (setupState s 2).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 2 = execInstrBr (setupState s 1) (.ADDI .x26 .x11 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x26 = (q.getReg .x11 + 0) := rfl
    rw [step, get, h1_11] <;> rfl
  have h3_26 : (setupState s 3).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 3 = execInstrBr (setupState s 2) (.ADDI .x9 .x12 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x9 .x12 0)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h2_26] <;> rfl
  have h4_26 : (setupState s 4).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 4 = execInstrBr (setupState s 3) (.ADDI .x6 .x0 384) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 384)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h3_26] <;> rfl
  have h5_26 : (setupState s 5).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 5 = execInstrBr (setupState s 4) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h4_26] <;> rfl
  have h6_26 : (setupState s 6).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 6 = execInstrBr (setupState s 5) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h5_26] <;> rfl
  have h7_26 : (setupState s 7).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 7 = execInstrBr (setupState s 6) (.SLLI .x6 .x6 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h6_26] <;> rfl
  have h8_26 : (setupState s 8).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 8 = execInstrBr (setupState s 7) (.ADDI .x6 .x6 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 0)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h7_26] <;> rfl
  have h9_26 : (setupState s 9).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 9 = execInstrBr (setupState s 8) (.ADD .x18 .x9 .x6) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADD .x18 .x9 .x6)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h8_26] <;> rfl
  have h10_26 : (setupState s 10).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 10 = execInstrBr (setupState s 9) (.ADDI .x23 .x9 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x23 .x9 0)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h9_26] <;> rfl
  have h11_26 : (setupState s 11).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 11 = execInstrBr (setupState s 10) (.ADDI .x10 .x18 72) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x10 .x18 72)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h10_26] <;> rfl
  have h12_26 : (setupState s 12).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 12 = execInstrBr (setupState s 11) (.ADDI .x11 .x0 48) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x11 .x0 48)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h11_26] <;> rfl
  have h13_26 : (setupState s 13).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 13 = execInstrBr (setupState s 12) (.ADDI .x5 .x0 2) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 2)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h12_26] <;> rfl
  have h14_26 : (setupState s 14).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 14 = execInstrBr (setupState s 13) (.ADDI .x20 .x0 16) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x0 16)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h13_26] <;> rfl
  have h15_26 : (setupState s 15).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 15 = execInstrBr (setupState s 14) (.SLLI .x20 .x20 11) := rfl
    have get (q : MachineState) : (execInstrBr q (.SLLI .x20 .x20 11)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h14_26] <;> rfl
  have h16_26 : (setupState s 16).getReg .x26 = ((s.getReg .x11) + 0) := by
    have step : setupState s 16 = execInstrBr (setupState s 15) (.ADDI .x20 .x20 0) := rfl
    have get (q : MachineState) : (execInstrBr q (.ADDI .x20 .x20 0)).getReg .x26 = q.getReg .x26 := rfl
    rw [step, get, h15_26] <;> rfl
  dsimp only
  rw [h16_8,h16_9,h16_18,h16_23,h16_26,msg,root,td]
  decide

theorem unchanged_draws (ws : List PairCoins) (p : Nat) (s : MachineState) (reg : Reg)
    (ten : .x10 ≠ reg) (twenty : .x20 ≠ reg) : (applyPairs p s ws).getReg reg = s.getReg reg := by
  have branch (q : MachineState) : (branchBack q).getReg reg = q.getReg reg := by
    have choose (c : Bool) (y n : Word) :
        (if c then q.setPC y else q.setPC n).getReg reg = q.getReg reg := by cases c <;> exact MachineState.getReg_setPC
    exact choose (q.getReg .x20 != q.getReg .x0) (q.pc+signExtend13 6140) (q.pc+4)
  induction ws generalizing p s with
  | nil => rfl
  | cons w ws ih =>
    rw [applyPairs,ih]
    unfold nextPair
    split
    · rw [branch]
      simp only [decrement,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ twenty]
      exact (random_registers s w).2.2 reg ten.symm
    · exact (random_registers s w).2.2 reg ten.symm

end CommitGolfCandidate.Late
