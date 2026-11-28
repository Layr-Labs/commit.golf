import CommitGolfCandidate.PentaGroupedDecode

/-! Index arithmetic and fetch lemmas for the 4,095-leaf counter-mode commit body. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem heads_succ (n : Nat) : heads (n + 1) = heads n + (if rank n = 0 then 1 else 0) := by
  unfold heads rank
  by_cases last : n % 4095 = 4094
  · rw [show (n + 1) / 4095 = n / 4095 + 1 by omega, show (n + 1) % 4095 = 0 by omega, last]
    norm_num; omega
  · rw [show (n + 1) / 4095 = n / 4095 by omega, show (n + 1) % 4095 = n % 4095 + 1 by omega]
    by_cases h : n % 4095 % 11 = 0 <;> simp [h] <;> omega

theorem credit_succ (n : Nat) : 11 + cacheCredit (n + 1) = cacheCredit n + bodyLen n := by
  unfold cacheCredit bodyLen rank
  have e : (n + 1) % 4095 = if n % 4095 = 4094 then 0 else n % 4095 + 1 := by split <;> omega
  rw [e]; split_ifs <;> omega

theorem rb_succ (n : Nat) : rb (n + 1) = rb n + (if rebase n then 1 else 0) := by
  have step : rb n ≤ rb (n + 1) ∧ rb (n + 1) ≤ rb n + 1 := by unfold rb; omega
  by_cases h : rebase n
  · rw [if_pos h]; unfold rebase at h; omega
  · rw [if_neg h]; unfold rebase at h; omega

theorem rb_le (n : Nat) (h : n < 4095) : rb n ≤ 90 := by unfold rb; omega
theorem rb_zero : rb 0 = 0 := by decide
theorem rb_last : rb 4094 = 90 := by decide
theorem rebase_last : rebase 4094 := by decide

/-- Total rebases over the 4,095-leaf passes: 91 per pass plus `rb` inside the current pass. -/
theorem rebases_succ (i : Nat) :
    91 * ((i + 1) / 4095) + rb ((i + 1) % 4095) =
      91 * (i / 4095) + rb (i % 4095) + (if rebase (i % 4095) then 1 else 0) := by
  by_cases last : i % 4095 = 4094
  · rw [show (i + 1) % 4095 = 0 by omega, show (i + 1) / 4095 = i / 4095 + 1 by omega,
      last, if_pos rebase_last, rb_zero, rb_last]
    omega
  · rw [show (i + 1) % 4095 = i % 4095 + 1 by omega, show (i + 1) / 4095 = i / 4095 by omega, rb_succ]
    by_cases h : rebase (i % 4095)
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

theorem packet_length (n : Nat) : (packet n).length = bodyLen n + (if rebase n then 1 else 0) := by
  unfold packet bodyLen
  split_ifs <;> rfl

theorem packet_next (n : Nat) : firstWord (n + 1) = firstWord n + (packet n).length := by
  rw [packet_length]; unfold firstWord
  have h := credit_succ n
  rw [rb_succ]
  split_ifs <;> omega

theorem first_word_0 : firstWord 0 = 17 := by decide
theorem first_word_4095 : firstWord 4095 = 45153 := by decide

theorem fetch_packet (n : Fin 4095) (i : Nat) (hi : i < (packet n.val).length)
    (state : MachineState) (pc : state.pc = wordPC (firstWord n.val + i)) :
    fetch image state = some (.base ((packet n.val)[i]?.getD .EBREAK)) := by
  have hn := n.isLt
  have len : (packet n.val).length ≤ 16 := by rw [packet_length]; unfold bodyLen; split_ifs <;> decide
  have ix : 64 * (n.val / 64) + n.val % 64 = n.val := Nat.div_add_mod ..
  have h := packet_tiles ⟨n.val / 64, by omega⟩ ⟨n.val % 64, by omega⟩ ⟨i, by omega⟩
  simp only [Fin.val_mk, ix] at h
  have rbBound := rb_le n.val hn
  have cap : cacheCredit n.val ≤ 4 := by unfold cacheCredit; split_ifs <;> decide
  exact fetch_decoded state (firstWord n.val + i) (by unfold firstWord; omega) pc _ (h hn hi)

theorem fetch_trailing (i : Nat) (hi : i < trailingPacket.length)
    (state : MachineState) (pc : state.pc = wordPC (45190 + i)) :
    fetch image state = some (.base ((trailingPacket[i]?).getD .EBREAK)) := by
  have hi' : i < 11 := by simpa [trailingPacket] using hi
  exact fetch_decoded state (45190 + i) (by omega) pc _ (trailing_decode ⟨i, hi'⟩)

end TwoPermutationPrototype.PentaGrouped
