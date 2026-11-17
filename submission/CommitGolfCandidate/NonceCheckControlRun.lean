import CommitGolfCandidate.NonceCheckControlStep
import CommitGolfCandidate.NonceOpeningSupport

namespace CommitGolfCandidate.NonceCheckControl
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem checked_step (state next : MachineState) (instruction : Instruction)
    (safe : checked state.pc instruction=true) (link : Link state)
    (stepped : ordinaryStep state instruction=some next) : StateControl next := by
  cases instruction with
  | base instruction => exact checked_base_step state next instruction safe link stepped
  | word op rd left right => simp only [checked,Bool.false_eq_true] at safe
  | sraiw rd source shift => simp only [checked,Bool.false_eq_true] at safe

theorem images_agree (state : MachineState) (control : StateControl state) :
    fetch nonceExpandedImage state=fetch oldImage state := by
  rcases control.1 with zero | core
  · simp only [fetch,zero]
    rfl
  · let index := (state.pc.toNat-4096)/4
    have positive : 1 ≤ index := by dsimp only [index]; unfold CorePC at core; omega
    have bounded : index<200 := by dsimp only [index]; unfold CorePC at core; omega
    have numeric : state.pc.toNat=4096+4*index := by dsimp only [index]; unfold CorePC at core; omega
    have pc : state.pc=BitVec.ofNat 64 (4096+4*index) := by
      calc
        state.pc=BitVec.ofNat 64 state.pc.toNat := by simp
        _ = _ := by rw [numeric]
    exact nonce_expanded_core_fetch state index positive bounded pc

theorem fetched_step_control (state next : MachineState) (instruction : Instruction)
    (control : StateControl state) (fetched : fetch oldImage state=some instruction)
    (stepped : ordinaryStep state instruction=some next) : StateControl next :=
  checked_step state next instruction (fetched_checked state instruction fetched) control.2 stepped

private theorem answer_register (state : MachineState) (address : Word)
    (query : PublicSpec.Domain) (answer : PublicSpec.Range query) (reg : Reg) :
    (writeOracleAnswer state address query answer).getReg reg=state.getReg reg := by
  cases query with
  | inl input => exact writeBits_register state address answer reg
  | inr query => cases query <;> exact writeBits_register state address answer reg

theorem oracle_control (state : MachineState) (control : StateControl state)
    (fetched : fetch oldImage state=some (.base .ECALL)) (address : Word)
    (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    StateControl (writeOracleAnswer state address query answer) := by
  have next : CorePC (state.pc+4) := by
    have safe:=fetched_checked state (.base .ECALL) fetched
    simpa only [checked,decide_eq_true_eq] using safe
  refine ⟨Or.inr ?_,?_⟩
  · rw [nonce_write_answer_pc]
    exact next
  · simpa only [Link,answer_register] using control.2

end CommitGolfCandidate.NonceCheckControl
