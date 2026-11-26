import CommitGolfCandidate.R1bMachine
namespace CommitGolfCandidate.R1b.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def keepsCount : Option Instruction → Bool
  | some (.base op) => match op with
    | .ADD d .. | .ADDI d .. | .ANDI d .. | .DIVU d .. | .JAL d .. | .LBU d ..
    | .LD d .. | .LHU d .. | .LUI d .. | .LWU d .. | .OR d .. | .SLLI d ..
    | .SRLI d .. | .SUB d .. | .XORI d .. => d != .x16
    | .BEQ .. | .BGEU .. | .BLTU .. | .BNE .. | .ECALL | .SB .. | .SD .. | .SH .. | .SW .. => true
    | _ => false
  | none => true
  | _ => false

private theorem ordinaryCount (s t : MachineState) (op : Instruction) (allowed : keepsCount (some op))
    (step : ordinaryStep s op=some t) : t.getReg .x16=s.getReg .x16 := by
  cases op with
  | word => contradiction
  | sraiw => contradiction
  | base ins =>
    cases ins <;> first | contradiction | (
      simp only [ordinaryStep] at step
      split at step <;> simp_all only [Option.some.injEq,reduceCtorEq]
      subst t
      simp_all [keepsCount,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne])
    all_goals first | rfl | (split <;> rfl)

private theorem answerCount (s : MachineState) (q : PublicSpec.Domain) (a : PublicSpec.Range q) :
    (writeOracleAnswer s (s.getReg .x12) q a).getReg .x16=s.getReg .x16 := by
  rcases q with h | p
  · exact writeBits_register .. 
  · cases p <;> exact writeBits_register ..

private theorem ordinaryCase (op : Instruction) (h : op≠.base .ECALL)
    (img : Image) (s : MachineState) (fuel : Nat) (f : fetch img s=some op) :
    execute img (fuel+1) s false =
      match ordinaryStep s op with
      | none => pure ⟨.failure,s,1,0⟩
      | some t => do
        let out ← execute img fuel t false
        return out.charge (instructionCycles op) 0 := by
  rw [execute,f]
  cases op with
  | base i=>cases i <;> first | rfl | contradiction
  | word=>rfl
  | sraiw=>rfl

theorem countRun (img : Image) (closed : ∀ s,keepsCount (fetch img s))
    (n : Nat) (s : MachineState) {out : Execution} (hit : out ∈ support (execute img n s false)) :
    out.state.getReg .x16=s.getReg .x16 := by
  induction n generalizing s out with
  | zero =>
    simp only [execute,support_pure,Set.mem_singleton_iff] at hit
    subst out;rfl
  | succ n ih =>
    cases f : fetch img s with
    | none => rw [execute,f] at hit;simp only [support_pure,Set.mem_singleton_iff] at hit;subst out;rfl
    | some op =>
      by_cases e : op=.base .ECALL
      · subst op
        by_cases zero : s.getReg .x5=0
        · cases query : oracleInput s with
          | none =>
            simp only [execute,f,if_pos zero,query,support_pure,Set.mem_singleton_iff] at hit
            subst out;rfl
          | some q =>
            simp only [execute,f,if_pos zero,query,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
            obtain ⟨answer,_,res,path,rfl⟩:=hit
            exact (ih _ path).trans (answerCount s q answer)
        · by_cases halt : s.getReg .x5=1
          · simp only [execute,f,if_neg zero,if_pos halt,support_pure,Set.mem_singleton_iff] at hit
            subst out;rfl
          · simp only [execute,f,if_neg zero,if_neg halt,Bool.false_and,Bool.false_eq_true,ite_false,
              support_pure,Set.mem_singleton_iff] at hit
            subst out;rfl
      · have allowed :=closed s
        rw [f] at allowed
        rw [ordinaryCase op e img s n f] at hit
        cases step : ordinaryStep s op with
        | none =>
          simp only [step,support_pure,Set.mem_singleton_iff] at hit;subst out;rfl
        | some t =>
          simp only [step,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
          obtain ⟨res,ran,rfl⟩:=hit
          exact (ih _ ran).trans (ordinaryCount s t op allowed step)

end CommitGolfCandidate.R1b.Machine
