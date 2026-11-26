import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestCallFlow
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestCuts
open CommitBlocks (addr)

def cost : Instruction→Nat
  | .base .ECALL => 1
  | _ => 0

private theorem charged (im : Image) (s : MachineState) (op : Instruction) (coins : Bool) (read : fetch im s=some op)
    (r : Execution) (run : r∈support (execute im 1 s coins)) : r.oracleCalls≤cost op := by
  cases op with
  | base op =>
    cases op <;> first | exact execute_calls_le_steps im 1 s coins r run | skip
    all_goals simp only [execute,read] at run
    all_goals split at run <;> simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run <;> subst r <;> exact le_rfl
  | word _ _ _ _ | sraiw _ _ _ =>
    simp only [execute,read] at run
    split at run <;> simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run <;> subst r <;> exact le_rfl

def test {n : Nat} (costs : ArtifactEncoding.Packed n) (cut : Word→Bool) (potential : Word→Nat)
    (i : Nat) (raw : BitVec 32) : Bool :=
  let pc := addr i
  if HonestBinaryRank.active costs pc then match decodeInstruction raw with
    | none => false
    | some op => decide (cost op≤potential pc) && (targets pc op).all (fun q => cut q || decide (cost op+potential q≤potential pc))
  else true

def Calls (im : Image) (s : MachineState) (coins : Bool) (bound : Nat) :=
  ∀ f r, r∈support (execute im f s coins) → r.oracleCalls≤bound

theorem extend (im : Image) (s : MachineState) (coins : Bool) (f extra : Nat) (r : Execution)
    (run : r∈support (execute im f s coins)) :
    ∃ out∈support (execute im (f+extra) s coins), r.oracleCalls≤out.oracleCalls := by
  rw [execute_add]
  by_cases progress : r.exit=.unfinished
  · obtain ⟨tail,rest⟩ := support_nonempty (execute im extra r.state coins)
    refine ⟨tail.charge r.cycles r.oracleCalls,?_,?_⟩
    · rw [mem_support_bind_iff]
      refine ⟨r,run,?_⟩
      simp only [resume,progress,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
      exact ⟨tail,rest,rfl⟩
    · change r.oracleCalls≤r.oracleCalls+tail.oracleCalls; omega
  · refine ⟨r,?_,le_rfl⟩
    rw [mem_support_bind_iff]
    refine ⟨r,run,?_⟩
    simp only [resume,ite_eq_right progress,support_pure,Set.mem_singleton_iff]

theorem bounded {n : Nat} (im : Image) (packed costs : ArtifactEncoding.Packed n)
    (same : im.code=ArtifactEncoding.decode 32 packed) (small : 4096+4*n<2^64)
    (cut zero : Word→Bool) (potential : Word→Nat)
    (ranked : Ranking im (HonestBinaryRank.active costs) cut zero (HonestBinaryRank.rank costs))
    (table : CommitBlocks.allWords packed 0 (test costs cut potential)=true)
    (s : MachineState) (entry : HonestBinaryRank.active costs s.pc=true) (mode : zero s.pc=true → s.getReg .x5=0)
    (coins : Bool) (tail : Nat) (boundary : ∀ t, Reaches im coins cut s t → Calls im t coins tail) :
    Calls im s coins (potential s.pc+tail) := by
  intro fuel r run
  induction fuel generalizing s r with
  | zero => simp only [execute,support_pure,Set.mem_singleton_iff] at run; subst r; exact Nat.zero_le _
  | succ fuel ih =>
    obtain ⟨op,read,dir,safe,_,edges⟩ := ranked.step s entry
    have act := entry
    simp only [HonestBinaryRank.active,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at act
    have idx : HonestBinaryRank.index s.pc<n := by
      by_contra no; simp only [HonestBinaryRank.rank,dite_eq_right no,Nat.lt_irrefl] at act; exact act.2
    have receipt := CommitBlocks.checked_word _ _ _ table ⟨HonestBinaryRank.index s.pc,idx⟩
    have fetch := fetch_packed im packed same _ idx (by omega) s act.1
    rw [read] at fetch
    simp only [Nat.zero_add,test,←act.1,entry,ite_true,←fetch,Bool.and_eq_true,decide_eq_true_eq] at receipt
    rw [show fuel+1=1+fuel by omega,execute_add,mem_support_bind_iff] at run
    obtain ⟨mid,first,rest⟩ := run
    have fee := charged im s op coins read mid first
    by_cases cont : mid.exit=.unfinished
    · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
      obtain ⟨out,after,rfl⟩ := rest
      obtain ⟨target,clean⟩ := ((charged_successors im s op coins read dir (mode ∘ safe) mid first).2 cont)
      cases stop : cut mid.state.pc with
      | true =>
        have advance := boundary _ (.hit first cont stop) fuel out after
        change mid.oracleCalls+out.oracleCalls≤_
        omega
      | false =>
        have edge := edges _ target
        simp only [stop,Bool.false_eq_true,false_or] at edge
        have price := List.all_eq_true.mp receipt.2 _ target
        simp only [stop,Bool.false_or,decide_eq_true_eq] at price
        have advance := ih mid.state edge.1 (clean ∘ edge.2.2) (fun t p => boundary t (.more first cont stop p)) out after
        change mid.oracleCalls+out.oracleCalls≤_
        omega
    · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
      subst r; omega

end CommitGolfCandidate.Reconstruction.HonestCallFlow
