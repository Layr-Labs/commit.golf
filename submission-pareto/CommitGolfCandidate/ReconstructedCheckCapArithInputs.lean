import CommitGolfCandidate.ReconstructedCheckCapArith

namespace CommitGolfCandidate.Reconstruction.CheckCapArithInputs
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningOps CheckCapArith
set_option maxRecDepth 16000
set_option maxHeartbeats 900000

def reads : E→List Reg
  | .op (.lui _) => []
  | .op (.addi a _) | .op (.andi a _) | .op (.slli a _) | .op (.srli a _) | .op (.xori a _)
  | .addiw a _ | .srliw a _ => [a]
  | .op (.add a b) | .op (.sub a b) | .op (.subw a b) | .op (.and a b) | .op (.or a b)
  | .op (.xor a b) | .op (.sll a b) | .op (.srl a b) | .op (.mul a b) | .op (.mulhu a b)
  | .op (.sltu a b) | .sllw a b => [a,b]

def Agrees (r t : Reg→Word) (known : List Reg) := ∀ q∈known,r q=t q

private theorem equation (r t : Reg→Word) (e : E) (same : Agrees r t (reads e)) : e.value r=e.value t := by
  cases e with
  | op e=>
    cases e with
    | lui=>rfl
    | addi a _ | andi a _ | slli a _ | srli a _ | xori a _=>
      have eq:=same a (by simp [reads]);simp only [E.value,Expr.eval,eq]
    | add x y | sub x y | subw x y | and x y | or x y | xor x y | sll x y | srl x y | mul x y | mulhu x y | sltu x y=>
      have a:=same x (by simp [reads]);have b:=same y (by simp [reads]);simp only [E.value,Expr.eval,a,b]
  | addiw a i | srliw a i=>simp only [E.value,same a (by simp [reads])]
  | sllw a b=>simp only [E.value,same a (by simp [reads]),same b (by simp [reads])]

def ready (known : List Reg) : List Line → Bool
  | []=>true
  | (rd,e)::rest=>decide (rd≠.x0) && (reads e).all (fun q=>known.contains q) && ready (rd::known) rest
def finish (known : List Reg) : List Line→List Reg
  | []=>known
  | (rd,_)::rest=>finish (rd::known) rest

theorem agree (r t : Reg→Word) (ops : List Line) (known : List Reg) (old : Agrees r t known)
    (valid : ready known ops=true) : Agrees (regs r ops) (regs t ops) (finish known ops) := by
  induction ops generalizing r t known with
  | nil=>exact old
  | cons x xs ih=>
    obtain ⟨rd,e⟩:=x
    simp only [ready,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at valid
    have value:=equation r t e (fun q h=>old q (valid.1.2 q h))
    have extended : Agrees (update r (rd,e)) (update t (rd,e)) (rd::known) := by
      intro v hv
      rcases List.mem_cons.mp hv with same|prior
      · subst v;simp [update,valid.1.1,value]
      · by_cases same : v=rd
        · subst v;simp [update,valid.1.1,value]
        · simp [update,same,old v prior]
    exact ih _ _ _ extended valid.2

end CommitGolfCandidate.Reconstruction.CheckCapArithInputs
