import CommitGolfCandidate.PhasePlain
namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
attribute [local irreducible] execute

def PricedRun (im : Image) (s u : MachineState) (steps more : Nat) : Prop := ∀ fuel coins,
  execute im (steps+fuel) s coins = do
    let z ← execute im fuel u coins
    return z.charge (steps+more) 0

theorem PairRun.priced {im s u n} (r : PairRun im s u n) : PricedRun im s u n 0 := by
  intro fuel coins;simpa only [Nat.add_zero] using r fuel coins

theorem PricedRun.next {im s t u n m a b} (h : PricedRun im s t n a) (g : PricedRun im t u m b) :
    PricedRun im s u (n+m) (a+b) := by
  intro fuel coins;rw [Nat.add_assoc,h (m+fuel) coins,g fuel coins]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def straight (s : MachineState) (ops : List Instr) := ops.foldl execInstrBr s

def readyOps : List Instr → MachineState → Prop
  | [], _ => True
  | op::ops,s => memoryArgumentsValid s op=true ∧ readyOps ops (execInstrBr s op)

theorem ready_congr (a b : MachineState) (h : Rel a b) (op : Instr) (pool : op∈plainOps) :
    memoryArgumentsValid a op=memoryArgumentsValid b op := by
  have regs (r : Reg) (safe : r≠.x31 := by decide) := h.reg r safe
  simp only [plainOps,List.mem_cons,List.not_mem_nil,or_false] at pool
  rcases pool with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [memoryArgumentsValid,memAccess,regs .x7,regs .x8]

theorem plain_ordinary (s : MachineState) (op : Instr) (pool : op∈plainOps)
    (ready : memoryArgumentsValid s op=true) : ordinaryStep s (.base op)=some (execInstrBr s op) := by
  simp only [plainOps,List.mem_cons,List.not_mem_nil,or_false] at pool
  rcases pool with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [ordinaryStep,ready,↓reduceIte]

theorem straight_run (im : Image) (ops : List Instr) (old actual : MachineState)
    (rel : Rel old actual) (ready : readyOps ops old) (pool : ∀ op∈ops, op∈plainOps)
    (fetches : ∀ j (inside : j<ops.length) (s : MachineState), s.pc=actual.pc+addr (4*j) →
      fetch im s=some (.base ops[j])) :
    PricedRun im actual (straight actual ops) ops.length (extraOps ops) ∧ Rel (straight old ops) (straight actual ops) ∧
    (straight actual ops).pc=actual.pc+addr (4*ops.length) := by
  induction ops generalizing old actual with
  | nil =>
    refine ⟨?_,rel,?_⟩
    · intro fuel coins;simp [straight,extraOps,Execution.charge]
    · simp [straight,addr]
  | cons op ops ih =>
    have atHead : op∈plainOps := pool _ (List.mem_cons_self)
    have fact := plain_rel old actual rel op atHead
    have rr : memoryArgumentsValid actual op=true := (ready_congr old actual rel op atHead).symm.trans ready.1
    have hw : PricedRun im actual (execInstrBr actual op) 1 (surcharge op) := by
      intro fuel coins
      have f : fetch im actual=some (.base op) := by
        have ff:=fetches 0 (by simp) actual (by simp [addr])
        exact ff.trans (congrArg (fun x : Instr => some (Instruction.base x)) (show (op::ops)[0]=op by rfl))
      have step:=CommitGolfCandidate.execute_ordinary_step im _ _ _ fuel coins f (plain_ordinary _ _ atHead rr)
      simpa [fact.2.2,Nat.add_comm 1 fuel] using step
    have shift (j : Nat) : (execInstrBr actual op).pc+addr (4*j)=actual.pc+addr (4*(j+1)) := by
      rw [fact.2.1,Nat.mul_succ]
      unfold addr
      rw [BitVec.ofNat_add]
      change actual.pc+BitVec.ofNat 64 4+BitVec.ofNat 64 (4*j)=actual.pc+(BitVec.ofNat 64 (4*j)+BitVec.ofNat 64 4)
      ac_rfl
    have ⟨tail,similar,pc⟩:=ih _ _ fact.1 ready.2 (fun x h => pool x (List.mem_cons_of_mem _ h))
      (fun j hj s atPC => by
        have q := fetches (j+1) (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj) s (atPC.trans (shift j))
        simpa only [List.getElem_cons_succ] using q)
    exact ⟨by simpa only [straight,List.foldl_cons,List.length_cons,extraOps,Nat.add_comm 1] using hw.next tail,
      similar,pc.trans (shift ops.length)⟩

theorem lifted_run (pi : Image) (p : Fin 4) (ops : List Instr) (base : Nat)
    (inside : opsDecoded p ops base=true) (low : 761≤base) (high : base+ops.length≤2680)
    (old actual : MachineState) (entry : actual.pc=addr (4096+4*base)) (rel : Rel old actual)
    (ready : readyOps ops old) (pool : ∀ op∈ops, op∈plainOps) :
    PricedRun (stitched pi) actual (straight actual ops) ops.length (extraOps ops) ∧ Rel (straight old ops) (straight actual ops) ∧
    (straight actual ops).pc=addr (4096+4*(base+ops.length)) := by
  have go:=straight_run (stitched pi) ops old actual rel ready pool
    (fun j h s atPC => decoded_rows pi p ops base j inside h low high s (by
      rw [atPC,entry];unfold addr; rw [←BitVec.ofNat_add]; congr 1 <;> omega))
  refine ⟨go.1,go.2.1,go.2.2.trans ?_⟩
  rw [entry];unfold addr;rw [←BitVec.ofNat_add];congr 1 <;> omega

#print axioms lifted_run
end TwoPermutationPrototype.PhaseOpening
