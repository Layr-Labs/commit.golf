import CommitGolfCandidate.TruncFlow
import CommitGolfCandidate.ParentRefinement
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 9000
set_option maxHeartbeats 220000

def advance (n : Nat) (s : MachineState) (v : Digest) :=
  nextState n (laneState (bank n) s (31-lane n) v)

def parentProgram : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | q+1,s => do
    let v ← World.query (.inr (parentQuery s (31-lane (q+1))))
    parentProgram q (advance (q+1) s v)

theorem advanceFrame (q : Nat) (pos : 0<q) (s : MachineState) (v : Digest) (f : ParentFrame q s) :
    ParentFrame (q-1) (advance q s v) :=
  nextFrame q pos _ (laneFrame _ s _ v q f.toRegFrame)

private theorem afterPC (q : Nat) (s : MachineState) (v : Digest) (f : ParentFrame q s) :
    (laneState (bank q) s (31-lane q) v).pc=loc (word q+bodySteps q) := by
  rw [lanePC,f.pc,correctBankMask]
  by_cases m : masked q
  · simp only [m,decide_true,ite_true,bodySteps];unfold loc;exact ofNat64_add_eq _ 16 _ (by omega)
  · simp only [m,decide_false,Bool.false_eq_true,ite_false,bodySteps];unfold loc;exact ofNat64_add_eq _ 12 _ (by omega)

theorem parent_exec (q : Nat) (small : q<2^24) (s : MachineState) (f : ParentFrame q s) (fuel : Nat) :
    execute (submission.image .commit) (treeSteps q+fuel) s true =
      (do let t←parentProgram q s
          let r←execute (submission.image .commit) fuel t true
          return r.charge (treeSteps q+7*q) q) := by
  induction q generalizing s with
  | zero => simp [parentProgram,treeSteps,threshold,Execution.charge]
  | succ q ih =>
    let n:=q+1
    have pos : 0<n := by omega
    have pc : s.pc=loc (startWord (bank n) (lane n)) := by
      have fp : s.pc=loc (word n) := f.pc
      rwa [word,if_neg (by omega : n≠0)] at fp
    have core := runLane s (bank n) (lane n) (laneIn n pos) pc f.r5 f.r11 f.r13 (validLane n small s f.toRegFrame)
    have length : (if projectedBank (bank n) then 4 else 3)=bodySteps n := by rw [correctBankMask];simp [bodySteps]
    have price : (if projectedBank (bank n) then 11 else 10)=bodySteps n+7 := by rw [correctBankMask];by_cases m : masked n <;> simp [bodySteps,m]
    rw [length,price] at core
    have spec (a : Digest) := runSuffix (laneState (bank n) s (31-lane n) a) n pos small (afterPC n s a f)
      (laneFrame _ _ _ _ n f.toRegFrame)
    have k : treeSteps (q+1)+fuel=bodySteps n+(suffixSteps n+(treeSteps q+fuel)) := by dsimp only [n];rw [totalSucc];omega
    rw [k,core]
    simp only [parentProgram,bind_assoc]
    apply bind_congr
    intro a
    change Digest at a
    have recur:=ih (by omega) (advance n s a) (advanceFrame n pos s a f)
    rw [spec a (treeSteps q+fuel) true]
    simp only [advance] at recur
    rw [recur]
    have sums (r : Execution) :
        ((r.charge (treeSteps q+7*q) q).charge (suffixSteps n) 0).charge (bodySteps n+7) 1 =
        r.charge (treeSteps (q+1)+7*(q+1)) (q+1) := by
      rw [totalSucc]
      cases r;simp only [Execution.charge,Execution.mk.injEq,true_and,Nat.zero_add]
      dsimp only [n];constructor <;> omega
    simp only [bind_assoc,pure_bind,sums,advance] <;> rfl

def fixedParents (o : Oracle) : Nat → MachineState → MachineState
  | 0,s=>s
  | q+1,s=>fixedParents o q (advance (q+1) s (parentAnswer o s (31-lane (q+1))))

theorem parent_eval (o : Oracle) (q : Nat) (s : MachineState) :
    checkEvaluation o (parentProgram q s)=(fixedParents o q s,q) := by
  induction q generalizing s with
  | zero => exact check_evaluation_pure o s
  | succ q ih => rw [parentProgram,check_evaluation_public_bind];simp only [ih,fixedParents,Nat.add_comm 1];rfl

theorem parent_fixed_run (o : Oracle) (q : Nat) (s : MachineState) :
    o.run (parentProgram q s)=pure (fixedParents o q s,q) := by
  induction q generalizing s with
  | zero => exact oracle_run_pure _ _
  | succ q ih => rw [parentProgram,oracle_run_public_bind];simp only [ih,pure_bind,Nat.add_comm 1];rfl

theorem parent_final_frame (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) :
    ParentFrame 0 (fixedParents o q s) := by
  induction q generalizing s with
  | zero => exact f
  | succ q ih => exact ih _ (advanceFrame (q+1) (by omega) s _ f)

end CommitGolfCandidate.Trunc
