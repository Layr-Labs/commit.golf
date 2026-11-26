import CommitGolfCandidate.ReconstructedCheckCapLevelContract
import CommitGolfCandidate.ReconstructedCheckCapQuery

namespace CommitGolfCandidate.Reconstruction.CheckCapIterate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckCapLevel
open TwoPermutationPrototype.Sampling

/-- Ordered evidence retained by the checker from any upper height to acceptance or rejection. -/
inductive Trail (o : Oracle) (f : Nat→Bool) (stream : Nat) :
    Nat→Nat→MachineState→Option Nat→MachineState→List PublicRow→Prop where
  | finish (c s) (boundary : Boundary f stream 0 c s) : Trail o f stream 0 c s (some c) s []
  | stopped (k c s t log m) (base : Bases m s)
      (invalid : (parsed f (k+1) stream c m).valid=false) (halt : Rejected t) :
      Trail o f stream (k+1) c s none t log
  | level (k c s u t log tail m out) (base : Bases m s)
      (good : Passed o f stream (k+1) c s u log m)
      (rest : Trail o f stream k (parsed f (k+1) stream c m).cursor u out t tail) :
      Trail o f stream (k+1) c s out t (log++tail)

def fuel : Nat→Nat
  | 0=>0
  | k+1=>56+322*2^k+fuel k

theorem run (o : Oracle) (f : Nat→Bool) (stream : Nat) (levelRun : Contract o f stream)
    (d c : Nat) (s : MachineState) (small : d≤9) (space : c+70000*d≤70000000000)
    (ready : Boundary f stream d c s) :
    ∃ n t log out, n≤fuel d ∧ log.length≤CheckCapQuery.fee f d ∧ Segment o n s t log ∧
      Frame s t ∧ Trail o f stream d c s out t log := by
  induction d generalizing c s with
  | zero=>exact ⟨0,s,[],some c,by decide,Nat.zero_le _,empty o s,fun _ _ _=>rfl,.finish c s ready⟩
  | succ k ih=>
    obtain ⟨n,u,log,m,cost,queries,segment,frame,bases,invalid|pass⟩:=
      levelRun (k+1) c s (by omega) small space ready
    · exact ⟨n,u,log,none,cost.trans (Nat.le_add_right _ _),queries.trans (Nat.le_add_right _ _),
        segment,frame,.stopped k c s u log m bases invalid.1 invalid.2⟩
    · have room : (parsed f (k+1) stream c m).cursor+70000*k≤70000000000:=by
        have := pass.cursor
        omega
      obtain ⟨n',t,tail,out,cost',queries',segment',frame',rest⟩:=
        ih _ u (by omega) room pass.boundary
      exact ⟨n+n',t,log++tail,out,Nat.add_le_add cost cost',
        by rw [List.length_append];exact Nat.add_le_add queries queries', compose segment segment',
        fun q h a=>(frame' q h a).trans (frame q h a),.level k c s u t log tail m out bases pass rest⟩

def Endpoint (f : Nat→Bool) (stream : Nat) (t : MachineState) (out : Option Nat) : Prop :=
    match out with
    | none=>Rejected t
    | some cursor=>Boundary f stream 0 cursor t

theorem endState {o f stream d c s out t log} (tr : Trail o f stream d c s out t log) :
    Endpoint f stream t out := by
  induction tr with
  | finish _ _ b=>exact b
  | stopped _ _ _ _ _ _ _ _ h=>exact h
  | level _ _ _ _ _ _ _ _ _ _ _ _ ih=>exact ih

theorem nine (o : Oracle) (ps : Positions) (stream c : Nat) (s : MachineState)
    (levelRun : Contract o (CapEntry.flags ps) stream) (space : c+630000≤70000000000)
    (ready : Boundary (CapEntry.flags ps) stream 9 c s) :
    ∃ n t log out, n≤165046 ∧ log.length≤2303 ∧ log.length≤16*ps.card ∧ Segment o n s t log ∧
      Frame s t ∧ Trail o (CapEntry.flags ps) stream 9 c s out t log := by
  obtain ⟨n,t,log,out,cost,queries,seg,frame,trail⟩:=run o _ stream levelRun 9 c s (by decide) space ready
  exact ⟨n,t,log,out,cost,queries.trans (CheckCapQuery.at_positions ps).1,
    queries.trans (CheckCapQuery.at_positions ps).2,seg,frame,trail⟩

end CommitGolfCandidate.Reconstruction.CheckCapIterate

