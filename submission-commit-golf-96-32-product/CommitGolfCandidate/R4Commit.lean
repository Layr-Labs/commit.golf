import CommitGolfCandidate.R4Layers
import CommitGolfCandidate.R4Start
import CommitGolfCandidate.R4Root
import CommitGolfCandidate.LateTrapdoor
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
open Late (nodeAddress levelCount sharedSaltAddr pcAt slice)

private theorem readSlice (s : MachineState) (a n : Nat) (lo : C_TD≤a) (hi : a+n≤7650414624) :
    slice (readBuffer s C_TD 3355443200) a n=readBuffer s a n := by
  unfold slice
  exact (read_buffer_slice s C_TD 3355443200 (a-C_TD) n (by dsimp [C_TD] at *;omega)).trans
    (congrArg (fun x=>readBuffer s x n) (show C_TD+(a-C_TD)=a by omega))

set_option maxRecDepth 10000 in
private theorem totals : total layerSteps 24=39852732 ∧ total layerCycles 24=118146486 ∧ total nodes 24=11184822 := by decide +kernel

def modelTree (o : Oracle) (m : Message) (r : Coins) := S4Hiding.tree o.compression m (pairSalts r)
structure Final (o : Oracle) (m : Message) (r : Coins) (s : MachineState) : Prop where
  root : readBuffer s C_CMT 32=Late.node (modelTree o m r) LOG_LENGTH 0
  trapdoor : Late.TrapdoorAgrees (readBuffer s C_TD 3355443200) (modelTree o m r) (pairSalts r)

private theorem finishProof (o : Oracle) (m : Message) (r : Coins) (s : MachineState) (seed : Seed m r s) :
    ∃ t,Final o m r t ∧ o.run (execute (submission.image .commit) (1099511627776-16778266) s true)=
      pure (⟨.success,t,789243345,78293686⟩,78293686) := by
  obtain ⟨u,leaves,lu,env,lev,gap,sa⟩:=start o m r s seed
  obtain ⟨v,stages,pv,envV,_,dst,lv,g,sl⟩:=layerChain o (baseLeaf o.compression m r) (pairSalts r) u env lu lev gap sa 24 le_rfl
  obtain ⟨t,copy,ip,mode,success,root,mem⟩:=exit o v pv (dst rfl) envV.root
  rw [totals.1,totals.2.1,totals.2.2] at stages
  have full := (leaves.trans stages).trans copy
  have atHalt:=full.finish (hasOp_sound (by decide : hasOp 262122 .ECALL) t ip) mode success 1099494849510 (by decide)
  have same (a n : Nat) (lo : C_TD≤a) (hi : a+n≤7650414624) : readBuffer t a n=readBuffer v a n :=
    mem.readBuffer_eq (by omega) (Or.inr lo)
  have node (h i : Nat) (hh : h≤24) (hi : i<levelCount h) :
      readBuffer v (nodeAddress h i) 32=Late.node (modelTree o m r) h i :=
    (lv h hh i hi).trans (Late.fixed_tree_node_all o.compression m (pairSalts r) h i hh).symm
  refine ⟨t,⟨root.trans (node 24 0 le_rfl (by decide)),⟨?_,?_,?_,?_⟩⟩,atHalt⟩
  · intro h hh i hi
    have lo : C_TD≤nodeAddress h i:=by unfold C_TD nodeAddress;omega
    have cap:=(Late.parent_below_salts h i hi).trans (by decide : Late.rowBase≤7650414624)
    exact (readSlice t _ 32 lo cap).trans ((same _ _ lo cap).trans (node h i hh hi))
  · intro i
    have bd : i.val<16777216:=i.isLt
    have inside : C_TD≤sharedSaltAddr i ∧ sharedSaltAddr i+24≤7650414624:=by unfold sharedSaltAddr Late.rowBase C_TD;omega
    exact (readSlice t _ _ inside.1 inside.2).trans ((same _ _ inside.1 inside.2).trans (sl i))
  · intro h p k pad
    have lo : C_TD≤Late.unusedSlotAddr h p k:=by unfold Late.unusedSlotAddr Late.rowAddress C_TD;omega
    have hi:=(Late.padValid h p k pad).trans (by decide : Late.rowBase≤7650414624)
    exact (readSlice t _ _ lo hi).trans ((same _ _ lo hi).trans (g h p k pad))
  · intro h hh j outside
    exact (Late.fixed_tree_node_all o.compression m (pairSalts r) h j hh).trans (Late.missing_node _ _ _ _ outside)

def endExec (s : MachineState) : Execution := ⟨.success,s,847964651,78293686⟩

set_option maxRecDepth 8000
attribute [local irreducible] execute
private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : (Fin (LENGTH / 2) → PairRand) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (16778266 + (submission.steps .commit - 16778266))
        (submission.initialState .commit message) true) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58721306 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 16778266) (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute (submission.image .commit) (submission.steps .commit - 16778266) (post0 rand) true) =
      pure (⟨.success, finalState rand, 789243345, 78293686⟩, 78293686)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 847964651, oracleCalls := 78293686 } : Execution), 78293686)) := by
  have hsteps_commit : submission.steps .commit = 16778266 + (submission.steps .commit - 16778266) := by
    have hge : 16778266 ≤ submission.steps .commit := by decide
    omega
  rw [submission_run_commit submission message, hsteps_commit]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 789243345, oracleCalls := 78293686 } : Execution).charge 58721306 0, 78293686) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 847964651, oracleCalls := 78293686 } : Execution), 78293686) := by
    unfold Execution.charge; dsimp only
  rw [heq]


private theorem seedDraw (o : Oracle) (m : Message) (extra : Nat) :
    ∃ init : Coins→MachineState,
      (o.run (execute (submission.image .commit) (16778266+extra) (submission.initialState .commit m) true) =ᵈ
        (($ᵗ Coins) >>= fun r=>(fun x : Execution×Nat=>(x.1.charge 58721306 0,x.2)) <$> o.run (execute (submission.image .commit) extra (init r) true))) ∧
      ∀ r, Seed m r (init r) := by
  obtain ⟨init,run,ok⟩:=commit_phase0 o m extra
  refine ⟨init,run,?_⟩;intro r
  obtain ⟨pc,db,mode,msg,td,i,w,k,row,e,rt,sa,mem⟩:=ok r
  exact ⟨pc,db,mode,msg,td,i,w,k,row,e,rt,sa,mem⟩

theorem commitExact (o : Oracle) (m : Message) :
    ∃ state : Coins→MachineState,(o.run (submission.run .commit m) =ᵈ
      (($ᵗ Coins) >>= fun r=>pure (endExec (state r),78293686))) ∧ ∀ r,Final o m r (state r) := by
  obtain ⟨init,draw,seeds⟩:=seedDraw o m (submission.steps .commit-16778266)
  have det (r : Coins) := finishProof o m r (init r) (seeds r)
  let st (r : Coins) := (det r).choose
  have suffix (r : Coins) : o.run (execute (submission.image .commit) (submission.steps .commit-16778266) (init r) true)=pure (⟨.success,st r,789243345,78293686⟩,78293686) := by
    rw [show submission.steps .commit=1099511627776 by rfl]
    exact (det r).choose_spec.2
  exact ⟨st,commit_run_eq_helper o m init st draw suffix,fun r=>(det r).choose_spec.1⟩
end CommitGolfCandidate.R4
