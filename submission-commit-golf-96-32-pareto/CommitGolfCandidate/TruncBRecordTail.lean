import CommitGolfCandidate.TruncBFill
import CommitGolfCandidate.TruncUpper
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 300000

def afterTest (b : MachineState) := execInstrBr b (.BEQ .x7 .x0 56)
def nextEdge (s : MachineState) := execInstrBr (recordNextState s) (.BNE .x27 .x0 7844)
def copied (s : MachineState) := nextEdge (storeState (afterTest (bucketState s)))
def compared (s : MachineState) :=
  nextEdge (execInstrBr (PairCap.top_checkRootWordsState (afterTest (bucketState s)) 269 4) (.JAL .x0 44))

private theorem passPC (b : MachineState) (pc : b.pc=5168) :
    (afterTest b).pc = if b.getReg .x7 = 0 then 5224 else 5172 := by
  unfold afterTest; dsimp only [execInstrBr]
  simp only [beq_iff_eq,show b.getReg .x0 = 0 from rfl]
  split <;> simp_all [pc,MachineState.setPC,signExtend13]

theorem tailPC (s : MachineState) (pc : s.pc=5264) :
    (recordNextState s).pc=5272 := by simp [recordNextState,recordNextOps,execInstrBr,pc,MachineState.setPC]

theorem storePC (s : MachineState) (pc : s.pc=5224) :
    (storeState s).pc=5264 := by simp [storeState,storeOps,execInstrBr,pc,MachineState.setPC]

attribute [local irreducible] execute bucketState storeState recordNextState PairCap.top_checkRootWordsState

theorem firstWrite (s : MachineState) (pc : s.pc=5120) (mode : s.getReg .x19≠0) (u : Fin 256)
    (index : s.getReg .x20=BitVec.ofNat 64 u.val)
    (fresh : (bucketState s).getReg .x7=0)
    (safe : safeSteps storeOps (afterTest (bucketState s))) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (29+fuel) s coins =
      (do let res ← execute (Trunc.wireImage true) fuel (copied s) coins
          return res.charge 29 0) := by
  let b := bucketState s
  have bpc : b.pc=5168 := (bucketInfo s pc u index).1
  have pass : (afterTest b).pc=5224 := by rw [passPC b bpc,if_pos fresh]
  have out := storePC (afterTest b) pass
  have latch := tailPC (storeState (afterTest b)) out
  rw [show 29+fuel=15+((10+(2+(fuel+1)))+1) by omega,bucketRun _ pc mode (bucketAccess s u index),
    edge293 b bpc]
  change (do let a ← (do let t ← execute (Trunc.wireImage true) (10+(2+(fuel+1))) (afterTest b) coins
                          return t.charge 1 0)
             return a.charge 15 0) = _
  rw [storeRun (afterTest b) pass safe (2+(fuel+1)) coins,
      recordNextRun (storeState (afterTest b)) out (fuel+1) coins,
      edge319 (recordNextState (storeState (afterTest b))) latch fuel coins]
  simp [copied,nextEdge,b,Execution.charge,← Nat.add_assoc]

theorem duplicateWrite (s : MachineState) (pc : s.pc=5120) (mode : s.getReg .x19≠0) (u : Fin 256)
    (index : s.getReg .x20=BitVec.ofNat 64 u.val) (seen : (bucketState s).getReg .x7≠0)
    (sv : ∀ j<4,accessValid ((afterTest (bucketState s)).getReg .x21+BitVec.ofNat 64 (8*j)) 8)
    (dv : ∀ j<4,accessValid ((afterTest (bucketState s)).getReg .x23+BitVec.ofNat 64 (8*j)) 8)
    (same : ∀ j<4, let b := afterTest (bucketState s)
      b.getMem (b.getReg .x21+BitVec.ofNat 64 (8*j)) = b.getMem (b.getReg .x23+BitVec.ofNat 64 (8*j)))
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (32+fuel) s coins =
      (do let res ← execute (Trunc.wireImage true) fuel (compared s) coins
          return res.charge 32 0) := by
  let b := bucketState s
  have bpc : b.pc=5168 := (bucketInfo s pc u index).1
  have pass : (afterTest b).pc=5172 := by rw [passPC b bpc,if_neg seen]
  let done := PairCap.top_checkRootWordsState (afterTest b) 269 4
  have donePc : done.pc=5220 := PairCap.top_check_root_words_pc _ 269 (Or.inl rfl) pass 4 (by decide) same
  let jump := execInstrBr done (.JAL .x0 44)
  have out : jump.pc=5264 := by simp [jump,execInstrBr,MachineState.setPC,signExtend21,donePc]
  rw [show 32+fuel=15+((12+((2+(fuel+1))+1))+1) by omega,bucketRun _ pc mode (bucketAccess s u index),edge293 b bpc]
  change (do let a ← (do let t ← execute (Trunc.wireImage true) (12+((2+(fuel+1))+1)) (afterTest b) coins
                          return t.charge 1 0)
             return a.charge 15 0) = _
  rw [Check.top_check_root_matches (afterTest b) 269 (Or.inl rfl) pass sv dv same ((2+(fuel+1))+1) coins,
      edge306 done donePc (2+(fuel+1)) coins,recordNextRun jump out (fuel+1) coins,
      edge319 (recordNextState jump) (tailPC _ out) fuel coins]
  simp [compared,nextEdge,b,jump,done,Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate.Trunc.Batch
