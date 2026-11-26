import CommitGolfCandidate.ReconstructedCheckWidth221
import CommitGolfCandidate.ReconstructedCheckWidth222
import CommitGolfCandidate.ReconstructedCheckWidth223
import CommitGolfCandidate.ReconstructedCheckWidth224
import CommitGolfCandidate.ReconstructedCheckWidth225
import CommitGolfCandidate.ReconstructedCheckWidth236
import CommitGolfCandidate.ReconstructedCheckWidth238
import CommitGolfCandidate.ReconstructedCheckWidth240

namespace CommitGolfCandidate.Reconstruction.CheckLowerPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckCursorImage
set_option maxRecDepth 26000
set_option maxHeartbeats 6000000

theorem checked (r : Fin 64) (d : Fin 15) : receipt r (lowWidth (10+d.val))=true := by
  fin_cases d
  · exact width221 r
  · exact width221 r
  · exact width221 r
  · exact width221 r
  · exact width221 r
  · exact width225 r
  · exact width222 r
  · exact width222 r
  · exact width223 r
  · exact width224 r
  · exact width236 r
  · exact width238 r
  · exact width238 r
  · exact width238 r
  · exact width240 r

theorem control_ok (r : Fin 64) (d : Fin 15) : control r (lowWidth (10+d.val)) := by
  have yes:=checked r d
  simp only [receipt,Bool.and_eq_true,decide_eq_true_eq] at yes
  exact yes.2

theorem positive (o : Oracle) (env : Env) (ctx : CheckCursorValues.Context env) (r : Fin 64) (d : Fin 15)
    (layout : Layout env (table (lowWidth (10+d.val)))) (s : MachineState) (initial : Matches env (start r) s) :
    let w:=lowWidth (10+d.val)
    ∃ t, CheckRecorded.Segment o (done r w).ticks s t [] ∧ Matches env (done r w).state t ∧
      t.pc=CommitBlocks.addr 350 ∧ (done r w).state.get .x10=CheckHeaderPlan.field r 64 ∧
      (done r w).state.get .x16=middle r 1 ∧ (done r w).state.get .x17=middle r 2 ∧
      (done r w).state.get .x6=top r w ∧ (done r w).state.get .x5=.lit (BitVec.ofNat 64 (w-192)) ∧
      (done r w).state.get .x15=.lit (BitVec.ofNat 64 w) ∧ (done r w).state.get .x24=ptr 1 (r.val+192) ∧
      (done r w).state.writes=[] ∧ (done r w).ticks≤70 := by
  let w:=lowWidth (10+d.val)
  have ok:=checked r d
  simp only [receipt,Bool.and_eq_true,decide_eq_true_eq] at ok
  have replay : run r w=some (done r w) := by
    have defn : (run r w).isSome=true:=ok.1.1
    unfold done;cases v:run r w <;> simp_all
  obtain ⟨t,seg,h,_,pc⟩:=CheckCursorOps.run_sound o env ctx (table w) layout _ lower_decoded _ 76 _ s initial
    (fun _ h=>by cases h) _ replay
  exact ⟨t,seg,h,pc,ok.1.2⟩

end CommitGolfCandidate.Reconstruction.CheckLowerPlan
