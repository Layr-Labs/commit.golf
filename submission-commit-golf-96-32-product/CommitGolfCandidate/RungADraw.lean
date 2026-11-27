import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute readBuffer

theorem draw (o : Oracle) (m : Message) (extra : Nat) :
    ∃ init : Tape→MachineState,
      (o.run (execute (R4.submission.image .commit) (16778266+extra) (R4.submission.initialState .commit m) true) =ᵈ
        (($ᵗ Tape) >>= fun r=>(fun x : Execution×Nat=>(x.1.charge 58721306 0,x.2)) <$> o.run (execute (R4.submission.image .commit) extra (init r) true))) ∧
      ∀ r, AfterDraw m r (init r) := by
  obtain ⟨init,run,ok⟩:=R4.commit_phase0 o m extra
  refine ⟨init,run,?_⟩;intro r
  obtain ⟨pc,db,mode,msg,td,c,w,k,row,e,rt,sa,mem⟩:=ok r
  exact ⟨pc,db,mode,msg,td,c,w,k,row,e,rt,fun j=>(sa j).1,fun j=>(sa j).2,mem⟩

end CommitGolfCandidate.RungA
