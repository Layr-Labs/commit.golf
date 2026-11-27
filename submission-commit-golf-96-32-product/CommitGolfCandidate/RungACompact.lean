import CommitGolfCandidate.RungAComplete
import CommitGolfCandidate.RungALoop
import CommitGolfCandidate.R4Root
import CommitGolfCandidate.RungALaw
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp R4 Late
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 1700000
attribute [local irreducible] execute readBuffer DetRun

theorem fused (o : Oracle) (m : Message) (r : Tape) (s : MachineState)
    (e : Env s) (pc : s.pc=pcAt 131123) (data : Inputs o m r s) :
    ∃ t,MRun o s 79866578 t 270707424 27262978 ∧ t.pc=pcAt 238455 ∧ Env t ∧
      t.getReg .x28=16383 ∧ Ground o m r t ∧
      Upper.Levels o.compression (Kernel.baseLeaf o m r) 4 t := by
  obtain ⟨u,run,ip,mem,eu,src,dst,stride,stop⟩:=Setup.header o s pc e
  have same (a n : Nat):=readBuffer_of_mem_eq mem a n
  have init : Kernel.State o m r 0 u := by
    refine ⟨eu,src,stride,stop,(beginGround data).kept (fun a n _ _ _=>same a n)
      (fun h p k z=>(same _ _).trans ((beginGround data).gaps h p k z)),?_,fun i bad=>by omega⟩
    intro j small _
    apply (same _ _).trans;apply readBuffer_zero_of_bytes
    intro a hi;exact data.fresh _ (by dsimp [MEMORY_BYTES];omega) (Or.inl (by dsimp [C_MSG];omega))
  obtain ⟨v,bulk,edge,sv,dv⟩:=Kernel.bulk o m r u init ip dst 87381 le_rfl
  obtain ⟨w,tail,wp,sw,dw⟩:=Kernel.groups o m r v 699048 132054 2 (by decide) (by decide) (by decide)
    (fun j hj=>Kernel.restFull ⟨j,hj⟩) sv edge dv 2 le_rfl
  let c : Kernel.Layout:=⟨699050,16,nodeAddress 4 699048,96,by decide,by decide,by decide,by decide⟩
  obtain ⟨z,last,zp,sz,_⟩:=Kernel.group o m r c w 132282 false (by decide) rfl sw wp dw
    Kernel.sitesEnd.1 (hasOp_sound Kernel.sitesEnd.2)
  obtain ⟨t,done_,end_,tm,et,mask⟩:=Setup.finish o z zp sz.env
  have keep (a n : Nat):=readBuffer_of_mem_eq tm a n
  refine ⟨t,(((run.trans bulk).trans tail).trans last).trans done_,end_,et,mask,
    sz.ground.kept (fun a n _ _ _=>keep a n) (fun h j k q=>(keep _ _).trans (sz.ground.gaps h j k q)),?_⟩
  intro h lo hi i bi
  have eq : h=4:=by omega
  subst h;change i<699051 at bi;exact (keep _ _).trans (sz.roots i (by change i<699051;exact bi))

theorem compactSuffix : CompactSuffix (R4.submission.image .commit) := suffix_of_phase .compact fused

theorem compactCommitLaw : CommitLaw .twentyFour (R4.submission.image .commit) (Late.submission.image .opening) 841142282 :=
  commitLaw_of_suffix 841142282 (by decide) compactSuffix
end CommitGolfCandidate.RungA
