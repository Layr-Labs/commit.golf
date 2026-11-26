import CommitGolfCandidate.ReconstructedCheckLaunchBody

namespace CommitGolfCandidate.Reconstruction.CheckLaunch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckLaunchGate
set_option maxRecDepth 16000
attribute [local irreducible] execute ArtifactEncoding.decode

/-- The checker enters its lower traversal after the two actual length checks. All
other inputs return a negative status through the ABI trampoline and halt with no oracle rows. -/
theorem run (o : Oracle) (s : MachineState) (count len : Nat) (small : count≤2^24) (lengthBound : len≤8355061248)
    (pc : s.pc=addr 24) (ra : s.getReg .x1=addr 20) (stack : s.getReg .x2=W CheckLayout.fp)
    (num : s.getReg .x10=W count) (size : s.getReg .x11=W len) :
    if len%8=0 ∧ minimum count≤len then
      ∃ t,Segment o 68 s t [] ∧ CheckLaunchBody.Positive s t count len
    else ∃ n,n≤52 ∧ Reject o n s := by
  have a:=CheckLaunchGate.align o s count len pc ra stack num size
  by_cases aligned : len%8=0
  · rw [ite_eq_left aligned] at a
    obtain ⟨u,first,here,ret,sp,number,neg,bytes,memory⟩:=a
    have b:=CheckLaunchBody.run o u count len small lengthBound here ret sp number neg bytes
    by_cases enough : minimum count≤len
    · rw [ite_eq_left enough] at b
      rw [ite_eq_left (And.intro aligned enough)]
      obtain ⟨t,body,post⟩:=b
      exact ⟨t,compose first body,⟨post.registers,post.x5,post.slots,fun p h=>(post.frame p h).trans (congrFun memory p)⟩⟩
    · rw [ite_eq_right enough] at b
      rw [ite_eq_right (fun h=>enough h.2)]
      exact ⟨52,by decide,extend first b⟩
  · rw [ite_eq_right aligned] at a
    rw [ite_eq_right (fun h=>aligned h.1)]
    exact ⟨9,by decide,a⟩
end CommitGolfCandidate.Reconstruction.CheckLaunch

