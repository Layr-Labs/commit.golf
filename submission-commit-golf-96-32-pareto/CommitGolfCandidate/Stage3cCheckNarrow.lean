import CommitGolfCandidate.Stage3cCheckMaskStore
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
theorem mask_low (s : MachineState) (h : Height) (pc : s.pc=pcAt 211) (w : s.getReg .x31=BitVec.ofNat 64 (wireWidth h))
    (small : wireWidth h≤238) (a : Nat) (dst : s.getReg .x12=BitVec.ofNat 64 a) (bound : a+32≤MEMORY_BYTES) (al : a%8=0) :
    let t:=writtenMask (preparedMask (pathEnd s narrowStart))
    (∀ fuel,execute (image .check) (fuel+11) s false=
      (do let out←execute (image .check) fuel t false;pure (out.charge 11 0))) ∧ t.pc=pcAt 224 ∧ t.mem=(maskedWord s a (heldMask h)).mem := by
  let q:=pathEnd s narrowStart
  let u:=preparedMask q
  obtain ⟨g,ip,eq,d,w'⟩:=narrow_guard s pc _ small w
  obtain ⟨p,ip',eq',d',mask⟩:=setup_mask q h ip (w'.trans w)
  obtain ⟨t,last,mem⟩:=write_mask_tail u a _ ip' (d'.trans (d.trans dst)) mask bound al
  refine ⟨?_,last,?_⟩
  · intro fuel
    have r₁:=path_run .check false s narrowStart narrow_sites.1 g (fuel+7)
    have r₂:=path_run .check false q maskSetup (by decide +kernel) p (fuel+3)
    have r₃:=path_run .check false u maskWrite (by decide +kernel) t fuel
    rw [show fuel+11=(fuel+7)+narrowStart.length by rfl,r₁]
    change (do let r←execute (image .check) ((fuel+3)+maskSetup.length) q false;return r.charge 4 0)=_
    rw [r₂]
    change (do let r←(do let z←execute (image .check) (fuel+maskWrite.length) u false;pure (z.charge 4 0));pure (r.charge 4 0))=_
    rw [r₃];simp only [bind_assoc,pure_bind]
    apply bind_congr;intro out;congr 1 <;> simp [Execution.charge,maskWrite] <;> omega
  · apply mem.trans
    simp only [maskedWord,MachineState.setWord32,MachineState.getHalfword,MachineState.getMem,MachineState.setMem,
      show u.mem=s.mem from eq'.trans eq]
end CommitGolfCandidate.Chained.BinaryMachine.Check
