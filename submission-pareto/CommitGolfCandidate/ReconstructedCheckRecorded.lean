import CommitGolfCandidate.ReconstructedBindingTrace
import CommitGolfCandidate.ReconstructedCommitParentsCall

namespace CommitGolfCandidate.Reconstruction.CheckRecorded
open CommitGolf CommitGolf.Riscv OracleComp RiscvZkvm.Rv64 Binding Binding.Machine
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- A checker segment produces its actual ordered public-oracle rows and
leaves an exact continuation for every remaining fuel amount. -/
def Segment (o : Oracle) (steps : Nat) (s t : MachineState) (rows : List PublicRow) :=
  ∃ c, ∀ fuel,
    observation o (steps+fuel) s =
      (((observation o fuel t).1.1.charge c rows.length,rows ++ (observation o fuel t).1.2),
        rows.length+(observation o fuel t).2)

theorem empty (o : Oracle) (s : MachineState) : Segment o 0 s s [] := by
  refine ⟨0,fun n=>?_⟩
  simp [Execution.charge]

theorem compose {o : Oracle} {n m : Nat} {s t u : MachineState} {rs qs : List PublicRow}
    (a : Segment o n s t rs) (b : Segment o m t u qs) : Segment o (n+m) s u (rs++qs) := by
  obtain ⟨c,a⟩ := a
  obtain ⟨p,b⟩ := b
  refine ⟨c+p,fun n=>?_⟩
  rw [Nat.add_assoc,a,b]
  simp [Execution.charge,List.append_assoc,Nat.add_assoc]

theorem plain (o : Oracle) (s t : MachineState) (op : Instruction)
    (fetch : fetch image s=some op) (exactStep : ordinaryStep s op=some t) : Segment o 1 s t [] := by
  refine ⟨instructionCycles op,fun fuel=>?_⟩
  have h := Binding.Machine.step_ordinary o s t 1 (instructionCycles op)
    (fun fuel => by rw [Nat.one_add];exact execute_ordinary_step image op s t fuel false fetch exactStep) fuel
  simpa using h

theorem trace (o : Oracle) (s : MachineState) (xs : Trace) (decoded : Decoded xs) (ok : valid xs s=true) :
    Segment o xs.length s (last xs s) [] := by
  exact ⟨cycles xs,fun fuel=>by simpa using trace_observation o xs s fuel decoded ok⟩

theorem call (o : Oracle) (site : Fin 6) (s : MachineState) (q : PublicSpec.Domain)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*oracleSite site)) (sel : s.getReg .x5=0)
    (input : oracleInput s=some q) :
    let a := o.answer (m:=Id) q
    Segment o 1 s (writeOracleAnswer s (s.getReg .x12) q a) (queryRows (.inr q) a) := by
  have size : (queryRows (.inr q) (o.answer (m:=Id) q)).length=1 := by
    rcases q with q|q|q <;> rfl
  refine ⟨oracleCycles q,fun fuel=>?_⟩
  rw [Nat.one_add,size]
  exact step_oracle o site s fuel q pc sel input

theorem compress (o : Oracle) (site : Fin 6) (s : MachineState) (src dst : Nat) (key : Key)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*oracleSite site))
    (srcRoom : src+64≤MEMORY_BYTES) (dstRoom : dst+32≤MEMORY_BYTES)
    (srcA : src%8=0) (dstA : dst%8=0) (read : readBuffer s src 64 = encodeKey key)
    (regs : s.getReg .x5=0 ∧ s.getReg .x10=BitVec.ofNat 64 src ∧ s.getReg .x11=64 ∧
      s.getReg .x12=BitVec.ofNat 64 dst ∧ s.getReg .x13=0) :
    let t := CommitParents.callAfter s o dst key
    Segment o 1 s t [.compression (encodeKey key) (o.compression (encodeKey key))] ∧
    CommitParents.cell t dst=CommitParents.rawC o key ∧ CommitParents.Frame dst s t := by
  have sv : (BitVec.ofNat 64 src).toNat=src := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at srcRoom;omega)]
  have dv : (BitVec.ofNat 64 dst).toNat=dst := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at dstRoom;omega)]
  have args : oracleInput s=some (.inl (encodeKey key)) := by
    have k : (s.getReg .x13).toNat=0 := by rw [regs.2.2.2.2];rfl
    unfold oracleInput
    dsimp only
    rw [k]
    simp [regs.2.1,regs.2.2.1,regs.2.2.2.1,rangeValid,sv,dv,srcA,dstA,srcRoom,dstRoom,read,
      COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH]
  have h := call o site s (.inl (encodeKey key)) pc regs.1 args
  rw [regs.2.2.2.1] at h
  exact ⟨h,CommitParents.call_contents s o dst key (by unfold MEMORY_BYTES at dstRoom;omega)⟩

end CommitGolfCandidate.Reconstruction.CheckRecorded
