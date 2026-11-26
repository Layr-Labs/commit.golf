import CommitGolfCandidate.R1bParentRun
namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] execute writeBits

private theorem ip_succ (n : Nat) : ip (n+1)=ip n+4 := by
  unfold ip
  rw [show 4096+4*(n+1)=4096+4*n+4 by omega,BitVec.ofNat_add] <;> rfl

theorem fetchLane (slot k : Nat) (hs : slot<1024) (hk : k<6) (s : MachineState)
    (pc : s.pc=ip (4125+6*slot+k)) :
    fetch packedWideCommitImage s=some (.base (narrowOps[k]?.getD .EBREAK)) := by
  have dec:= decodedBlock (slot/64) (by omega) true
    ⟨slot%64,by omega⟩ ⟨k,hk⟩
  change Manifest.decodeBase (packed_wideCodeWord (4125+6*(64*(slot/64)+slot%64)+k))=some narrowOps[k] at dec
  rw [show 64*(slot/64)+slot%64=slot by omega] at dec
  have word : Manifest.decodeBase (packed_wideCodeWord (4125+6*slot+k))=some (narrowOps[k]?.getD .EBREAK) := by
    rw [List.getElem?_eq_getElem (show k<narrowOps.length from hk)];exact dec
  exact packed_wide_fetch_decoded s (4125+6*slot+k) (by omega) pc _ word

theorem narrowSuffix {s : MachineState} {n slot : Nat} (v : BitVec 256) (hn : n<8388608)
    (hs : slot<1024) (regs : ParentRegs s n) (pc : s.pc=ip (4125+6*slot)) (fuel : Nat) :
    let raw:=parentWritten s n v
    execute packedWideCommitImage (5+fuel) raw true =
    (do let out ← execute packedWideCommitImage fuel (suffixState raw 5) true
        return out.charge 5 0) := by
  let raw:=parentWritten s n v
  let addr:=8*treeWord n+28
  have here : raw.pc=s.pc+4 := written_pc .. 
  have hereK (k : Nat) (hk : k<5) :
      (suffixState raw k).pc=ip (4125+6*slot+(k+1)) := by
    have start : raw.pc=ip (4125+6*slot+1) := here.trans ((congrArg (·+4) pc).trans (ip_succ _).symm)
    interval_cases k
    · exact start
    · change raw.pc+4=_;rw [start,←ip_succ] <;> rfl
    · change raw.pc+4+4=_;rw [start,←ip_succ,←ip_succ] <;> rfl
    · change raw.pc+4+4+4=_;rw [start,←ip_succ,←ip_succ,←ip_succ] <;> rfl
    · change raw.pc+4+4+4+4=_;rw [start,←ip_succ,←ip_succ,←ip_succ,←ip_succ] <;> rfl
  have limit : addr+4≤MEMORY_BYTES := by dsimp [addr,treeWord,MEMORY_BYTES];omega
  have ok (j : Nat) (h : j=2 ∨ j=4) : accessValid (BitVec.ofNat 64 addr) j=true := by
    have mem : MEMORY_BYTES<2^64 := by decide
    rcases h with rfl|rfl <;> simp [accessValid,rangeValid,Nat.mod_eq_of_lt (by omega : addr<2^64),
      show addr%2=0 by dsimp [addr];omega,show addr%4=0 by dsimp [addr];omega] <;> omega
  have a : raw.getReg .x12+signExtend12 28=BitVec.ofNat 64 addr := narrowPtr s n v regs
  have load : accessValid (raw.getReg .x12+signExtend12 28) 2=true := by rw [a];exact ok _ (Or.inl rfl)
  have store : accessValid (raw.getReg .x12+signExtend12 28) 4=true := by rw [a];exact ok _ (Or.inr rfl)
  apply execute_unit_steps (states:=suffixState raw)
  intro k hk
  refine ⟨.base (narrowOps[k+1]?.getD .EBREAK),fetchLane slot _ hs (by omega) _ (hereK k hk),?_,?_⟩
  · interval_cases k
    · change (if accessValid (raw.getReg .x12+signExtend12 28) 2 then some _ else none)=_
      rw [load] <;> rfl
    · rfl
    · change (if accessValid (raw.getReg .x12+signExtend12 28) 4 then some _ else none)=_
      rw [store] <;> rfl
    · rfl
    · rfl
  · interval_cases k <;> rfl

end TwoPermutationPrototype.RV64.R1bParents
