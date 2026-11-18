import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.MaterializedManifest
import CommitGolfCandidate.TwoPermutationInputWords

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxHeartbeats 1300000
set_option maxRecDepth 18000

abbrev actual := MaterializedArtifact.submission

theorem actual_layout : OpeningLayout actual := ⟨rfl,rfl,rfl,rfl⟩

def virtualTd (s : MachineState) : BitVec (8*actual.sizes.trapdoor) := readBuffer s trapdoorBase actual.sizes.trapdoor

theorem word_at (s : MachineState) (a : Nat) (aligned : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  obtain ⟨w,rfl⟩ : ∃ w, a=8*w := ⟨a/8,by omega⟩
  exact read_word s w

theorem virtual_slice (s : MachineState) (off bytes : Nat) (room : off+bytes≤actual.sizes.trapdoor) :
    (virtualTd s).extractLsb' (8*off) (8*bytes)=readBuffer s (trapdoorBase+off) bytes :=
  read_buffer_slice s trapdoorBase _ off bytes room

private theorem outside_td (t t' : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (a : Nat)
    (lo : trapdoorBase+trapdoorBytes ≤ a) :
    inputByte actual .opening (t,p) a=inputByte actual .opening (t',p) a := by
  have gon : ¬(actual.layout.trapdoor≤a ∧ a<actual.layout.trapdoor+(8*actual.sizes.trapdoor+7)/8) := by
    rw [actual_layout.trapdoor,actual_layout.trapdoorSize];omega
  simp only [inputByte,Submission.inputBuffers,fixedBuffer,List.find?_cons,gon,decide_false,Bool.false_eq_true,ite_false]

/-- All aligned words that the original opener can load agree with a fresh load of the
materialized trapdoor. Unused indices and the gap between the private state and proof are framed. -/
theorem virtual_input (t : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (s : MachineState)
    (h : ∀ a, trapdoorBase+trapdoorBytes ≤ a → a<proofBase → a%8=0 →
      s.getMem (BitVec.ofNat 64 a)=(actual.initialState .opening (t,p)).getMem (BitVec.ofNat 64 a)) :
    SameOpeningInput (actual.initialState .opening (virtualTd s,p)) s := by
  intro a lo hi alg
  have ram : proofBase<2^64 := by decide
  by_cases td : a<trapdoorBase+trapdoorBytes
  · let off:=a-trapdoorBase
    have asOffset : trapdoorBase+off=a := by dsimp [off];omega
    have room : off+8≤trapdoorBytes := by
      have al : trapdoorBase%8=0 := by decide
      have sz : trapdoorBytes%8=0 := by decide
      dsimp [off];omega
    rw [←word_at _ _ alg,←word_at _ _ alg,←asOffset,input_trapdoor_slice actual actual_layout _ p off 8 room,
      virtual_slice s off 8 (by rwa [actual_layout.trapdoorSize])]
  · rw [h a (by omega) hi alg,initial_input_word actual .opening (t,p) a (by omega),
      initial_input_word actual .opening (virtualTd s,p) a (by omega)]
    apply congrArg (BitVec.ofNat 64);apply Finset.sum_congr rfl
    intro j hj;rw [outside_td t (virtualTd s) p _ (by omega)]

end TwoPermutationPrototype.GroupedOpening
