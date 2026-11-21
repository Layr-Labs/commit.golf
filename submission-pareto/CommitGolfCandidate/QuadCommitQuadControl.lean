import CommitGolfCandidate.QuadCommitQuadRun

namespace TwoPermutationPrototype.Quad.Commit.Quads
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
attribute [local irreducible] image leafCode quadCode quad2Code quad3Code parentCode decodeInstruction execute

private theorem fetch_latch (part : Fin 2) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (381552+4*part.val)) :
    fetch image s=some (.base (if part.val=0 then .BEQ .x12 .x21 8 else .JAL .x0 1900540)) := by
  apply fetch_code_index s (94364+part.val) (by have := part.isLt;omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at (quadPrefix++quadCode) quadLatchWords
    (quad2SetupWords++quad2Code++quadLatchWords++quad3SetupWords++quad3Code++quadLatchWords++
      parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image quadPrefix;simp only [List.append_assoc]) part.val part.isLt
  rw [List.length_append,quad_prefix_length,quad_code_length] at atIndex
  change image.code[94364+part.val]?=_ at atIndex
  rw [atIndex]
  fin_cases part <;> change decodeInstruction _=some (.base _) <;> unfold decodeInstruction <;> rfl

def nextPC (g : Nat) : Word := if g=2^22 then 381560 else 184944
def latchCost (g : Nat) := if g=2^22 then 1 else 2

attribute [local irreducible] nextPC latchCost

theorem latch_run (s : MachineState) (g fuel : Nat) (bound : g≤2^22) (r : Regs s g)
    (pc : s.pc=quadPC 16384 0) (stop : s.getReg .x21=wordAddress (quadSlotWord (2^22))) :
    execute image (latchCost g+fuel) s true =
      (do let out ← execute image fuel (s.setPC (nextPC g)) true
          return out.charge (latchCost g) 0) := by
  have equal : s.getReg .x12=s.getReg .x21 ↔ g=2^22 := by
    rw [r.target,stop]
    constructor
    · intro h
      have index := wordAddress_injective_of_bound (a := quadSlotWord g) (b := quadSlotWord (2^22))
        (by unfold quadSlotWord quad2GroupWord;omega) (by decide) h
      unfold quadSlotWord quad2GroupWord at index;omega
    · rintro rfl;rfl
  by_cases last : g=2^22
  · have step : ordinaryStep s (.base (.BEQ .x12 .x21 8))=some (s.setPC 381560) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13,quadPC]
    rw [latchCost,if_pos last,nextPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_latch ⟨0,by decide⟩ s pc) step];rfl
  · let mid := s.setPC 381556
    have diff : s.getReg .x12≠s.getReg .x21 := fun h => last (equal.mp h)
    have step : ordinaryStep s (.base (.BEQ .x12 .x21 8))=some mid := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,diff,mid,quadPC]
    have jump : ordinaryStep mid (.base (.JAL .x0 1900540))=some (s.setPC 184944) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setReg,MachineState.setPC]
      rfl
    rw [latchCost,if_neg last,nextPC,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_latch ⟨0,by decide⟩ s pc) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_latch ⟨1,by decide⟩ mid rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def groups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,g,s => do
    let body ← trace 16384 g s
    groups n (g+16384) (body.setPC (nextPC (g+16384)))

attribute [local irreducible] trace groups

private theorem combined_charges (p : OracleComp World Execution) (k cost : Nat) :
    (((p >>= fun c => pure (c.charge (163842*k-1) (16384*k))) >>=
      fun b => pure (b.charge cost 0)) >>= fun a => pure (a.charge 163840 16384)) =
      (p >>= fun c => pure (c.charge (163840+cost+(163842*k-1)) (16384*(k+1)))) := by
  simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem groups_run (s : MachineState) (cnt g fuel : Nat) (limit : g+16384*cnt=2^22)
    (r : Regs s g) (pc : 0<cnt → s.pc=quadPC 0 0) (stop : s.getReg .x21=wordAddress (quadSlotWord (2^22))) :
    execute image ((49154*cnt-1)+fuel) s true =
      (do let next ← groups cnt g s
          let out ← execute image fuel next true
          return out.charge (163842*cnt-1) (16384*cnt)) := by
  induction cnt generalizing s g with
  | zero => simp [groups,Execution.charge]
  | succ k ih =>
    have step : 49154*(k+1)-1=49152+latchCost (g+16384)+(49154*k-1) ∧
        163842*(k+1)-1=163840+latchCost (g+16384)+(163842*k-1) := by
      unfold latchCost;split <;> constructor <;> omega
    rw [step.1,show 49152+latchCost (g+16384)+(49154*k-1)+fuel=
      3*16384+(latchCost (g+16384)+((49154*k-1)+fuel)) by omega,
      sequence_run s 16384 g 0 _ (by omega) (by decide) (by omega) r (pc (by omega))]
    simp only [groups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    obtain ⟨rs,here,keep⟩ := sequence_post s 16384 g 0 r (pc (by omega)) reached
    rw [latch_run body (g+16384) _ (by omega) rs here
      ((keep .x21 (by decide) (by decide)).trans stop)]
    let next := body.setPC (nextPC (g+16384))
    have regs : Regs next (g+16384) := regs_setPC body (g+16384) _ rs
    have again (positive : 0<k) : next.pc=quadPC 0 0 := by
      dsimp only [next,MachineState.setPC]
      rw [nextPC,if_neg (by omega)];rfl
    rw [ih next (g+16384) (by omega) regs again
      ((keep .x21 (by decide) (by decide)).trans stop),step.2]
    simpa only [bind_assoc] using combined_charges
      (groups k (g+16384) next >>= fun state => execute image fuel state true) k (latchCost (g+16384))

theorem groups_post (s : MachineState) (cnt g : Nat) (limit : g+16384*cnt=2^22)
    (r : Regs s g) (pc : 0<cnt → s.pc=quadPC 0 0) {out : MachineState}
    (hit : out ∈ support (groups cnt g s)) :
    Regs out (2^22) ∧ (0<cnt → out.pc=381560) ∧
      ∀ reg, .x10≠reg → .x12≠reg → out.getReg reg=s.getReg reg := by
  induction cnt generalizing s g with
  | zero =>
    simp only [groups,support_pure,Set.mem_singleton_iff] at hit;subst out
    refine ⟨?_,by omega,fun _ _ _ => rfl⟩
    have eq : g=2^22 := by omega
    rw [←eq];exact r
  | succ k ih =>
    simp only [groups,mem_support_bind_iff] at hit
    obtain ⟨body,reach,tail⟩ := hit
    obtain ⟨rs,here,keep⟩ := sequence_post s 16384 g 0 r (pc (by omega)) reach
    let next := body.setPC (nextPC (g+16384))
    have regs : Regs next (g+16384) := regs_setPC body (g+16384) _ rs
    have again (positive : 0<k) : next.pc=quadPC 0 0 := by
      dsimp only [next,MachineState.setPC]
      rw [nextPC,if_neg (by omega)];rfl
    obtain ⟨done,finish,rest⟩ := ih next (g+16384) (by omega) regs again tail
    refine ⟨done,fun _ => ?_,fun reg a b => (rest reg a b).trans (keep reg a b)⟩
    cases k with
    | zero =>
      simp only [groups,support_pure,Set.mem_singleton_iff] at tail
      rw [tail];change nextPC (g+16384)=381560
      rw [nextPC,if_pos (by omega)]
    | succ k => exact finish (by omega)

end TwoPermutationPrototype.Quad.Commit.Quads
