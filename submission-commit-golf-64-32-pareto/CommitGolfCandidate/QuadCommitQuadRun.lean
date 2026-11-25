import CommitGolfCandidate.QuadCommitTreeFetch
import CommitGolfCandidate.QuadCommitWindows

/-! Level-1 quad pass: node `g` reads leaf group `g` and writes its 200-byte reply at the
quad-group slot of `g`; the destination advances 32, 32, 32, 272 bytes. -/
namespace TwoPermutationPrototype.Quad.Commit.Quads
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image execute writeBits

structure Regs (s : MachineState) (g : Nat) : Prop where
  source : s.getReg .x10=wordAddress (groupWord g)
  target : s.getReg .x12=wordAddress (quadSlotWord g)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem regs_setPC (s : MachineState) (g : Nat) (pc : Word) (r : Regs s g) : Regs (s.setPC pc) g :=
  ⟨r.source,r.target,r.selector,r.size,r.primitive⟩

def after (s : MachineState) (g : Nat) (reply : BitVec 1600) :=
  execInstrBr (execInstrBr (writeBits s (wordAddress (quadSlotWord g)) reply)
    (.ADDI .x10 .x10 368)) (.ADDI .x12 .x12 (quadStride (g%4)))

def trace : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,g,s => do
    let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (groupWord g))))))) : OracleComp World (BitVec 1600))
    trace n (g+1) (after s g reply)

theorem after_pc (s : MachineState) (g : Nat) (reply : BitVec 1600) :
    (after s g reply).pc=s.pc+12 := by
  change (writeBits s _ reply).pc+4+4=_
  rw [written_pc,BitVec.add_assoc,BitVec.add_assoc]
  rfl

theorem after_reg (s : MachineState) (g : Nat) (reply : BitVec 1600) (reg : Reg)
    (source : .x10≠reg) (target : .x12≠reg) :
    (after s g reply).getReg reg=s.getReg reg := by
  simp only [after,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ source,MachineState.getReg_setReg_ne _ _ _ _ target,
    CommitGolfCandidate.writeBits_register]

theorem stride_advance (g : Nat) :
    wordAddress (quadSlotWord g)+signExtend12 (quadStride (g%4))=wordAddress (quadSlotWord (g+1)) := by
  by_cases last : g%4=3
  · rw [quadStride,if_pos last,show signExtend12 (272 : BitVec 12)=BitVec.ofNat 64 272 by rfl,
      wordAddress,←BitVec.ofNat_add]
    congr 1
    unfold quadSlotWord quad2GroupWord
    omega
  · rw [quadStride,if_neg last,show signExtend12 (32 : BitVec 12)=BitVec.ofNat 64 32 by rfl,
      wordAddress,←BitVec.ofNat_add]
    congr 1
    unfold quadSlotWord quad2GroupWord
    omega

theorem after_regs (s : MachineState) (g : Nat) (reply : BitVec 1600) (r : Regs s g) :
    Regs (after s g reply) (g+1) := by
  refine ⟨?_,?_,(after_reg s g reply .x5 (by decide) (by decide)).trans r.selector,
    (after_reg s g reply .x11 (by decide) (by decide)).trans r.size,
    (after_reg s g reply .x13 (by decide) (by decide)).trans r.primitive⟩
  · change (writeBits s _ reply).getReg .x10+signExtend12 368=_
    rw [CommitGolfCandidate.writeBits_register,r.source]
    change wordAddress (groupWord g)+BitVec.ofNat 64 368=_
    rw [wordAddress,←BitVec.ofNat_add]
    congr 1 <;> (unfold groupWord;omega)
  · change (writeBits s _ reply).getReg .x12+signExtend12 (quadStride (g%4))=_
    rw [CommitGolfCandidate.writeBits_register,r.target]
    exact stride_advance g

private theorem one_run (s : MachineState) (g : Nat) (slot : Fin 16384) (fuel : Nat)
    (bound : g<2^22) (phase : slot.val%4=g%4) (r : Regs s g) (pc : s.pc=quadPC slot.val 0) :
    execute image (3+fuel) s true =
      (do let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (groupWord g))))))) : OracleComp World (BitVec 1600))
          let out ← execute image fuel (after s g reply) true
          return out.charge 32 1) := by
  have fetched := fetch_quad slot ⟨0,by decide⟩ s pc
  rw [show 3+fuel=(fuel+2)+1 by omega,
    execute_permutation_call image (fuel+2) s true (groupWord g) (quadSlotWord g)
      (by unfold groupWord;omega) (by unfold quadSlotWord quad2GroupWord;omega) r.source r.target r.selector r.size r.primitive
      (by simpa [quadInstr] using fetched)]
  apply bind_congr_of_forall_mem_support
  intro reply _
  let written := writeBits s (wordAddress (quadSlotWord g)) reply
  let moved := execInstrBr written (.ADDI .x10 .x10 368)
  have writtenPC : written.pc=quadPC slot.val 1 := by
    dsimp only [written]
    rw [written_pc,pc]
    change BitVec.ofNat 64 (4096+4*(45212+3*slot.val+0))+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add];congr 1 <;> omega
  have movedPC : moved.pc=quadPC slot.val 2 := by
    change written.pc+BitVec.ofNat 64 4=_
    rw [writtenPC];unfold quadPC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  have f1 := fetch_quad slot ⟨1,by decide⟩ written writtenPC
  have f2 := fetch_quad slot ⟨2,by decide⟩ moved movedPC
  simp only [quadInstr,phase] at f1 f2
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ f1
    (show ordinaryStep written (.base (.ADDI .x10 .x10 368))=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ f2
    (show ordinaryStep moved (.base (.ADDI .x12 .x12 (quadStride (g%4))))=some (after s g reply) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem sequence_run (s : MachineState) (count g slot fuel : Nat) (bound : g+count≤2^22)
    (inside : slot+count≤16384) (phase : slot%4=g%4) (r : Regs s g) (pc : s.pc=quadPC slot 0) :
    execute image (3*count+fuel) s true =
      (do let mid ← trace count g s
          let out ← execute image fuel mid true
          return out.charge (32*count) count) := by
  induction count generalizing s g slot with
  | zero => simp [trace,Execution.charge]
  | succ k ih =>
    rw [show 3*(k+1)+fuel=3+(3*k+fuel) by omega,
      one_run s g ⟨slot,by omega⟩ _ (by omega) phase r pc]
    simp only [trace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro reply _
    have nextPC : (after s g reply).pc=quadPC (slot+1) 0 := by
      rw [after_pc,pc]
      change BitVec.ofNat 64 (4096+4*(45212+3*slot+0))+BitVec.ofNat 64 12=_
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    rw [ih _ (g+1) (slot+1) (by omega) (by omega) (by omega) (after_regs s g reply r) nextPC]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem sequence_post (s : MachineState) (count g slot : Nat) (r : Regs s g) (pc : s.pc=quadPC slot 0)
    {out : MachineState} (hit : out ∈ support (trace count g s)) :
    Regs out (g+count) ∧ out.pc=quadPC (slot+count) 0 ∧
      ∀ reg, .x10≠reg → .x12≠reg → out.getReg reg=s.getReg reg := by
  induction count generalizing s g slot with
  | zero =>
    simp only [trace,support_pure,Set.mem_singleton_iff] at hit;subst out
    exact ⟨by simpa using r,by simpa using pc,fun _ _ _ => rfl⟩
  | succ k ih =>
    simp only [trace,mem_support_bind_iff] at hit
    obtain ⟨reply,_,tail⟩ := hit
    have nextPC : (after s g reply).pc=quadPC (slot+1) 0 := by
      rw [after_pc,pc]
      change BitVec.ofNat 64 (4096+4*(45212+3*slot+0))+BitVec.ofNat 64 12=_
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    obtain ⟨rs,here,keep⟩ := ih _ (g+1) (slot+1) (after_regs s g reply r) nextPC tail
    refine ⟨by simpa only [Nat.add_assoc,Nat.add_comm 1 k] using rs,by simpa only [Nat.add_assoc,Nat.add_comm 1 k] using here,?_⟩
    intro reg a b;exact (keep reg a b).trans (after_reg s g reply reg a b)

end TwoPermutationPrototype.Quad.Commit.Quads
