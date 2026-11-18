import CommitGolfCandidate.QuadCommitQuad2Control

/-! Level-3 quad pass: node `m` reads level-2 group `m` (72 zero bytes and four level-2 nodes) and
writes its 200-byte reply ascending at heap node `2^18 + m`. -/
namespace TwoPermutationPrototype.Quad.Commit.Quad3s
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image execute writeBits

structure Regs (s : MachineState) (g : Nat) : Prop where
  source : s.getReg .x10=wordAddress (quad3GroupWord g)
  target : s.getReg .x12=wordAddress (heapWord (2^18+g))
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem regs_setPC (s : MachineState) (g : Nat) (pc : Word) (r : Regs s g) : Regs (s.setPC pc) g :=
  ⟨r.source,r.target,r.selector,r.size,r.primitive⟩

def after (s : MachineState) (g : Nat) (reply : BitVec 1600) :=
  execInstrBr (execInstrBr (writeBits s (wordAddress (heapWord (2^18+g))) reply)
    (.ADDI .x10 .x10 368)) (.ADDI .x12 .x12 32)

def trace : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,g,s => do
    let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (quad3GroupWord g))))))) : OracleComp World (BitVec 1600))
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

theorem after_regs (s : MachineState) (g : Nat) (reply : BitVec 1600) (r : Regs s g) :
    Regs (after s g reply) (g+1) := by
  refine ⟨?_,?_,(after_reg s g reply .x5 (by decide) (by decide)).trans r.selector,
    (after_reg s g reply .x11 (by decide) (by decide)).trans r.size,
    (after_reg s g reply .x13 (by decide) (by decide)).trans r.primitive⟩
  · change (writeBits s _ reply).getReg .x10+signExtend12 368=_
    rw [CommitGolfCandidate.writeBits_register,r.source]
    change wordAddress (quad3GroupWord g)+BitVec.ofNat 64 368=_
    rw [wordAddress,←BitVec.ofNat_add]
    congr 1 <;> (unfold quad3GroupWord;omega)
  · change (writeBits s _ reply).getReg .x12+signExtend12 32=_
    rw [CommitGolfCandidate.writeBits_register,r.target]
    change wordAddress (heapWord (2^18+g))+BitVec.ofNat 64 32=_
    rw [wordAddress,←BitVec.ofNat_add]
    congr 1 <;> (unfold heapWord;omega)

private theorem one_run (s : MachineState) (g : Nat) (slot : Fin 16384) (fuel : Nat)
    (bound : g<2^18) (r : Regs s g) (pc : s.pc=quad3PC slot.val 0) :
    execute image (3+fuel) s true =
      (do let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (quad3GroupWord g))))))) : OracleComp World (BitVec 1600))
          let out ← execute image fuel (after s g reply) true
          return out.charge 10 1) := by
  rw [show 3+fuel=(fuel+2)+1 by omega,
    execute_permutation_call image (fuel+2) s true (quad3GroupWord g) (heapWord (2^18+g))
      (by unfold quad3GroupWord;omega) (by unfold heapWord;omega) r.source r.target r.selector r.size r.primitive
      (fetch_quad3 slot ⟨0,by decide⟩ s pc)]
  apply bind_congr_of_forall_mem_support
  intro reply _
  let written := writeBits s (wordAddress (heapWord (2^18+g))) reply
  let moved := execInstrBr written (.ADDI .x10 .x10 368)
  have writtenPC : written.pc=quad3PC slot.val 1 := by
    dsimp only [written]
    rw [written_pc,pc]
    change BitVec.ofNat 64 (4096+4*(143538+3*slot.val+0))+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add];congr 1 <;> omega
  have movedPC : moved.pc=quad3PC slot.val 2 := by
    change written.pc+BitVec.ofNat 64 4=_
    rw [writtenPC];unfold quad3PC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad3 slot ⟨1,by decide⟩ written writtenPC)
    (show ordinaryStep written (.base (.ADDI .x10 .x10 368))=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad3 slot ⟨2,by decide⟩ moved movedPC)
    (show ordinaryStep moved (.base (.ADDI .x12 .x12 32))=some (after s g reply) from rfl)]
  simp [quad3Instr,instructionCycles,Execution.charge,←Nat.add_assoc]

theorem sequence_run (s : MachineState) (count g slot fuel : Nat) (bound : g+count≤2^18)
    (inside : slot+count≤16384) (r : Regs s g) (pc : s.pc=quad3PC slot 0) :
    execute image (3*count+fuel) s true =
      (do let mid ← trace count g s
          let out ← execute image fuel mid true
          return out.charge (10*count) count) := by
  induction count generalizing s g slot with
  | zero => simp [trace,Execution.charge]
  | succ k ih =>
    rw [show 3*(k+1)+fuel=3+(3*k+fuel) by omega,
      one_run s g ⟨slot,by omega⟩ _ (by omega) r pc]
    simp only [trace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro reply _
    have nextPC : (after s g reply).pc=quad3PC (slot+1) 0 := by
      rw [after_pc,pc]
      change BitVec.ofNat 64 (4096+4*(143538+3*slot+0))+BitVec.ofNat 64 12=_
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    rw [ih _ (g+1) (slot+1) (by omega) (by omega) (after_regs s g reply r) nextPC]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem sequence_post (s : MachineState) (count g slot : Nat) (r : Regs s g) (pc : s.pc=quad3PC slot 0)
    {out : MachineState} (hit : out ∈ support (trace count g s)) :
    Regs out (g+count) ∧ out.pc=quad3PC (slot+count) 0 ∧
      ∀ reg, .x10≠reg → .x12≠reg → out.getReg reg=s.getReg reg := by
  induction count generalizing s g slot with
  | zero =>
    simp only [trace,support_pure,Set.mem_singleton_iff] at hit;subst out
    exact ⟨by simpa using r,by simpa using pc,fun _ _ _ => rfl⟩
  | succ k ih =>
    simp only [trace,mem_support_bind_iff] at hit
    obtain ⟨reply,_,tail⟩ := hit
    have nextPC : (after s g reply).pc=quad3PC (slot+1) 0 := by
      rw [after_pc,pc]
      change BitVec.ofNat 64 (4096+4*(143538+3*slot+0))+BitVec.ofNat 64 12=_
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    obtain ⟨rs,here,keep⟩ := ih _ (g+1) (slot+1) (after_regs s g reply r) nextPC tail
    refine ⟨by simpa only [Nat.add_assoc,Nat.add_comm 1 k] using rs,by simpa only [Nat.add_assoc,Nat.add_comm 1 k] using here,?_⟩
    intro reg a b;exact (keep reg a b).trans (after_reg s g reply reg a b)

end TwoPermutationPrototype.Quad.Commit.Quad3s
