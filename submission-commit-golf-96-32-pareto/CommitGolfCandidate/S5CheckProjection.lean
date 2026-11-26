import CommitGolfCandidate.S5CheckRegisters
import CommitGolfCandidate.S5OpenMemory
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W)
structure Masked (o : Oracle) (original s t : MachineState) (h : Height) (dst : Nat) (v : Output) (steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt 224
  mem : t.mem=(writeBits original (W dst) (storeReply h v)).mem
  keep : ParentPreserves s t

private theorem half_same {s u : MachineState} (m : s.mem=u.mem) (a : Word) :
    (s.setHalfword a 0).mem=(u.setHalfword a 0).mem := by
  simp only [MachineState.setHalfword,MachineState.setMem,MachineState.getMem,m]
private theorem masked_same {s u : MachineState} (m : s.mem=u.mem) (a : Nat) (mask : Word) :
    (maskedWord s a mask).mem=(maskedWord u a mask).mem := by
  simp only [maskedWord,MachineState.setWord32,MachineState.setMem,MachineState.getHalfword,MachineState.getMem,m]

theorem check_projection (o : Oracle) (orig s : MachineState) (h : Height) (dst : Nat) (v : Output)
    (pc : s.pc=pcAt 211) (width : s.getReg .x31=W (wireWidth h)) (to_ : s.getReg .x12=W dst)
    (al : dst%8=0) (space : dst+32≤MEMORY_BYTES) (mem : s.mem=(writeBits orig (W dst) v).mem) :
    ∃ t steps,steps≤11 ∧ Masked o orig s t h dst v steps := by
  have cap : dst+32≤2^64:=space.trans (by decide)
  by_cases wide : wireWidth h=256
  · obtain ⟨run,ep,same⟩:=mask_full s pc (width.trans (congrArg W wide))
    exact ⟨_,2,by decide,⟨plain_flow o run,ep,by rw [full_projection h v wide];exact same.trans mem,wide_preserves s true⟩⟩
  by_cases half : wireWidth h=240
  · obtain ⟨run,ep,same⟩:=mask_halfword s pc (width.trans (congrArg W half)) dst to_ space al
    exact ⟨_,6,by decide,⟨plain_flow o run,ep,same.trans ((half_same mem _).trans (clear_reply_memory h half orig dst v al cap)),wide_preserves s false⟩⟩
  · have limits : 224≤wireWidth h ∧ wireWidth h≤238 :=
      (by decide +kernel : ∀ k : Height,wireWidth k≠256 → wireWidth k≠240 → 224≤wireWidth k ∧ wireWidth k≤238) h wide half
    obtain ⟨run,ep,same⟩:=mask_low s h pc width limits.2 dst to_ space al
    exact ⟨_,11,le_rfl,⟨plain_flow o run,ep,same.trans ((masked_same mem _ _).trans
      (narrow_reply_memory h limits.1 (by omega) orig dst v al cap)),narrow_preserves s⟩⟩

theorem parent_return (o : Oracle) (s : MachineState) (back : Nat) (limit : back<2336)
    (pc : s.pc=pcAt 224) (ra : s.getReg .x1=pcAt back) : Flow o s (s.setPC (pcAt back)) 1 0 := by
  apply one_flow o pc (known (by decide +kernel)) (i:=.JALR .x0 .x1 0)
  change some (s.setPC ((s.getReg .x1+signExtend12 0) &&& ~~~1#64))=_
  rw [ra,show signExtend12 0=0#64 by rfl,BitVec.add_zero,(by decide +kernel : ∀ j : Fin 2336,pcAt j.val &&& ~~~1#64=pcAt j.val) ⟨back,limit⟩]

private theorem reply_pc (s : MachineState) (dest : Word) (v : Output) : (writeBits s dest v).pc=s.pc+4:=rfl
attribute [local irreducible] writeBits readBuffer prepared
set_option maxHeartbeats 1000000 in
theorem plain_parent (o : Oracle) (s : MachineState) (h : Height) (src dst back : Nat)
    (pc : s.pc=pcAt 173) (one : s.getReg .x30=1) (width : s.getReg .x31=W (wireWidth h))
    (sp : s.getReg .x10=W src) (dp : s.getReg .x12=W dst) (ret : s.getReg .x1=pcAt back) (limit : back<2336)
    (source : src+96≤MEMORY_BYTES) (sa : src%8=0) (dest : dst+32≤MEMORY_BYTES) (da : dst%8=0) :
    ∃ t steps,steps≤19 ∧ Flow o s t steps 1 ∧ t.pc=pcAt back ∧ ParentPreserves s t ∧
      t.mem=(writeBits s (W dst) (storeReply h (o.compression (readBuffer s src 96)))).mem := by
  let z:=prepared s
  obtain ⟨ready,ip,mem,sys,kind,nbytes,from_,to_,w⟩:=prepare_parent s pc false (by rw [one];decide)
  have head : Flow o s z 5 0 :=by unfold z prepared;exact path_flow o (code:=prepare) (by decide +kernel) ready
  let answer:=o.compression (readBuffer s src 96)
  let u:=writeBits z (W dst) answer
  have eq : readBuffer z src 96=readBuffer s src 96:=read_buffer_memory_congr z s mem src 96
  have call:=reply_flow o ip (known (by decide +kernel)) sys nbytes kind (from_.trans sp) (to_.trans dp) source sa dest da
  rw [show readBuffer (prepared s) src 96=_ from eq] at call
  have cu : u.pc=pcAt 179:=(reply_pc z _ answer).trans ((congrArg (·+4) ip).trans (pc_succ 178))
  let v:=u.setPC (pcAt 211)
  have jump : ordinaryStep u (.base (.JAL .x0 128))=some v := by change some (u.setPC (u.pc+signExtend21 128))=some v;rw [cu];rfl
  have leap:=one_flow o cu (known (by decide +kernel)) jump
  have vr (q : Reg) : v.getReg q=z.getReg q:=MachineState.getReg_setPC.trans (writeBits_register ..)
  have vv : v.mem=(writeBits z (W dst) answer).mem:=rfl
  obtain ⟨t,n,sm,mask⟩:=check_projection o z v h dst answer rfl ((vr _).trans (w.trans width)) ((vr _).trans (to_.trans dp)) da dest vv
  have middle : ParentPreserves z v:=fun q _=>vr q
  have preserved : ParentPreserves s t:=(parent_prepare_preserves s).trans (middle.trans mask.keep)
  have retRun:=parent_return o t back limit mask.pc ((preserved .x1 (by simp [parentLive])).trans ret)
  refine ⟨_,7+n+1,by omega,(((head.trans call).trans leap).trans mask.run).trans retRun,rfl,?_,?_⟩
  · intro q good;exact MachineState.getReg_setPC.trans (preserved q good)
  · exact mask.mem.trans (write_bits_memory_congr z s _ _ mem)
end CommitGolfCandidate.S5Machine.Check
