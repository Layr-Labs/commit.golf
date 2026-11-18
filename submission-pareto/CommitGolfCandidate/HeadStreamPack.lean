import CommitGolfCandidate.HeadStreamInitial

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStream
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

def compactExit : List Nat := [156,168]
def finishPath : List Nat := [169,226,227]

theorem compact_exit (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Compact k L base H Q s0 (L-k) s) :
    Heads k L base H Q s0 0 (run s compactExit) ∧ Runs s (run s compactExit) 2 2 := by
  have regs := inv.regs
  have ok : PathOK s compactExit := by
    simp [PathOK,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨⟨regs.keep compactExit (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path _ s ok).cast rfl (by decide)⟩
  · simp [run,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18]
  · simp [run,compactExit,execInstrBr]
  · simpa using (run_keeps .x26 compactExit s (by decide)).trans inv.x26
  · intro a
    simpa using (getByte_of_mem (run_mem compactExit s (by decide)) a).trans (inv.mem a)

set_option maxHeartbeats 1000000 in
theorem finish_run (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 (groups k) s) (records : 481*k≤L) (small : L+7≤2^33) :
    ∃ final, (∀ fuel coins, execute openingImage (4+fuel) s coins=pure ⟨.success,final,4,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k/8) ∧ final.mem=s.mem := by
  have regs := inv.regs
  have ok : PathOK s finishPath := by
    simp [PathOK,finishPath,execInstrBr,inv.pc,inv.x22,regs.x7,groups,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  let final := run s finishPath
  have pc : final.pc=pcOf 228 := by
    simp [final,run,finishPath,execInstrBr,inv.pc,inv.x22,regs.x7,groups]
  have x5 : final.getReg .x5=1 := (run_keeps _ finishPath s (by decide)).trans regs.x5
  have x10 : final.getReg .x10=0 := (run_keeps _ finishPath s (by decide)).trans regs.x10
  have fetched := fetch_pack final 228 (by decide) pc
  rw [show packCode.getD 228 .NOP=.ECALL from rfl] at fetched
  have halted (fuel : Nat) (coins : Bool) :
      execute openingImage (1+fuel) final coins=pure ⟨.success,final,1,0⟩ := by
    rw [Nat.add_comm 1 fuel]
    simp [execute,fetched,x5,x10]
  have ran := (runs_path _ s ok).cast (s2 := 3) (c2 := 3) rfl (by decide)
  refine ⟨final,?_,?_,run_mem finishPath s (by decide)⟩
  · intro fuel coins
    rw [show 4+fuel=3+(1+fuel) by omega,ran,halted]
    simp [Execution.charge]
  · simp (disch := omega) [final,run,finishPath,execInstrBr,inv.x22,regs.x7,groups,
      regs.x11,regs.x16,w_shr,w_sub]

def extraSteps (k L : Nat) : Nat := 20+(12*(L-k)-(480*k-435))+57*groups k
def extraCycles (k L : Nat) : Nat := 20+(15*(L-k)-(480*k-435))+57*groups k

set_option maxHeartbeats 1000000 in
theorem convert_run (k L base H : Nat) (Q : Proof) (s : MachineState)
    (pc : s.pc=pcOf 142) (x5 : s.getReg .x5=1) (x10 : s.getReg .x10=0)
    (x11 : s.getReg .x11=BitVec.ofNat 64 L) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x20 : s.getReg .x20=BitVec.ofNat 64 base) (x27 : s.getReg .x27=BitVec.ofNat 64 H)
    (len : Q.length=L) (records : 481*k≤L) (small : L+7≤2^33)
    (room : base+2^34≤2^36) (gap : base+2^33≤H) (hroom : H+k+7≤base+2^34)
    (source : ∀ p<L, s.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0)
    (headers : ∀ r<k, (s.getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r) :
    ∃ final,
      (∀ fuel coins, execute openingImage (extraSteps k L+fuel) s coins=
        pure ⟨.success,final,extraCycles k L,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k/8) ∧
      (∀ p<L-k/8, final.getByte (BitVec.ofNat 64 (base+p))=(convert k Q).getD p 0) ∧
      (∀ a, ¬(base≤a.toNat ∧ a.toNat<base+2^34) → final.getByte a=s.getByte a) := by
  obtain ⟨init,r0,initBytes⟩ := initial_registers k L base H Q s pc x5 x10 x11 x16 x20 x27 records small room gap hroom
  obtain ⟨src,hdr,frame⟩ := initial_memory k L base H Q s (run s initial) initBytes records small room gap hroom source headers
  have gdef : groups k=(k+7)/8 := rfl
  have hroom' : H+8*groups k≤base+2^34 := by omega
  obtain ⟨s1,i1,r1⟩ := compact_loop k L base H Q _ _ init len records small room src
  obtain ⟨i2,r2⟩ := compact_exit k L base H Q _ s1 i1
  obtain ⟨s3,i3,r3⟩ := head_loop k L base H Q _ _ i2 len records small gap room hroom' hdr
  obtain ⟨final,finish,length,mem⟩ := finish_run k L base H Q _ s3 i3 records small
  have all := ((r0.trans r1).trans r2).trans r3
  refine ⟨final,?_,length,?_,?_⟩
  · intro fuel coins
    have h := all (4+fuel) coins
    rw [finish] at h
    rw [show extraSteps k L+fuel=14+(12*(L-k)-(480*k-435))+2+57*groups k+(4+fuel) by
      unfold extraSteps; omega,h]
    simp only [pure_bind,Execution.charge]
    congr 2
    unfold extraCycles
    omega
  · intro p hp
    rw [getByte_of_mem mem,i3.mem,toNat_w _ (by omega),if_pos (by omega),show base+p-base=p by omega]
    exact (getD_convert k Q p (by omega)).symm
  · intro a outside
    rw [getByte_of_mem mem,i3.mem,if_neg (by omega)]
    exact frame a outside

def exitSteps (k b : Nat) : Nat :=
  Pack.exitSteps k b+extraSteps k (ProofCodec.packedLength k (15*k+b))

def exitCycles (k b : Nat) : Nat :=
  Pack.exitCycles k b+extraCycles k (ProofCodec.packedLength k (15*k+b))

theorem extra_cycles_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    extraCycles k (ProofCodec.packedLength k (15*k+b))≤940247 := by
  have heads : (k+7)/8≤16 := by omega
  have remainders : (15*k+b+3)/4≤512 := by omega
  unfold extraCycles ProofCodec.packedLength ProofCodec.bodyLength groups
  omega

theorem exit_cycles_le (k b : Nat) (hk : k≤128) (hb : b≤128) : exitCycles k b≤3979408 := by
  have old := Pack.exit_cycles_le k b hk hb
  have extra := extra_cycles_le k b hk hb
  unfold exitCycles
  omega

theorem exit_cycles_max : exitCycles 128 128=3979408 := by decide

theorem exit_steps_le_cardinality (k b : Nat) (hk : k≤16777216) (hb : b≤128) :
    exitSteps k b≤351407434407 := by
  have old := Pack.exit_steps_le_cardinality k b hk hb
  have extra : extraSteps k (ProofCodec.packedLength k (15*k+b))≤110000000000 := by
    unfold extraSteps ProofCodec.packedLength ProofCodec.bodyLength groups
    omega
  unfold exitSteps
  omega

end TwoPermutationPrototype.PackedOpening.HeadStream
