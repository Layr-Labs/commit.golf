import CommitGolfCandidate.HeadStreamInitial

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open ProofCodec
open CommitGolfCandidate.ProofCodec.HeadStreamThree
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

def compactExit : List Nat := [156,168,169]
def finishPath : List Nat := [170,237,238,239,240]

theorem compact_exit (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Compact k L base H Q s0 (L-k) s) (len : Q.length=L) :
    Heads k L base H Q s0 0 (run s compactExit) ∧ Runs s (run s compactExit) 3 3 := by
  have regs := inv.regs
  have ok : PathOK s compactExit := by
    simp [PathOK,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨⟨regs.keep compactExit (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path _ s ok).cast rfl (by decide)⟩
  · simp [run,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18]
  · simp [run,compactExit,execInstrBr]
  · simp [run,compactExit,execInstrBr,inv.x22,regs.x18,regs.x20,w_add]
  · intro a
    rw [getByte_of_mem (run_mem compactExit s (by decide)),inv.mem]
    by_cases inside : base≤a.toNat ∧ a.toNat<base+(L-k)
    · rw [if_pos inside,if_pos inside,partial_zero,convertedByte,len,if_pos (by omega)]
    · rw [if_neg inside,if_neg inside]

set_option maxHeartbeats 1000000 in
theorem finish_run (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 k s) (records : 481*k≤L) (small : L+7≤2^33) :
    ∃ final, (∀ fuel coins, execute openingImage (6+fuel) s coins=pure ⟨.success,final,6,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k) ∧ final.mem=s.mem := by
  have regs := inv.regs
  have ok : PathOK s finishPath := by
    simp [PathOK,finishPath,execInstrBr,inv.pc,inv.x22,regs.x16,
      ordinaryInstr,memoryArgumentsValid,memAccess] <;> decide
  let final := run s finishPath
  have pc : final.pc=pcOf 241 := by
    simp [final,run,finishPath,execInstrBr,inv.pc,inv.x22,regs.x16] <;> decide
  have x5 : final.getReg .x5=1 := (run_keeps _ finishPath s (by decide)).trans regs.x5
  have x10 : final.getReg .x10=0 := (run_keeps _ finishPath s (by decide)).trans regs.x10
  have fetched := fetch_pack final 241 (by decide) pc
  rw [show packCode.getD 241 .NOP=.ECALL from rfl] at fetched
  have halted (fuel : Nat) (coins : Bool) :
      execute openingImage (1+fuel) final coins=pure ⟨.success,final,1,0⟩ := by
    rw [Nat.add_comm 1 fuel]
    simp [execute,fetched,x5,x10]
  have ran := (runs_path _ s ok).cast (s2 := 5) (c2 := 5) rfl (by decide)
  refine ⟨final,?_,?_,run_mem finishPath s (by decide)⟩
  · intro fuel coins
    rw [show 6+fuel=5+(1+fuel) by omega,ran,halted]
    simp [Execution.charge]
  · simp (disch := omega) [final,run,finishPath,execInstrBr,inv.x22,regs.x16,
      regs.x11,regs.x16,w_shl,w_add,w_shr,w_sub]

def extraSteps (k L : Nat) : Nat := 23+(12*(L-k)-(480*k-435))+12*k
def extraCycles (k L : Nat) : Nat := 23+(15*(L-k)-(480*k-435))+12*k

set_option maxHeartbeats 1000000 in
theorem convert_run (k L base H : Nat) (Q : Proof) (s : MachineState)
    (pc : s.pc=pcOf 142) (x5 : s.getReg .x5=1) (x10 : s.getReg .x10=0)
    (x11 : s.getReg .x11=BitVec.ofNat 64 L) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x20 : s.getReg .x20=BitVec.ofNat 64 base) (x27 : s.getReg .x27=BitVec.ofNat 64 H)
    (len : Q.length=L) (records : 481*k≤L) (small : L+7≤2^33)
    (room : base+2^34≤2^36) (gap : base+2^33≤H) (hroom : H+k+8≤base+2^34)
    (source : ∀ p<L, s.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0)
    (headers : ∀ r<k, (s.getByte (BitVec.ofNat 64 (H+r))).toNat%8=head k Q r) :
    ∃ final,
      (∀ fuel coins, execute openingImage (extraSteps k L+fuel) s coins=
        pure ⟨.success,final,extraCycles k L,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k) ∧
      (∀ p<L-k, final.getByte (BitVec.ofNat 64 (base+p))=(HeadStreamZero.convert k Q).getD p 0) ∧
      (∀ a, ¬(base≤a.toNat ∧ a.toNat<base+2^34) → final.getByte a=s.getByte a) := by
  obtain ⟨init,r0,initBytes⟩ := initial_registers k L base H Q s pc x5 x10 x11 x16 x20 x27 records small room gap hroom
  obtain ⟨src,hdr,frame⟩ := initial_memory k L base H Q s (run s initial) initBytes records small room gap hroom source headers
  obtain ⟨s1,i1,r1⟩ := compact_loop k L base H Q _ _ init len records small room src
  obtain ⟨i2,r2⟩ := compact_exit k L base H Q _ s1 i1 len
  obtain ⟨s3,i3,r3⟩ := head_loop k L base H Q _ _ i2 len records small gap room hroom
    hdr
  obtain ⟨final,finish,length,mem⟩ := finish_run k L base H Q _ s3 i3 records small
  have all := ((r0.trans r1).trans r2).trans r3
  refine ⟨final,?_,length,?_,?_⟩
  · intro fuel coins
    have h := all (6+fuel) coins
    rw [finish] at h
    rw [show extraSteps k L+fuel=14+(12*(L-k)-(480*k-435))+3+12*k+(6+fuel) by
      unfold extraSteps; omega,h]
    simp only [pure_bind,Execution.charge]
    congr 2
    unfold extraCycles
    omega
  · intro p hp
    rw [getByte_of_mem mem,i3.mem,toNat_w _ (by omega),if_pos (by omega),show base+p-base=p by omega]
    rw [partial_full]
    exact (HeadStreamZero.getD_convert k Q p (by omega)).symm
  · intro a outside
    rw [getByte_of_mem mem,i3.mem,if_neg (by omega)]
    exact frame a outside

def exitSteps (k b : Nat) : Nat :=
  Pack.exitSteps k b+extraSteps k (ProofCodec.packedLength k (15*k+b))

def exitCycles (k b : Nat) : Nat :=
  Pack.exitCycles k b+extraCycles k (ProofCodec.packedLength k (15*k+b))

theorem extra_cycles_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    extraCycles k (ProofCodec.packedLength k (15*k+b))≤940874 := by
  have remainders : (15*k+b+3)/4≤512 := by omega
  unfold extraCycles ProofCodec.packedLength ProofCodec.bodyLength
  omega

theorem exit_cycles_le (k b : Nat) (hk : k≤128) (hb : b≤128) : exitCycles k b≤3980035 := by
  have old := Pack.exit_cycles_le k b hk hb
  have extra := extra_cycles_le k b hk hb
  unfold exitCycles
  omega

theorem exit_cycles_max : exitCycles 128 128=3980035 := by decide

theorem exit_steps_le_cardinality (k b : Nat) (hk : k≤16777216) (hb : b≤128) :
    exitSteps k b≤351407434407 := by
  have old := Pack.exit_steps_le_cardinality k b hk hb
  have extra : extraSteps k (ProofCodec.packedLength k (15*k+b))≤110000000000 := by
    unfold extraSteps ProofCodec.packedLength ProofCodec.bodyLength
    omega
  unfold exitSteps
  omega

end TwoPermutationPrototype.PackedOpening.HeadStream
