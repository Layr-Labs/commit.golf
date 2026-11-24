import CommitGolfCandidate.TailStreamGroups

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack ProofCodec.HeadStreamSeven
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

def finishPath : List Nat := [37,98,99]
def extraSteps (k L : Nat) : Nat := 24+7*k+(12*(L-k)-(479*k-435))+61*((k+7)/8)
def extraCycles (k L : Nat) : Nat := 24+7*k+(15*(L-k)-(479*k-435))+61*((k+7)/8)

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 1000000 in
theorem finish_run (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 ((k+7)/8) s) (records : 480*k≤L) (small : L+7≤2^33) :
    ∃ final, (∀ fuel coins, execute image (4+fuel) s coins=pure ⟨.success,final,4,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k/8) ∧ final.mem=s.mem := by
  have regs := inv.regs
  have ok : PathOK s finishPath := by
    simp [PathOK,finishPath,execInstrBr,inv.pc,inv.x22,regs.x7,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  let final := run s finishPath
  have pc : final.pc=pcOf 100 := by
    simp [final,run,finishPath,execInstrBr,inv.pc,inv.x22,regs.x7]
  have x5 : final.getReg .x5=1 := (run_keeps _ finishPath s (by decide)).trans regs.x5
  have x10 : final.getReg .x10=0 := (run_keeps _ finishPath s (by decide)).trans regs.x10
  have fetched := CodeImage.fetched (image := image) final 100 (by decide) pc
  rw [word_100] at fetched
  have halted (fuel : Nat) (coins : Bool) :
      execute image (1+fuel) final coins=pure ⟨.success,final,1,0⟩ := by
    rw [Nat.add_comm 1 fuel]
    simp [execute,fetched,x5,x10]
  have ran := (runs_path (image := image) _ s ok).cast (s2 := 3) (c2 := 3) rfl (by decide)
  refine ⟨final,?_,?_,run_mem finishPath s (by decide)⟩
  · intro fuel coins
    rw [show 4+fuel=3+(1+fuel) by omega,ran,halted]
    simp [Execution.charge]
  · simp (disch := omega) [final,run,finishPath,execInstrBr,inv.x22,regs.x7,
      regs.x11,regs.x16,w_shr,w_sub]

set_option maxHeartbeats 2400000 in
theorem convert_run (k L base H : Nat) (Q : Proof) (s : MachineState)
    (regs : EntryRegs k L base H s) (pc : s.pc=pcOf 0)
    (len : Q.length=L) (records : 480*k≤L) (small : L+7≤2^33)
    (room : base+2^34≤2^36) (gap : base+2^33≤H) (hroom : H+k+8≤base+2^34)
    (source : ∀ p<L, s.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0) :
    ∃ final,
      (∀ fuel coins, execute image (extraSteps k L+fuel) s coins=
        pure ⟨.success,final,extraCycles k L,0⟩) ∧
      final.getReg .x11=BitVec.ofNat 64 (L-k/8) ∧
      (∀ p<L-k/8, final.getByte (BitVec.ofNat 64 (base+p))=(convert k Q).getD p 0) ∧
      (∀ a, ¬(base≤a.toNat ∧ a.toNat<base+2^34) → final.getByte a=s.getByte a) := by
  obtain ⟨ex0,re0⟩ := extract_initialize (image := image) k L base H Q s regs pc
  obtain ⟨ex,exk,re1⟩ := extract_loop (image := image) k L base H Q s _ ex0 records small gap room hroom source
  obtain ⟨rex,pcx,mex,re2⟩ := extract_exit (image := image) k L base H Q s ex exk
  let sx := run ex extractExit
  have exMem (a : Word) : sx.getByte a=
      if H≤a.toNat ∧ a.toNat<H+k then Q.getD (480*(a.toNat-H)+44) 0 else s.getByte a :=
    (mex a).trans (exk.mem a)
  have exSource : ∀ p<L, sx.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0 := by
    intro p hp
    rw [exMem,toNat_w _ (by omega),if_neg (by omega)]
    exact source p hp
  have exHeaders : ∀ r<k, (sx.getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r := by
    intro r hr
    rw [exMem,toNat_w _ (by omega),if_pos (by omega),show H+r-H=r by omega,head,if_pos hr]
  obtain ⟨init,r0,initBytes⟩ := initial_registers (image := image) k L base H Q sx pcx
    rex.x5 rex.x10 rex.x11 rex.x16 rex.x20 rex.x27 records small room gap hroom
  obtain ⟨src,hdr,frame⟩ := initial_memory k L base H Q sx (run sx initial) initBytes records small room gap hroom exSource exHeaders
  have headers : ∀ r<k+7, ((run sx initial).getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r := by
    intro r hr
    by_cases before : r<k
    · exact hdr r before
    · rw [initBytes,fillZero_bytes sx (H+k) 7 (by omega),toNat_w _ (by omega),if_pos (by omega),head,if_neg before]
      rfl
  obtain ⟨s1,i1,r1⟩ := compact_loop (image := image) k L base H Q _ _ init len records small room src
  have bank : ∀ r<k+7, (s1.getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r := by
    intro r hr
    rw [i1.mem,toNat_w _ (by omega),if_neg (by omega)]
    exact headers r hr
  obtain ⟨i2,r2⟩ := compact_exit (image := image) k L base H Q _ s1 i1
  obtain ⟨s3,i3,r3⟩ := group_loop (image := image) k L base H Q s1 _ i2 records small gap room hroom bank
  obtain ⟨final,finish,length,mem⟩ := finish_run (image := image) k L base H Q _ s3 i3 records small
  have all := ((((((re0.trans re1).trans re2).trans r0).trans r1).trans r2).trans r3)
  refine ⟨final,?_,length,?_,?_⟩
  · intro fuel coins
    have h := all (4+fuel) coins
    rw [finish] at h
    rw [show extraSteps k L+fuel=2+7*k+1+14+(12*(L-k)-(479*k-435))+3+61*((k+7)/8)+(4+fuel) by
      unfold extraSteps;omega,h]
    simp only [pure_bind,Execution.charge]
    congr 2
    unfold extraCycles
    omega
  · intro p hp
    rw [getD_convert k Q p (by rw [len];exact hp),getByte_of_mem mem,i3.mem,toNat_w _ (by omega)]
    by_cases front : p<L-k
    · rw [if_neg (by omega),i1.mem,toNat_w _ (by omega),if_pos (by omega),show base+p-base=p by omega]
    · rw [if_pos (by omega),show base+p-(base+(L-k))=p-(L-k) by omega]
      rw [convertedByte,len,if_neg front]
  · intro a outside
    rw [getByte_of_mem mem,i3.mem,if_neg (by omega),i1.mem,if_neg (by omega),frame a outside,exMem,if_neg (by omega)]

end TwoPermutationPrototype.PackedOpening.TailStream
