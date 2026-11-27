import CommitGolfCandidate.Stage3cPtrLeafRun
import CommitGolfCandidate.Stage3cLeafFrame
import CommitGolfCandidate.Stage3cChainBlock
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf Late CommitGolf.Riscv RiscvZkvm.Rv64
set_option Elab.async false
set_option maxHeartbeats 500000

private def source (i c : Nat) := match c with
  | 0=>msgAddr i | 1=>msgAddr i+64 | 2=>msgAddr i+160 | _=>rowAddr i
private def target (i c : Nat) := match c with
  | 0=>msgAddr i+64 | 1=>contentAddr i | 2=>contentAddr i+32 | _=>nodeAddress 0 i

private theorem positions (i : Nat) (c : Fin 4) : absSrc i c=source i c ∧ absDst i c=target i c := by
  have eq0:levelOffset 0=0:=by decide
  fin_cases c <;> simp [absSrc,absDst,srcOff,dstOff,msgCursor,rowCursor,nodeCursor,source,target,msgAddr,rowAddr,
       contentAddr,nodeAddress,eq0,gapOffset,rowBase] <;> (try split_ifs) <;> omega

private theorem siteMemory (h : Compression) {s : MachineState} {i : Nat} (r:LeafRegs s i)
    (c : Fin 4) (bound:i<LENGTH) (t : MachineState) (same:s.mem=t.mem) :
    (siteResult h s i c).mem=(compressAt h t (source i c) (target i c)).mem := by
  have addr:=ready_addresses r c bound
  let w:=h (readBuffer s (absSrc i c) 96)
  change (writeBits (leafReady s i c) ((leafReady s i c).getReg .x12) w).mem=_
  rw [addr.2]
  unfold w
  rw [(positions i c).1,(positions i c).2,read_congr_mem s t _ _ same]
  apply write_bits_memory_congr
  exact (show (leafReady s i c).mem=s.mem by rfl).trans same

theorem finalLeafMemory (h : Compression) {s : MachineState} {i : Nat} (r:LeafRegs s i) (bound:i<LENGTH) :
    (finalLeaf h s i).mem=(writeLeaf h s i).mem := by
  unfold finalLeaf writeLeaf
  let u:=siteResult h s i 0
  let v:=siteResult h u i 1
  let w:=siteResult h v i 2
  have ru:LeafRegs u i:=reply_regs r 0 _
  have rv:LeafRegs v i:=reply_regs ru 1 _
  have rw':LeafRegs w i:=reply_regs rv 2 _
  exact siteMemory h rw' 3 bound _ (siteMemory h rv 2 bound _ (siteMemory h ru 1 bound _ (siteMemory h r 0 bound _ rfl)))

private theorem advanceMem (on : Prop) [Decidable on] (s : MachineState) (r : Reg) (v : Word) :
    (advanceWhen on s r v).mem=s.mem:=by unfold advanceWhen;split <;> cases r <;> rfl
theorem afterLeafMemory (h : Compression) {s : MachineState} {i : Nat} (r:LeafRegs s i) (bound:i<LENGTH) :
    (afterLeaf h s i).mem=(writeLeaf h s i).mem:=by
  unfold afterLeaf leafTail movedCount movedNode movedRow movedMsg
  simp only [MachineState.setPC,advanceMem];exact finalLeafMemory h r bound

end CommitGolfCandidate.Chained.BinaryMachine
