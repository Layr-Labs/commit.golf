import CommitGolfCandidate.S5PlainNode
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16000
attribute [local irreducible] readBuffer writeBits callState

private theorem half_memory (s : MachineState) (dst : Nat) (atDst : s.getReg .x12=BitVec.ofNat 64 dst) :
    (execInstrBr s (.SH .x12 .x0 30)).mem=(s.setHalfword (BitVec.ofNat 64 (dst+30)) 0).mem := by
  change (s.setHalfword (s.getReg .x12+signExtend12 30) 0).mem=_
  rw [atDst,BitVec.ofNat_add];rfl

theorem plain_effect (H : Compression) {s h p f t} (addr : Addr s h p f t) (pads : gaps s) (inside : p<count h)
    (simple : ¬chained h) (selected : wireWidth h=238 → s.getReg .x30=heldMask h) :
    NodeEffect H h p s (plainResult H h p s f t) := by
  let x:=srcAddr h p
  let y:=dstAddr h p
  let reply : Output:=H (readBuffer s x 96)
  let z:=callState s .x21 .x22 f t reply
  let prep:=prepareCall s .x21 .x22 f t
  have dest:= (ready_addr addr).2
  have mz : z.mem=(writeBits prep (BitVec.ofNat 64 y) reply).mem := by
    unfold z callState
    change (writeBits prep (prep.getReg .x12) reply).mem=_
    rw [show prep.getReg .x12=BitVec.ofNat 64 y from dest]
  have zread : z.getReg .x12=BitVec.ofNat 64 y := by
    unfold z callState
    exact (writeBits_register prep (prep.getReg .x12) reply .x12).trans dest
  have al:= (buffers inside).2.2.2
  have endY := (buffers inside).2.2.1
  have room : y+32≤2^64 := by change dstAddr h p+32≤2^36 at endY;dsimp [y];omega
  have mem : (plainEnd h z).mem=(writeBits prep (BitVec.ofNat 64 y) (storeReply h reply)).mem := by
    rcases plain_widths h simple with wide|half|narrow
    · rw [plainEnd,if_pos wide,full_mask wide];exact mz
    · rw [plainEnd,if_neg (by omega),if_pos half,half_memory z y zread]
      apply Eq.trans _ (clear_reply_memory h half prep y reply al room)
      simp only [MachineState.setHalfword,MachineState.getMem,MachineState.setMem,mz] <;> rfl
    · rw [plainEnd,if_neg (by omega),if_neg (by omega)]
      have mask : z.getReg .x30=heldMask h :=
        (call_register s .x21 .x22 .x30 f t reply (by decide) (by decide)).trans (selected narrow)
      apply (mask_mem z y (heldMask h) zread mask).trans
      apply Eq.trans _ (narrow_reply_memory h (by omega) (by omega) prep y reply al room)
      simp only [maskedWord,MachineState.setWord32,MachineState.getHalfword,MachineState.getMem,MachineState.setMem,mz] <;> rfl
  have transfer (a n : Nat) := read_congr_mem (plainResult H h p s f t) (writeBits prep (BitVec.ofNat 64 y) (storeReply h reply)) a n mem
  constructor
  · apply (transfer y 32).trans
    exact (written prep y _).trans (plain_value H h s p simple inside pads)
  · intro a n fit away _
    apply (transfer a n).trans
    exact (write_bits_read_outside prep (storeReply h reply) y a n room (by change _≤2^36 at fit;omega) away).trans
      (read_congr_mem prep s a n rfl)
end CommitGolfCandidate.S5Machine
