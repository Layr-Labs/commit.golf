import CommitGolfCandidate.Stage3cReadChunk
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)

structure WordValue (o : Oracle) (s t : MachineState) (base bytes v bit width n k : Nat) : Prop where
  run : Flow o s t n 0
  pc : t.pc=pcAt 58
  cursor : Cursor t base bytes v (bit+width) k
  value : (t.getReg .x30).toNat=window v bit width
  mem : t.mem=s.mem
  keep : ReaderKeeps s t

attribute [local irreducible] window
theorem word_value (o : Oracle) (s : MachineState) (base bytes v bit k off left count : Nat)
    (num : count=(left+31)/32) (kmax : k<8) (inside : off+left≤64) (space : bit+off+left≤8*bytes)
    (room : base+bytes≤MEMORY_BYTES) (pc : s.pc=pcAt 34) (c : Cursor s base bytes v (bit+off) k)
    (used : s.getReg .x29=W off) (remaining : s.getReg .x31=W left) (low : (s.getReg .x30).toNat=window v bit off) :
    ∃ t n rem,n≤48*count+1 ∧ rem<8 ∧ WordValue o s t base bytes v bit (off+left) n rem := by
  induction count generalizing s k off left with
  | zero=>
    have z : left=0:=by omega
    subst left
    let t:=s.setPC (pcAt 58)
    have run:=select_zero o .chunk s pc remaining
    refine ⟨t,1,k,by decide,kmax,⟨run,rfl,?_,?_,rfl,fun q _=>MachineState.getReg_setPC⟩⟩
    · rw [Nat.add_zero];exact c.same rfl MachineState.getReg_setPC MachineState.getReg_setPC MachineState.getReg_setPC MachineState.getReg_setPC
    · rw [Nat.add_zero];exact low
  | succ count ih=>
    have pos : 0<left:=by omega
    let w:=min left 32
    obtain ⟨u,a,newK,bound,small,head⟩:=read_chunk o s base bytes v bit k off left pos kmax inside space room pc c used remaining low
    have narrow : w≤left:=Nat.min_le_left ..
    have same : off+w+(left-w)=off+left:=by omega
    obtain ⟨t,n,rem,lim,klt,tail⟩:=ih (s:=u) (k:=newK) (off:=off+w) (left:=left-w)
      (by dsimp [w];omega) small (by omega) (by omega) head.pc (by simpa only [Nat.add_assoc,w] using head.cursor) head.offset head.rest head.pending
    rw [same] at tail
    exact ⟨t,a+n,rem,by omega,klt,⟨head.run.trans tail.run,tail.pc,tail.cursor,tail.value,tail.mem.trans head.mem,head.keep.trans tail.keep⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Reader
