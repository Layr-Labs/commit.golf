import CommitGolfCandidate.S5ReadStart
import CommitGolfCandidate.S5CheckStore
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt Outside)
open Check (Flow store)
def storeTail (s : MachineState) := (execInstrBr s (.ADDI .x12 .x12 8)).setPC (pcAt 27)
private theorem store_tail (o : Oracle) (s : MachineState) (pc : s.pc=pcAt 59) :
    Flow o s (storeTail s) 2 0 ∧ (storeTail s).getReg .x12=s.getReg .x12+8 ∧
      ∀ q,q≠.x12 → (storeTail s).getReg q=s.getReg q := by
  let u:=execInstrBr s (.ADDI .x12 .x12 8)
  have inc:=Check.one_flow o (t:=u) pc (Check.known (by decide +kernel)) (i:=.ADDI .x12 .x12 8) rfl
  have pu : u.pc=pcAt 60:=(congrArg (·+4) pc).trans (pc_succ 59)
  have leap : ordinaryStep u (.base (.JAL .x0 2097020))=some (storeTail s):=by
    change some (u.setPC (u.pc+signExtend21 2097020))=_;rw [pu];rfl
  exact ⟨inc.trans (Check.one_flow o pu (Check.known (by decide +kernel)) leap),rfl,fun q h=>
    MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm))⟩

def fieldKeep (q : Reg) := readKeep q ∧ q≠.x12 ∧ q≠.x13
structure FieldWord (o : Oracle) (s t : MachineState) (base bytes v bit n dst steps k : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt 27
  cursor : Cursor t base bytes v (bit+min n 64) k
  mem : t.mem=(store s dst (W (window v bit (min n 64)))).mem
  rem : t.getReg .x13=W (n-min n 64)
  dest : t.getReg .x12=W (dst+8)
  keep : ∀ q,fieldKeep q→t.getReg q=s.getReg q

theorem field_word (o : Oracle) (s : MachineState) (base bytes v bit k n dst : Nat) (pos : 0<n) (bound : n≤256)
    (room : base+bytes≤MEMORY_BYTES) (space : bit+n≤8*bytes) (kmax : k<8) (pc : s.pc=pcAt 27)
    (rem : s.getReg .x13=W n) (c : Cursor s base bytes v bit k) (dest : s.getReg .x12=W dst)
    (low : dst+8≤base) (al : dst%8=0) :
    ∃ t steps buffered,steps≤107 ∧ buffered<8 ∧ FieldWord o s t base bytes v bit n dst steps buffered := by
  let w:=min n 64
  let value:=W (window v bit w)
  obtain ⟨u,a,k',lim,bits,got⟩:=decode_word o s base bytes v bit k n pos bound room space kmax pc rem c
  have source : u.getReg .x30=value:=by
    change u.getReg .x30=BitVec.ofNat 64 (window v bit w);rw [←got.word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have dstReg:=(got.keep .x12 (by simp [readKeep]) (by decide)).trans dest
  let z:=(store u dst value).setPC (pcAt 59)
  have write:=Check.store_step o u 58 .x12 .x30 0 dst value got.pc (Check.known (by decide +kernel))
    (by simpa only [show signExtend12 0=0#64 by rfl,BitVec.add_zero] using dstReg) source (by omega) al
  let t:=storeTail z
  obtain ⟨back,after,keep⟩:=store_tail o z rfl
  have same : t.mem=(store u dst value).mem:=rfl
  have frame : t.mem=(store s dst value).mem:=by rw [same];simp only [store,MachineState.setMem,got.mem]
  have stable (q : Reg) (ne : q≠.x12) : t.getReg q=u.getReg q:=by apply (keep q ne).trans;cases q <;> rfl
  let old:=got.cursor
  have data:=Check.stored_source old.input same low room al
  have queue : Cursor t base bytes v (bit+w) k':=⟨(stable _ (by decide)).trans old.ptr,(stable _ (by decide)).trans old.end_,
    (stable _ (by decide)).trans old.count,(congrArg BitVec.toNat (stable _ (by decide))).trans old.buf,old.whole,data⟩
  refine ⟨t,a+1+2,k',by omega,bits,⟨(got.run.trans write).trans back,rfl,queue,frame,(stable _ (by decide)).trans got.rem,?_,?_⟩⟩
  · exact after.trans ((congrArg (·+8) dstReg).trans (BitVec.ofNat_add dst 8).symm)
  · intro q h;exact (stable q h.2.1).trans (got.keep q h.1 h.2.2)
end CommitGolfCandidate.S5Machine.Reader
