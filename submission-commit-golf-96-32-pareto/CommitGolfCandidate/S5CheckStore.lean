import CommitGolfCandidate.S5ReadCursor
import CommitGolfCandidate.S5InputBlock
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)
def store (s : MachineState) (a : Nat) (v : Word) :=s.setMem (W a) v

theorem store_far (s : MachineState) (a : Nat) (v : Word) (room : a+8≤MEMORY_BYTES) :
    Outside s (store s a v) a 8 := by
  intro j bj al away
  apply MachineState.getMem_setMem_ne
  intro eq
  have h:=congrArg BitVec.toNat eq
  change j<2^36 at bj;change a+8≤2^36 at room
  change (W j).toNat=(W a).toNat at h
  simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show j<2^64 by omega),Nat.mod_eq_of_lt (show a<2^64 by omega)] at h;omega

theorem stored_source {s t : MachineState} {base bytes v a : Nat} {w : Word} (orig : Reader.Source s base bytes v)
    (mem : t.mem=(store s a w).mem) (high : a+8≤base) (bounds : base+bytes≤MEMORY_BYTES) (al : a%8=0) :
    Reader.Source t base bytes v := by
  have outside:=store_far s a w (by omega)
  apply Reader.Source.same (s:=store s a w) _ mem
  intro j h
  exact (congrArg BitVec.toNat (Open.outside_byte outside al (by decide) (by omega : base+j<MEMORY_BYTES)
    (Or.inr (by omega)))).trans (orig j h)

theorem store_step (o : Oracle) (s : MachineState) (n : Nat) (base r : Reg) (imm : BitVec 12) (a : Nat) (w : Word)
    (pc : s.pc=pcAt n) (encoded : Site .check n (.SD base r imm)) (addr : s.getReg base+signExtend12 imm=W a)
    (value : s.getReg r=w) (space : a+8≤MEMORY_BYTES) (al : a%8=0) :
    let t:=(store s a w).setPC (pcAt (n+1))
    Flow o s t 1 0 := by
  have eq : s.pc+4=pcAt (n+1):=(congrArg (·+4) pc).trans (pc_succ n)
  apply plain_flow o (cycles:=1);intro fuel
  have run:=sd_run (pg:=.check) fuel false (encoded s pc) a addr space al
  rw [value,eq] at run;exact run

theorem store_word_read (s : MachineState) (a : Nat) (w : Word) : wordAt (store s a w) a=w:=MachineState.getMem_setMem_eq

end CommitGolfCandidate.S5Machine.Check
