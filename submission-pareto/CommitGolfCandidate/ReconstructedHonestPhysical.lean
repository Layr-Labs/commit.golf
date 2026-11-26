import CommitGolfCandidate.ReconstructedHonestProtected
import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate.Reconstruction.HonestPhysical
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRegionStep HonestProtected HonestMemoryRanges HonestRanges

/-- An excluded output interval gives physical equality of the qword, including
all 200 bytes of any permutation response. -/
private theorem reply_away {bits : Nat} (a : Abstract) (s : MachineState) (q : Word) (answer : BitVec bits)
    (size : (bits+7)/8≤200) (meaning : Models s a)
    (outside : away (wrap (a.regs .x12).lo ((a.regs .x12).hi+199)) q=true) :
    (writeBits s (s.getReg .x12) answer).getMem q=s.getMem q := by
  apply writeBits_memory_outside
  intro i hi
  have access := meaning.1 .x12
  have small : i<2^64 := by omega
  have contained : Contains (wrap (a.regs .x12).lo ((a.regs .x12).hi+199))
      (s.getReg .x12+BitVec.ofNat 64 i) := by
    apply wrap_ok _ _ ((s.getReg .x12).toNat+i) (by have := access.1; omega) (by have := access.2; omega)
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,limit]
  exact (away_ok _ _ _ contained outside).2

theorem unchanged (im : Image) (s : MachineState) (coins : Bool) (a : Abstract) (op : Instruction)
    (meaning : Models s a) (read : fetch im s=some op) (pub : op=.base .ECALL → s.getReg .x5=0)
    (out : Execution) (run : out∈support (execute im 1 s coins)) (cont : out.exit=.unfinished)
    (q : Word) (safe : (writes a op).all (fun win => away win q)=true) :
    out.state.getMem q=s.getMem q := by
  by_cases call : op=.base .ECALL
  · subst op
    simp only [writes,isQuery,ite_true,Option.all_some] at safe
    rw [execute,read] at run; simp only [pub rfl,ite_true] at run
    cases input : oracleInput s with
    | none =>
      simp only [input,support_pure,Set.mem_singleton_iff] at run
      subst out; cases cont
    | some query =>
      simp only [input,mem_support_bind_iff] at run
      obtain ⟨answer,_,run⟩ := run
      simp only [execute,support_pure,Set.mem_singleton_iff] at run
      obtain ⟨_,rfl,rfl⟩ := run
      rcases query with x|(y|z) <;> exact reply_away a s q _ (by decide) meaning safe
  · have noCall : ¬isQuery op=true := fun test => call ((isQuery_iff _).mp test)
    have step := HonestAbstract.continued_step _ _ _ _ read call out run cont
    apply memory_frame s out.state op q step
    intro w desc
    simp only [writes,ite_eq_right noCall,desc,Option.map_some,Option.all_some] at safe
    have contained := address_ok (meaning.1 w.base) w.offset
    obtain ⟨word,part⟩ := away_ok _ _ _ contained safe
    unfold Store.cell; split <;> assumption

/-- An inclusive qword span suffices for all observed bytes after accounting
for the low three bits of the byte address. -/
def misses (span win : Range) := decide (span.hi+7<win.lo ∨ win.hi+7<span.lo)

theorem same_bytes (im : Image) (s : MachineState) (coins : Bool) (a : Abstract) (op : Instruction)
    (meaning : Models s a) (read : fetch im s=some op) (pub : op=.base .ECALL → s.getReg .x5=0)
    (out : Execution) (run : out∈support (execute im 1 s coins)) (cont : out.exit=.unfinished)
    (span : Range) (safe : (writes a op).all (misses span)=true) (q : Word) (between : Contains span q) :
    out.state.getByte q=s.getByte q := by
  have bound := aligned_window q
  have phys := unchanged im s coins a op meaning read pub out run cont (alignToDword q) (by
    cases w : writes a op with
    | none => rfl
    | some win =>
      simp only [w,Option.all_some,misses,decide_eq_true_eq] at safe
      simp only [Option.all_some,away,Bool.or_eq_true,decide_eq_true_eq]
      obtain ⟨lo,hi⟩ := between
      omega)
  simp only [getByte_eq,phys]

end CommitGolfCandidate.Reconstruction.HonestPhysical
