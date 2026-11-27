import CommitGolfCandidate.Stage3cCheckPath
import CommitGolfCandidate.Stage3cCheckDispatch
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def RecordFrame (s t : MachineState) := ∀ q<MEMORY_BYTES,q%8=0 →
  (q<leafBuf ∨ leafBuf+800≤q) → (q<saltBuf ∨ saltBuf+32≤q) → Open.wordAt t q=Open.wordAt s q
theorem RecordFrame.trans {s t u} (a : RecordFrame s t) (b : RecordFrame t u) : RecordFrame s u :=
  fun q h al w salt=>(b q h al w salt).trans (a q h al w salt)
theorem RecordFrame.cache {s t} (m : Outside s t leafBuf 800) : RecordFrame s t:=fun q h a l _=>m q h a l
theorem RecordFrame.row {s t} (m : RowFrame s t) : RecordFrame s t:=fun q h a l _=>m q h a (by change q<65536 ∨ 65536+800≤q at l;change q<65792 ∨ 65792+544≤q;omega)
theorem RecordFrame.salt {s t} (m : Outside s t saltBuf 32) : RecordFrame s t:=fun q h a _ l=>m q h a l
theorem RecordFrame.same {s t : MachineState} (m : t.mem=s.mem) : RecordFrame s t:=fun q _ _ _ _=>congrFun m (W q)

structure RecordRegs (b : Bool) (x : CheckInput) (r : Nat) (s : MachineState) : Prop where
  root : s.getReg .x8=W rootBase
  indices : s.getReg .x9=W (indexBase+8*r)
  values : s.getReg .x18=W (valueBase+256*r)
  count : s.getReg .x23=W (x.positions.card-r)
  leaf : s.getReg .x24=W leafBuf
  fixed : PathRegs s
  stream : WireCursor b x s (3780*r) (792*r)
  high : HighInput x s

def recordHead (b : Bool) : List Sym.Calc:=[.ld .x14 .x9 0,.addi .x9 .x9 8,.lui (if b then .x10 else .x6) 32]
theorem record_head (o : Oracle) (x : CheckInput) (r : Nat) (b : Bool) (s : MachineState) (hr : r<x.positions.card)
    (pc : s.pc=pcAt (recordBegin b)) (reg : RecordRegs b x r s) :
    ∃ t,Flow o s t 3 0 ∧ t.pc=pcAt (recordBegin b+3) ∧ t.getReg .x14=W (Pw.recordIndex x.positions r).val ∧
      t.getReg .x9=W (indexBase+8*(r+1)) ∧ t.getReg (peerTarget b)=W saltBuf ∧ t.mem=s.mem ∧
      ∀ q,q∉([.x6,.x9,.x10,.x14] : List Reg)→t.getReg q=s.getReg q := by
  let a:=indexBase+8*r
  have cap : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at cap
  have bound : a+8≤MEMORY_BYTES:=by dsimp [a,indexBase,MEMORY_BYTES];omega
  have align : a%8=0:=by dsimp [a,indexBase];omega
  have ea : s.getReg .x9+0#64=W a:=by rw [BitVec.add_zero];exact reg.indices
  have site : ∀ mode : Bool,Sym.Listed (recordHead mode) (recordBegin mode):=by decide +kernel
  have valid : ∀ e∈Sym.requirements Sym.original (recordHead b),accessValid (e.1.eval s) e.2=true:=by
    intro e he
    change e∈[(Sym.Expr.op .add (.reg .x9) (.lit 0),8)] at he
    obtain rfl:=List.mem_singleton.mp he
    change accessValid (s.getReg .x9+0#64) 8=true;rw [ea];apply access_ok _ _ bound (by change _≤2^36 at bound;omega) align
  obtain ⟨flow,regs,mem,ip⟩:=Sym.compiled o _ _ s pc (site b) valid
  have live : s.getMem (s.getReg .x9+0#64)=W (Pw.recordIndex x.positions r).val:=by
    rw [ea];exact (reg.high a (by dsimp [a,indexBase,rootBase];omega) (by omega) align).trans (loaded_index x r hr)
  refine ⟨_,flow,ip,?_,?_,?_,mem,?_⟩
  · apply (regs .x14).trans;cases b <;> exact live
  · apply (regs .x9).trans
    have advance : s.getReg .x9+8#64=W (indexBase+8*(r+1)) := (congrArg (·+8#64) reg.indices).trans
      ((BitVec.ofNat_add (indexBase+8*r) 8).symm.trans (congrArg W (by omega)))
    cases b <;> exact advance
  · apply (regs (peerTarget b)).trans;cases b <;> rfl
  · intro q h;apply (regs q).trans;cases b <;> cases q <;> first | (exfalso;apply h;decide) | rfl
end CommitGolfCandidate.Chained.BinaryMachine.Check
