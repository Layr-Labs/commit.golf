import CommitGolfCandidate.Stage3cEmitField
import CommitGolfCandidate.Stage3cOpenInitial
import CommitGolfCandidate.Stage3cFieldWidths

set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node)
open Writer (PackedPrefix widths pushBits Below)
def WireFits (t : Levels) := ∀ h≤16,∀ j,(node t h j).toNat<2^(levelBits h)

theorem honest_fits (H : Compression) (m : Message) (salt : SaltTape) :
    WireFits (Binary.treeM (M:=Id) H m salt) := by
  intro h hh j
  by_cases inside:j<levelCount h
  · exact node_width H m salt h j (by change h≤24;omega) inside
  · have missing : node (Binary.treeM (M:=Id) H m salt) h j=0:=by
      rw [model_cached];unfold node
      have len:=BinaryMachine.layer_size H m salt h (by change h≤24;omega)
      rw [List.getElem?_eq_none (by omega)];rfl
    rw [missing];exact Nat.two_pow_pos _
def Marked (s : MachineState) (seen : List Index) := ∀ j<512,
  byteAt s (1024+j)=if seen.any (fun i=>i.val/32768==j) then 1 else 0

structure InputRows (s : MachineState) (xs seen : List Index) (tree : Levels) (salt : SaltTape) : Prop where
  sources : Sources s xs tree salt
  table : Capacity s
  marks : Marked s seen

theorem below_byte {s t : MachineState} {base : Nat} (frame : Below s t base) (j : Nat) (small : j<base) :
    byteAt t j=byteAt s j := by rw [byte_word,byte_word s,frame _ (by omega)]

theorem below_read {s t : MachineState} {base : Nat} (frame : Below s t base) (a n : Nat) (low : a+n≤base) :
    readBuffer t a n=readBuffer s a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro j hj
  have eq:=below_byte frame (a+j) (by have :=Finset.mem_range.mp hj;omega)
  exact congrArg (fun b : Byte=>b.toNat*2^(8*j)) eq

theorem inputs_below {s t xs seen tree salt} (input : InputRows s xs seen tree salt) (size : xs.length≤LENGTH)
    (frame : Below s t proofBase) : InputRows t xs seen tree salt := by
  have lengthBound : xs.length≤16777216:=size
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro r hr;exact (frame _ (by unfold indexBase proofBase;omega)).trans (input.sources.index r hr)
  · intro d hd i hi;exact (below_read frame _ 32 ((node_ok _ _ hi).2.1.trans (by decide))).trans (input.sources.node _ hd _ hi)
  · intro i;exact (below_read frame _ 24 ((salt_ok i).2.1.trans (by decide))).trans (input.sources.salts i)
  · intro j hj;exact (frame _ (by unfold proofBase;omega)).trans (input.table j hj)
  · intro j hj;exact (below_byte frame _ (by unfold proofBase;omega)).trans (input.marks j hj)

theorem inputs_mem {s t xs seen tree salt} (input : InputRows s xs seen tree salt) (mem : t.mem=s.mem) :
    InputRows t xs seen tree salt :=
  ⟨input.sources.same_mem mem,fun j hj=>(congrFun mem (W (2048+8*j))).trans (input.table j hj),
    fun j hj=>(show byteAt t (1024+j)=byteAt s (1024+j) by simp only [byteAt,MachineState.getByte,MachineState.getMem,mem]).trans (input.marks j hj)⟩

abbrev FieldCursor (tree : Levels) (s : MachineState) (fields : List Binary.Field) :=
  ProofCursor (WireFits tree) s (widths fields) (Binary.encode fields)

theorem cursor_append {s tree fields w x} (c : ProofCursor (WireFits tree) s (widths fields+w) (pushBits (Binary.encode fields) (widths fields) x))
    (fit : WireFits tree → x<2^w) : FieldCursor tree s (fields++[⟨w,x⟩]) := by
  have len : widths (fields++[⟨w,x⟩])=widths fields+w := by simp [widths]
  unfold FieldCursor;rw [len];refine ⟨c.ptr,c.count,c.sixty,?_⟩
  intro good;rw [Writer.encode_append]
  have eq : Binary.encode [⟨w,x⟩]=x := by simp [Binary.encode,Nat.mod_eq_of_lt (fit good)]
  rw [eq];exact c.payload good

theorem field_source (s : MachineState) (a n bytes : Nat) (raw : BitVec (8*bytes))
    (read : readBuffer s a bytes=raw) (size : raw.toNat<2^n) (room : 8*(Writer.parts n).length≤bytes) (al : a%8=0) :
    Writer.SourceWords s a raw.toNat (Writer.parts n) := Writer.source_field s a n bytes raw read size room al
end CommitGolfCandidate.Chained.BinaryMachine.Open
