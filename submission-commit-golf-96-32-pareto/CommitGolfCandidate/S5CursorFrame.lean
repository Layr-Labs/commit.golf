import CommitGolfCandidate.S5InputFrame
import CommitGolfCandidate.S5WireBytes
import CommitGolfCandidate.S5CheckCells
import CommitGolfCandidate.S5ReadField
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
attribute [local irreducible] S5.packedInput
def WireCursor (batch : Bool) (x : CheckInput) (s : MachineState) (bit offset : Nat) : Prop :=
  if batch then ∃ k<8,Reader.Cursor s proofBase 69397 (S5.packedInput x) bit k
  else s.getReg .x19=W (proofBase+offset)
def wireValue (batch : Bool) (x : CheckInput) (bit offset width : Nat) : Late.Digest :=
  if batch then Reader.decoded (S5.packedInput x) bit width else S5.atProof x offset 32

theorem WireCursor.frame {batch x s t bit off a n} (c : WireCursor batch x s bit off) (frame : Outside s t a n)
    (base : a+n≤proofBase) (al : a%8=0) (len : n%8=0)
    (ptr : t.getReg .x19=s.getReg .x19) (ending : t.getReg .x20=s.getReg .x20)
    (held : t.getReg .x21=s.getReg .x21) (count : t.getReg .x22=s.getReg .x22) : WireCursor batch x t bit off := by
  cases batch
  · exact ptr.trans c
  · obtain ⟨k,b,old⟩:=c
    refine ⟨k,b,⟨ptr.trans old.ptr,ending.trans old.end_,count.trans old.count,(congrArg BitVec.toNat held).trans old.buf,
      old.whole,?_⟩⟩
    intro j h
    exact (congrArg BitVec.toNat (Open.outside_byte frame al len (by change proofBase+j<2^36;unfold proofBase;omega)
      (Or.inr (by omega)))).trans (old.input j h)

theorem WireCursor.same {batch x s t bit off} (c : WireCursor batch x s bit off) (mem : t.mem=s.mem)
    (ptr : t.getReg .x19=s.getReg .x19) (ending : t.getReg .x20=s.getReg .x20)
    (held : t.getReg .x21=s.getReg .x21) (count : t.getReg .x22=s.getReg .x22) : WireCursor batch x t bit off :=
  c.frame (a:=0) (n:=0) (fun q _ _ _=>congrFun mem _) (by decide) (by decide) (by decide) ptr ending held count

def RowFrame (s t : MachineState) := Outside s t rowBuf 544
theorem RowFrame.refl (s : MachineState) : RowFrame s s:=fun _ _ _ _=>rfl
theorem RowFrame.trans {s t u} (a : RowFrame s t) (b : RowFrame t u) : RowFrame s u :=
  fun q h al outside=>(b q h al outside).trans (a q h al outside)
theorem RowFrame.enlarge {s t a n} (out : Outside s t a n) (lo : rowBuf≤a) (hi : a+n≤rowBuf+544) : RowFrame s t :=
  fun q h al away=>out q h al (by omega)

def rowRegs : List Reg:=[.x3,.x8,.x9,.x18,.x20,.x23,.x24,.x25,.x26,.x27]
def RowKeeps (s t : MachineState) := ∀ q∈rowRegs,t.getReg q=s.getReg q
theorem RowKeeps.trans {s t u} (x : RowKeeps s t) (y : RowKeeps t u) : RowKeeps s u:=fun q h=>(y q h).trans (x q h)
theorem RowKeeps.refl (s : MachineState) : RowKeeps s s:=fun _ _=>rfl

end CommitGolfCandidate.S5Machine.Check
