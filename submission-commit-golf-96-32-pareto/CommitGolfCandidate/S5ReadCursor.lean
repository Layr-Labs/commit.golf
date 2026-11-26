import CommitGolfCandidate.S5ReadRefill
import CommitGolfCandidate.S5CheckFlow
import CommitGolfCandidate.S5OpenMemory
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W byteAt)
open Check (Flow)
def Source (s : MachineState) (base bytes v : Nat) :=
  ∀ j<bytes,(byteAt s (base+j)).toNat=window v (8*j) 8
structure Cursor (s : MachineState) (base bytes v bit k : Nat) : Prop where
  ptr : s.getReg .x19=W (base+(bit+k)/8)
  end_ : s.getReg .x20=W (base+bytes)
  count : s.getReg .x22=W k
  buf : (s.getReg .x21).toNat=window v bit k
  whole : (bit+k)%8=0
  input : Source s base bytes v

theorem Source.same {s t base bytes v} (old : Source s base bytes v) (mem : t.mem=s.mem) : Source t base bytes v := by
  intro j hj
  simp only [byteAt,MachineState.getByte,MachineState.getMem,mem] at old ⊢
  exact old j hj

theorem Cursor.same {s t base bytes v bit k} (old : Cursor s base bytes v bit k) (mem : t.mem=s.mem)
    (ptr : t.getReg .x19=s.getReg .x19) (end_ : t.getReg .x20=s.getReg .x20) (count : t.getReg .x22=s.getReg .x22)
    (buf : t.getReg .x21=s.getReg .x21) : Cursor t base bytes v bit k :=
  ⟨ptr.trans old.ptr,end_.trans old.end_,count.trans old.count,(congrArg BitVec.toNat buf).trans old.buf,old.whole,old.input.same mem⟩

def refilled (s : MachineState) :=loaded (s.setPC (pcAt 41))
private theorem refill_keep (s : MachineState) (q : Reg) (safe : q∉([.x7,.x19,.x21,.x22] : List Reg)) :
    (refilled s).getReg q=s.getReg q := by cases q <;> first | rfl | (exfalso;apply safe;decide)

theorem read_byte (o : Oracle) (s : MachineState) (base bytes v bit k width : Nat) (small : width≤32)
    (few : k<width) (fits : bit+width≤8*bytes) (room : base+bytes≤MEMORY_BYTES)
    (pc : s.pc=pcAt 38) (want : s.getReg .x6=W width) (old : Cursor s base bytes v bit k) :
    let t:=refilled s
    Flow o s t 8 0 ∧ t.pc=pcAt 38 ∧ Cursor t base bytes v bit (k+8) ∧ t.mem=s.mem ∧
      ∀ q,q∉([.x7,.x19,.x21,.x22] : List Reg) → t.getReg q=s.getReg q := by
  let j:=(bit+k)/8
  have eqn : bit+k=8*j := by dsimp [j];have h:=old.whole;omega
  have within : j<bytes:=by omega
  have safe : base+j<2^64 ∧ base+bytes<2^64:=by change base+bytes≤2^36 at room;omega
  have less : (s.getReg .x22).ult (s.getReg .x6)=true:=by
    rw [old.count,want];simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show k<2^64 by omega),Nat.mod_eq_of_lt (show width<2^64 by omega),decide_eq_true few]
  have more : (s.getReg .x19).ult (s.getReg .x20)=true := by
    rw [old.ptr,old.end_]
    change (W (base+j)).ult (W (base+bytes))=true
    simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt safe.1,Nat.mod_eq_of_lt safe.2,decide_eq_true (Nat.add_lt_add_left within base)]
  have addr : s.getReg .x19=W (base+j):=old.ptr
  have av : accessValid (s.getReg .x19) 1=true := by rw [addr];apply access_ok <;> first | omega | simpa
  let t:=refilled s
  obtain ⟨_,ep,ptr,cnt,buf,mem⟩:=refill s pc less more av 0
  have read : (s.getByte (s.getReg .x19)).toNat=window v (bit+k) 8:=by rw [addr,eqn];exact old.input j within
  have bits : (s.getReg .x22).toNat%64=k:=by rw [old.count];simp [W,Nat.mod_eq_of_lt (show k<2^64 by omega),Nat.mod_eq_of_lt (show k<64 by omega)]
  have joined:=refill_byte v bit k (s.getReg .x21) (s.getByte (s.getReg .x19)) old.buf read
  have win := Nat.mod_lt (v/2^bit) (Nat.two_pow_pos (k+8))
  have pow : 2^(k+8)≤2^64:=Nat.pow_le_pow_right (by decide) (by omega)
  have z : t.getReg .x21=W (window v bit (k+8)):=by rw [show t.getReg .x21=_ from buf,bits];exact joined
  refine ⟨Check.plain_flow o (fun fuel=>(refill s pc less more av fuel).1),ep,⟨?_,?_,?_,?_,by omega,old.input.same mem⟩,mem,refill_keep s⟩
  · rw [show t.getReg .x19=_ from ptr,addr];apply (BitVec.ofNat_add (base+j) 1).symm.trans;apply congrArg W;omega
  · exact (refill_keep s _ (by decide)).trans old.end_
  · exact cnt.trans ((congrArg (·+8) old.count).trans (BitVec.ofNat_add k 8).symm)
  · rw [z,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show window v bit (k+8)<2^64 from lt_of_lt_of_le win pow)]

end CommitGolfCandidate.S5Machine.Reader
