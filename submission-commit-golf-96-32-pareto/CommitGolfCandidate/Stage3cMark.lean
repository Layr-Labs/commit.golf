import CommitGolfCandidate.Stage3cBatchFrame
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def withMark (s : MachineState) (j : Nat) := s.setByte (W (1024+j)) 1

theorem mark_outside (s : MachineState) (j : Nat) (small : j<512) : Outside s (withMark s j) 1024 512 := by
  intro a inside al away
  have ne : W a≠alignToDword (W (1024+j)) := by
    rw [show alignToDword (W (1024+j))=W (1024+8*(j/8)) from word_address 1024 j (by decide)]
    intro eq;have h:=congrArg BitVec.toNat eq
    change a<2^36 at inside
    simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^64 by omega),
      Nat.mod_eq_of_lt (show 1024+8*(j/8)<2^64 by omega)] at h;omega
  exact MachineState.getMem_setMem_ne ne

theorem mark_seen (s : MachineState) (i : Index) (seen : List Index) (old : Marked s seen) :
    Marked (withMark s (i.val/32768)) (seen++[i]) := by
  let k:=i.val/32768
  have small : k<512:=above_bound i 15 (by decide)
  intro j lim
  have h:=set_byte_read s (W (1024+k)) (W (1024+j)) 1
  change byteAt (withMark s k) (1024+j)=(if W (1024+j)=W (1024+k) then 1 else byteAt s (1024+j)) at h
  rw [h,List.any_append,List.any_cons,List.any_nil,Bool.or_false]
  by_cases eq : j=k
  · subst j;simp [k]
  · have ne : W (1024+j)≠W (1024+k) := by
      intro hh;have z:=congrArg BitVec.toNat hh
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024+j<2^64 by omega),
        Nat.mod_eq_of_lt (show 1024+k<2^64 by omega)] at z;omega
    rw [if_neg ne,old j lim]
    have neq : i.val/32768≠j:=Ne.symm eq
    simp [neq]

theorem mark_input {s xs seen tree salt} (src : InputRows s xs seen tree salt) (size : xs.length≤LENGTH) (i : Index) :
    InputRows (withMark s (i.val/32768)) xs (seen++[i]) tree salt := by
  let frame:=mark_outside s (i.val/32768) (above_bound i 15 (by decide))
  refine ⟨src.sources.after_low size _ _ frame (by decide) (by decide) (by decide),?_,mark_seen s i seen src.marks⟩
  intro q h;exact (frame _ (by change _<2^36;omega) (by omega) (Or.inr (by omega))).trans (src.table q h)

theorem mark_cursor {s tree fs} (p : FieldCursor tree s fs) (n : Nat) (hn : n<512) (lim : widths fs≤542720) :
    FieldCursor tree (withMark s n) fs := by
  refine ⟨p.ptr,p.count,p.sixty,?_⟩
  intro good;have payload:=p.payload good
  refine ⟨payload.value,payload.ptr,payload.bits,payload.held,?_⟩
  intro j hj
  have q:=mark_outside s n hn (proofBase+8*j) (by change _<2^36;unfold proofBase;omega)
    (by unfold proofBase;omega) (Or.inr (by unfold proofBase;omega))
  exact (congrArg BitVec.toNat q).trans (payload.words j hj)
end CommitGolfCandidate.Chained.BinaryMachine.Open
