import CommitGolfCandidate.Stage3cReadWindow
import CommitGolfCandidate.Stage3cCheckStore
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt Outside)
def decoded (v bit n : Nat) := BitVec.ofNat 256 (window v bit n)
def fieldSlice (v bit n j : Nat) := (decoded v bit n).extractLsb' (64*j) 64

private theorem window_bound (v bit n : Nat) : window v bit n<2^n:=Nat.mod_lt _ (Nat.two_pow_pos _)
theorem decoded_toNat (v bit n : Nat) (small : n≤256) : (decoded v bit n).toNat=window v bit n := by
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (window_bound ..) (Nat.pow_le_pow_right (by decide) small))

theorem field_slice (v bit n j : Nat) (small : n≤256) :
    fieldSlice v bit n j=W (window v (bit+64*j) (min (n-64*j) 64)) := by
  have exp :=window_bound v bit n
  apply BitVec.eq_of_toNat_eq
  simp only [fieldSlice,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,decoded_toNat v bit n small,W,BitVec.toNat_ofNat]
  by_cases over : n≤64*j
  · have zero : n-64*j=0:=by omega
    rw [zero,Nat.zero_min,Nat.div_eq_of_lt (lt_of_lt_of_le exp (Nat.pow_le_pow_right (by decide) over))]
    simp [window,Nat.mod_one]
  · have covered : 64*j≤n:=by omega
    rw [window_high _ _ _ _ covered]
    by_cases full : 64≤n-64*j
    · rw [Nat.min_eq_right full,window_low _ _ _ _ full,Nat.mod_eq_of_lt (window_bound ..)]
    · rw [Nat.min_eq_left (by omega)]

theorem field_empty (v bit n j : Nat) (small : n≤256) (end_ : n≤64*j) : fieldSlice v bit n j=0 := by
  rw [field_slice _ _ _ _ small,Nat.sub_eq_zero_of_le end_];simp [window,W,Nat.mod_one]

def FieldMemory (s : MachineState) (dst v bit n filled : Nat) := ∀ j<4,
  wordAt s (dst+8*j)=if j<filled then fieldSlice v bit n j else 0

theorem field_memory_done (s : MachineState) (dst v bit n count : Nat) (small : n≤256)
    (all : n≤64*count) (space : dst+32≤MEMORY_BYTES) (al : dst%8=0) (data : FieldMemory s dst v bit n count) :
    readBuffer s dst 32=decoded v bit n := by
  let d:=decoded v bit n
  let t:=writeBits s (W dst) d
  have word (j : Nat) (hj : j<4) : wordAt s (dst+8*j)=wordAt t (dst+8*j) := by
    have rhs:=output_word s dst j d al hj
    change wordAt t (dst+8*j)=fieldSlice v bit n j at rhs
    rw [data j hj,rhs]
    split
    · rfl
    · symm;apply field_empty _ _ _ _ small (by omega)
  have eq:=read_digest_congr s t dst al word
  have value:=write_bits_digest s dst 0 d (by decide) (by decide)
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using eq.trans value

theorem field_memory_step {s t : MachineState} (dst v bit n j : Nat) (small : n≤256) (count : j<4)
    (space : dst+32≤MEMORY_BYTES) (al : dst%8=0) (old : FieldMemory s dst v bit n j)
    (mem : t.mem=(Check.store s (dst+8*j) (fieldSlice v bit n j)).mem) : FieldMemory t dst v bit n (j+1) := by
  intro i hi
  have eq:=congrFun mem (W (dst+8*i))
  by_cases same : i=j
  · subst i;rw [if_pos (Nat.lt_succ_self _)];exact eq.trans MachineState.getMem_setMem_eq
  · have frame:=Check.store_far s (dst+8*j) (fieldSlice v bit n j) (by omega) (dst+8*i) (by omega) (by omega) (by omega)
    apply (eq.trans (frame.trans (old i hi))).trans
    by_cases lo : i<j
    · simp only [if_pos lo,if_pos (by omega : i<j+1)]
    · simp only [if_neg lo,if_neg (by omega : ¬i<j+1)]
end CommitGolfCandidate.Chained.BinaryMachine.Reader
