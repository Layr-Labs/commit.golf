import CommitGolfCandidate.ProjectedHalfword
import RiscvZkvm.Rv64.Logic.ByteOps

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate.ProjectedHalfword
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

private theorem join_full (old data : Word) :
  replaceHalfword (replaceHalfword (replaceHalfword (replaceHalfword
    old 0 (extractHalfword data 0)) 1 (extractHalfword data 1))
    2 (extractHalfword data 2)) 3 (extractHalfword data 3) = data := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  interval_cases bit <;> simp [replaceHalfword,extractHalfword]

private theorem join_word (old data : Word) (a b : Nat) (ha : a<2) (hb : b<2) :
  replaceHalfword (replaceHalfword old (2*b) (extractHalfword data (2*a))) (2*b+1)
      (extractHalfword data (2*a+1)) = replaceWord32 old b (extractWord32 data a) := by
  interval_cases a <;> interval_cases b <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro bit bound <;>
    interval_cases bit <;> simp [replaceHalfword,extractHalfword,replaceWord32,extractWord32]

def addr (n : Nat) : Word := BitVec.ofNat 64 n
private theorem offset_addr (n : Nat) (fit : n < 2^64) :
    byteOffset (addr n) = n%8 := by
  unfold byteOffset addr
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  change n &&& (2^3-1) = n % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod n 3

private theorem align_addr (n : Nat) (fit : n<2^64) :
    alignToDword (addr n) = addr (n-n%8) := by
  have split := alignToDword_add_byteOffset (addr n)
  rw [offset_addr n fit] at split
  have split' : addr (n-n%8) + BitVec.ofNat 64 (n%8) = addr n := by
    change BitVec.ofNat 64 (n-n%8) + BitVec.ofNat 64 (n%8) = _
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel (Nat.mod_le _ _)]
    rfl
  have h := congrArg (fun x : Word => x-BitVec.ofNat 64 (n%8)) (split.trans split'.symm)
  simpa only [BitVec.add_sub_cancel] using h

private theorem addr_shift (n : Nat) :
    advance false (addr n) = addr (n+2) := by
  unfold addr
  rw [BitVec.ofNat_add]
  rfl

private theorem setMem_twice (s : MachineState) (a x y : Word) :
    (s.setMem a x).setMem a y = s.setMem a y := by
  unfold MachineState.setMem
  congr 1
  funext q
  by_cases h : q=a <;> simp [h]

private theorem get_set_half (st : MachineState) (n base slot : Nat)
    (ha : alignToDword (addr n) = addr base) (ho : byteOffset (addr n)/2 = slot) :
    st.getHalfword (addr n) = extractHalfword (st.getMem (addr base)) slot ∧
    ∀ v : BitVec 16, st.setHalfword (addr n) v = st.setMem (addr base)
        (replaceHalfword (st.getMem (addr base)) slot v) := by
  simp [MachineState.getHalfword, MachineState.setHalfword, ha, ho]

/-- One naturally aligned LD/SD has precisely the full memory effect of the original four
 sequential LHU/SH pairs, for every admitted pair of nonoverlapping addresses and every memory. -/
theorem dword_halfwords (state : MachineState) (source target : Nat)
    (sa : source%8=0) (ta : target%8=0) (sep : source+8≤target) (fit : target+8≤2^64) :
    copyLoopMemory false 4 state (addr source) (addr target) =
      state.setMem (addr target) (state.getMem (addr source)) := by
  have geo (base k : Nat) (al : base%8=0) (bnd : base+8≤2^64) (hk : k<8) :
      alignToDword (addr (base+k)) = addr base ∧ byteOffset (addr (base+k))/2 = k/2 := by
    rw [align_addr _ (by omega), offset_addr _ (by omega)]
    constructor
    · congr 1; omega
    · omega
  have sk (s : MachineState) (k : Nat) (hk : k<8) :=
    get_set_half s (source+k) source (k/2) (geo _ _ sa (by omega) hk).1 (geo _ _ sa (by omega) hk).2
  have tk (s : MachineState) (k : Nat) (hk : k<8) :=
    get_set_half s (target+k) target (k/2) (geo _ _ ta fit hk).1 (geo _ _ ta fit hk).2
  have ne : addr source ≠ addr target := by
    intro h
    have hv := congrArg BitVec.toNat h
    simp only [addr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : source < 2^64),
      Nat.mod_eq_of_lt (by omega : target < 2^64)] at hv
    omega
  simp only [copyLoopMemory,addr_shift,Nat.add_assoc,Nat.reduceAdd]
  have sk0 (s : MachineState) := (sk s 0 (by decide)).1
  have tk0 (s : MachineState) := (tk s 0 (by decide)).2
  simp only [Nat.add_zero,Nat.zero_div] at sk0 tk0
  simp only [sk0,tk0,fun s => (sk s 2 (by decide)).1,fun s => (tk s 2 (by decide)).2,
    fun s => (sk s 4 (by decide)).1,fun s => (tk s 4 (by decide)).2,
    fun s => (sk s 6 (by decide)).1,fun s => (tk s 6 (by decide)).2]
  simp only [Nat.reduceDiv, MachineState.getMem_setMem_ne ne, MachineState.getMem_setMem_eq,
    setMem_twice,join_full]

/-- One naturally aligned LWU/SW has precisely the full memory effect of two LHU/SH pairs,
 including the two possible four-byte slots of each independently aligned source/target dword. -/
theorem word_halfwords (state : MachineState) (source target : Nat)
    (sa : source%4=0) (ta : target%4=0) (sep : source+4≤target) (fit : target+4≤2^64) :
    copyLoopMemory false 2 state (addr source) (addr target) =
      state.setWord32 (addr target) (state.getWord32 (addr source)) := by
  let sb := source-source%8
  let tb := target-target%8
  let a := source%8/4
  let b := target%8/4
  have geo (base k : Nat) (al : base%4=0) (bnd : base+4≤2^64) (hk : k<4) :
      alignToDword (addr (base+k)) = addr (base-base%8) ∧
      byteOffset (addr (base+k))/2 = 2*(base%8/4)+k/2 := by
    rw [align_addr _ (by omega), offset_addr _ (by omega)]
    constructor
    · congr 1; omega
    · omega
  have sk (s : MachineState) (k : Nat) (hk : k<4) := get_set_half s (source+k) sb (2*a+k/2)
    (geo _ _ sa (by omega) hk).1 (geo _ _ sa (by omega) hk).2
  have tk (s : MachineState) (k : Nat) (hk : k<4) := get_set_half s (target+k) tb (2*b+k/2)
    (geo _ _ ta fit hk).1 (geo _ _ ta fit hk).2
  have ab : a<2 := by unfold a; omega
  have bb : b<2 := by unfold b; omega
  have ofa : byteOffset (addr source)/4=a := by rw [offset_addr _ (by omega)]
  have ofb : byteOffset (addr target)/4=b := by rw [offset_addr _ (by omega)]
  simp only [copyLoopMemory,addr_shift]
  have sk0 (s : MachineState) := (sk s 0 (by decide)).1
  have tk0 (s : MachineState) := (tk s 0 (by decide)).2
  simp only [Nat.add_zero,Nat.zero_div] at sk0 tk0
  simp only [sk0,tk0,fun s => (sk s 2 (by decide)).1,fun s => (tk s 2 (by decide)).2]
  simp only [Nat.reduceDiv,Nat.add_zero,MachineState.getMem_setMem_eq, setMem_twice,
    MachineState.getWord32,MachineState.setWord32, (geo _ 0 sa (by omega) (by decide)).1,
    (geo _ 0 ta fit (by decide)).1, ofa, ofb]
  rw [align_addr target (by omega),align_addr source (by omega)]
  change _=state.setMem (addr tb) (replaceWord32 (state.getMem (addr tb)) b (extractWord32 (state.getMem (addr sb)) a))
  by_cases eq : addr sb = addr tb
  · have n : sb=tb := by
      have h := congrArg BitVec.toNat eq
      simp only [addr,BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold sb;omega : sb<2^64),
        Nat.mod_eq_of_lt (by unfold tb;omega : tb<2^64)] at h
      exact h
    have hz : a=0 ∧ b=1 := by dsimp [a,b,sb,tb] at *;omega
    rw [eq,MachineState.getMem_setMem_eq, hz.1,hz.2]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [replaceHalfword,extractHalfword,replaceWord32,extractWord32]
  · rw [MachineState.getMem_setMem_ne eq, join_word _ _ _ _ ab bb]

#print axioms dword_halfwords
#print axioms word_halfwords

end TwoPermutationPrototype.PhaseOpening
