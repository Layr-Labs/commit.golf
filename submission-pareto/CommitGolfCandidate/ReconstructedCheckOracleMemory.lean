import CommitGolfCandidate.ReconstructedCheckParentRun
import RiscvZkvm.Rv64.Logic.ByteOps


namespace CommitGolfCandidate.Reconstruction.CheckOracleMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def atIndex (a : Loc) (i : Nat) : Loc := {a with offset:=a.offset+BitVec.ofNat 64 (8*i)}

theorem physical_index (env : Env) (a : Loc) (i : Nat) :
    physical env (atIndex a i) = physical env a+BitVec.ofNat 64 (8*i) := by
  simp [physical,atIndex,BitVec.add_assoc]

def install (dest : Loc) (q : Nat) (xs : Writes) : Nat→Writes
  | 0 => xs
  | n+1 => (atIndex dest n,.answer q n)::install dest q xs n

theorem safe_install (tab : Tables) (dest : Loc) (q : Nat) (xs : Writes) (prior : Safe tab xs)
    (n : Nat) (slots : ∀ i<n, tab.allowed (atIndex dest i)=true) : Safe tab (install dest q xs n) := by
  induction n with
  | zero => exact prior
  | succ n ih =>
    intro k h;rcases List.mem_cons.1 h with rfl|past
    · exact slots n (by omega)
    · exact ih (fun i hi=>slots i (by omega)) k past

private theorem mem_inside (env : Env) (dest : Loc) (q : Nat) (xs : Writes) (n j : Nat) (inside : j<n)
    (distinct : ∀ a<n, ∀ b<n, a≠b → physical env (atIndex dest a)≠physical env (atIndex dest b)) :
    memory env (physical env (atIndex dest j)) (install dest q xs n)=env.answer q j := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases eq : j=n
    · subst n;simp [install,memory,Term.val]
    · simp only [install,memory,ite_eq_right (distinct j inside n (by omega) eq)]
      exact ih (by omega) (fun a ha b hb=>distinct a (by omega) b (by omega))

private theorem mem_out (env : Env) (dest : Loc) (q : Nat) (xs : Writes) (p : Word) (n : Nat)
    (outside : ∀ i<n, p≠physical env (atIndex dest i)) :
    memory env p (install dest q xs n)=memory env p xs := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [install,memory,ite_eq_right (outside n (by omega))]
    exact ih (fun i hi=>outside i (by omega))

private theorem read_word (s : MachineState) (a : Nat) (ha : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  have part := read_buffer_slice s a 32 0 8 (by decide)
  have word := read_digest_word s a 0 ha (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using part.symm.trans word

private theorem written_word (n : Nat) (s : MachineState) (dst j : Nat) (answer : BitVec (64*n))
    (aligned : dst%8=0) (small : j<n) (size : dst+8*n≤2^64) :
    (writeBits s (BitVec.ofNat 64 dst) answer).getMem (BitVec.ofNat 64 (dst+8*j))=answer.extractLsb' (64*j) 64 := by
  rw [← read_word _ _ (by omega)]
  have slice := read_serialized_slice (writeBits s (BitVec.ofNat 64 dst) answer) answer (dst+8*j) (8*j) 8
  rw [show 64*j=8*(8*j) by omega]
  apply slice
  intro k hk
  have h := write_bits_byte s (BitVec.ofNat 64 dst) answer (8*j+k) (by omega) (by omega)
  simpa only [←BitVec.ofNat_add,Nat.add_assoc] using h

private theorem aligned_part (a j : Nat) (ha : a%8=0) :
    alignToDword (BitVec.ofNat 64 a+BitVec.ofNat 64 j)=BitVec.ofNat 64 (a+8*(j/8)) := by
  rw [←BitVec.ofNat_add]
  have off : byteOffset (BitVec.ofNat 64 (a+j))=j%8 := by
    unfold byteOffset
    rw [BitVec.toNat_and,BitVec.toNat_ofNat]
    change ((a+j)%2^64) &&& (2^3-1)=j%8
    rw [Nat.and_two_pow_sub_one_eq_mod];omega
  have parts := alignToDword_add_byteOffset (BitVec.ofNat 64 (a+j))
  rw [off] at parts
  have sum : BitVec.ofNat 64 (a+j)=BitVec.ofNat 64 (a+8*(j/8))+BitVec.ofNat 64 (j%8) := by
    rw [←BitVec.ofNat_add];congr 1;omega
  have eq := parts.trans sum
  exact (BitVec.add_left_inj _).1 eq

theorem reply (env : Env) (m : State) (s : MachineState) (h : Matches env m s) (dest : Loc) (q n : Nat)
    (answer : BitVec (64*n)) (value : ∀ i<n, env.answer q i=answer.extractLsb' (64*i) 64)
    (dst : Nat) (atDst : physical env dest=BitVec.ofNat 64 dst) (align : dst%8=0) (room : dst+8*n≤2^64) :
    Matches env {m with writes:=install dest q m.writes n,pc:=m.pc+4} (writeBits s (BitVec.ofNat 64 dst) answer) := by
  have place (i : Nat) : physical env (atIndex dest i)=BitVec.ofNat 64 (dst+8*i) := by
    rw [physical_index,atDst,BitVec.ofNat_add]
  have injective (i : Nat) (hi : i<n) (j : Nat) (hj : j<n) (ne : i≠j) :
      physical env (atIndex dest i)≠physical env (atIndex dest j) := by
    rw [place,place];intro eq
    have num := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : dst+8*i<2^64),
      Nat.mod_eq_of_lt (by omega : dst+8*j<2^64)] at num
    omega
  refine ⟨?_,fun r=>(writeBits_register _ _ _ _).trans (h.regs r),?_⟩
  · exact congrArg (·+4) h.pc
  · intro p
    by_cases hit : ∃ i<n, p=physical env (atIndex dest i)
    · obtain ⟨i,hi,rfl⟩ := hit
      change _=memory env _ (install ..)
      rw [mem_inside env dest q m.writes n i hi injective,place,written_word n s dst i answer align hi room,value i hi]
    · have diff (i : Nat) (hi : i<n) : p≠physical env (atIndex dest i) := fun eq=>hit ⟨i,hi,eq⟩
      change _=memory env _ (install ..)
      rw [mem_out env dest q m.writes p n diff,←h.mem]
      apply writeBits_memory_outside
      intro k hk
      rw [aligned_part dst k align,←place]
      exact diff (k/8) (by omega)

end CommitGolfCandidate.Reconstruction.CheckOracleMemory
