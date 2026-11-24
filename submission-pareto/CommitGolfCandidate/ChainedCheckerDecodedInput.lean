import CommitGolfCandidate.ChainedCheckerClearRun
import CommitGolfCandidate.ChainedCheckerRecordUntrusted

section

/-! One concrete public-index mark write, projected before and after its store. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def checkerSeedOps : List Instr := [.LD .x30 .x2 0,.SRLI .x30 .x30 16,.ADDI .x30 .x30 256,
  .SLLI .x31 .x30 3,.ADD .x31 .x31 .x4,.SD .x31 .x10 0,
  .ADDI .x2 .x2 8,.ADDI .x3 .x3 4095,.BNE .x3 .x0 8160]
@[irreducible] def checkerSeedPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerSeedOps.getD index .EBREAK)) n
def checkerSeedAddress (s : MachineState) : Word :=
  (((s.getMem (s.getReg .x2) >>> 16)+256) <<< 3)+s.getReg .x4
theorem checker_seed_zero (s : MachineState) : checkerSeedPrefix 0 s=s := by rw [checkerSeedPrefix]; rfl
theorem checker_seed_succ (n : Nat) (s : MachineState) : checkerSeedPrefix (n+1) s=
    execInstrBr (checkerSeedPrefix n s) (checkerSeedOps.getD n .EBREAK) := by unfold checkerSeedPrefix; rfl
theorem checker_seed_at : OpsAt chainedCheckerImage (4096+4*35) checkerSeedOps :=
  chained_checker_slice_at 35 9 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

private theorem merged_ChainedCheckerSeedState_seed_guard_register (s : MachineState) (reg : Reg) :
    (execInstrBr s (.BNE .x3 .x0 8160)).getReg reg=s.getReg reg := by
  change (if _ then s.setPC _ else s.setPC _).getReg reg=_
  split <;> exact MachineState.getReg_setPC
private theorem merged_ChainedCheckerSeedState_seed_guard_memory (s : MachineState) (query : Word) :
    (execInstrBr s (.BNE .x3 .x0 8160)).getMem query=s.getMem query := by
  change (if _ then s.setPC _ else s.setPC _).getMem query=_
  split <;> exact MachineState.getMem_setPC
theorem checker_seed_prepare_register (n : Nat) (s : MachineState) (small : n≤5) (reg : Reg)
    (kept : reg≠.x30 ∧ reg≠.x31) : (checkerSeedPrefix n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 5) : (execInstrBr t (checkerSeedOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i <;> cases reg <;> simp at kept <;> rfl
  induction n with
  | zero => rw [checker_seed_zero]
  | succ n ih => rw [checker_seed_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_seed_prepare_memory (n : Nat) (s : MachineState) (small : n≤5) (query : Word) :
    (checkerSeedPrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 5) : (execInstrBr t (checkerSeedOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_seed_zero]
  | succ n ih => rw [checker_seed_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_seed_prepare_address (s : MachineState) :
    (checkerSeedPrefix 5 s).getReg .x31=checkerSeedAddress s := by
  have loaded (t : MachineState) : (execInstrBr t (.LD .x30 .x2 0)).getReg .x30=t.getMem (t.getReg .x2) := by
    change t.getMem (t.getReg .x2+signExtend12 0)=_
    rw [show signExtend12 0=0#64 by rfl,BitVec.add_zero]
  rw [checker_seed_succ]
  change (checkerSeedPrefix 4 s).getReg .x31+(checkerSeedPrefix 4 s).getReg .x4=_
  rw [checker_seed_prepare_register 4 s (by decide) .x4 ⟨by decide,by decide⟩,checker_seed_succ]
  change ((checkerSeedPrefix 3 s).getReg .x30 <<< 3)+s.getReg .x4=_
  rw [checker_seed_succ]
  change (((checkerSeedPrefix 2 s).getReg .x30+256) <<< 3)+s.getReg .x4=_
  rw [checker_seed_succ]
  change ((((checkerSeedPrefix 1 s).getReg .x30 >>> 16)+256) <<< 3)+s.getReg .x4=_
  rw [checker_seed_succ,checker_seed_zero]
  change ((((execInstrBr s (.LD .x30 .x2 0)).getReg .x30 >>> 16)+256) <<< 3)+s.getReg .x4=_
  rw [loaded]
  rfl

theorem checker_seed_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3,.x30,.x31]) :
    (checkerSeedPrefix 9 s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 9) : (execInstrBr t (checkerSeedOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i
    all_goals first | exact merged_ChainedCheckerSeedState_seed_guard_register t reg | (cases reg <;> simp at kept <;> rfl)
  have frame (n : Nat) (small : n≤9) : (checkerSeedPrefix n s).getReg reg=s.getReg reg := by
    induction n with
    | zero => rw [checker_seed_zero]
    | succ n ih => rw [checker_seed_succ,step _ ⟨n,by omega⟩,ih (by omega)]
  exact frame 9 (by decide)
theorem checker_seed_pointer (s : MachineState) : (checkerSeedPrefix 9 s).getReg .x2=s.getReg .x2+8 := by
  rw [checker_seed_succ]
  change (execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)).getReg .x2=_
  rw [merged_ChainedCheckerSeedState_seed_guard_register,checker_seed_succ]
  change (checkerSeedPrefix 7 s).getReg .x2=_
  rw [checker_seed_succ]
  change (checkerSeedPrefix 6 s).getReg .x2+8=_
  rw [checker_seed_succ]
  change (checkerSeedPrefix 5 s).getReg .x2+8=_
  rw [checker_seed_prepare_register 5 s (by decide) .x2 ⟨by decide,by decide⟩]
theorem checker_seed_counter (s : MachineState) : (checkerSeedPrefix 9 s).getReg .x3=s.getReg .x3-1 := by
  rw [checker_seed_succ]
  change (execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)).getReg .x3=_
  rw [merged_ChainedCheckerSeedState_seed_guard_register,checker_seed_succ]
  change (checkerSeedPrefix 7 s).getReg .x3+signExtend12 4095=_
  rw [checker_seed_succ]
  change (checkerSeedPrefix 6 s).getReg .x3+signExtend12 4095=_
  rw [checker_seed_succ]
  change (checkerSeedPrefix 5 s).getReg .x3+signExtend12 4095=_
  rw [checker_seed_prepare_register 5 s (by decide) .x3 ⟨by decide,by decide⟩,BitVec.sub_eq_add_neg]
  rfl
theorem checker_seed_memory (s : MachineState) (query : Word) :
    (checkerSeedPrefix 9 s).getMem query=if query=checkerSeedAddress s then s.getReg .x10 else s.getMem query := by
  have store (t : MachineState) : (execInstrBr t (.SD .x31 .x10 0)).getMem query=
      if query=t.getReg .x31 then t.getReg .x10 else t.getMem query := by
    change (if query==t.getReg .x31+signExtend12 0 then _ else _)=_
    simp only [show signExtend12 0=0#64 by rfl,BitVec.add_zero,beq_iff_eq,MachineState.getMem]
  rw [checker_seed_succ]
  change (execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)).getMem query=_
  rw [merged_ChainedCheckerSeedState_seed_guard_memory,checker_seed_succ]
  change (checkerSeedPrefix 7 s).getMem query=_
  rw [checker_seed_succ]
  change (checkerSeedPrefix 6 s).getMem query=_
  rw [checker_seed_succ]
  change (execInstrBr (checkerSeedPrefix 5 s) (.SD .x31 .x10 0)).getMem query=_
  rw [store,checker_seed_prepare_address,checker_seed_prepare_register 5 s (by decide) .x10 ⟨by decide,by decide⟩,
    checker_seed_prepare_memory 5 s (by decide)]

theorem checker_seed_group_word (index : Index) :
    (BitVec.ofNat 64 index.val >>> 16)+256=BitVec.ofNat 64 (capGroup index) := by
  have bound := index.isLt
  have fit : index.val<2^64 := Nat.lt_trans bound (by decide +kernel)
  have shift : BitVec.ofNat 64 index.val >>> 16=BitVec.ofNat 64 (index.val/65536) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.shiftRight_eq_div_pow]
    change index.val/65536=(index.val/65536)%2^64
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [shift]
  change BitVec.ofNat 64 (index.val/65536)+BitVec.ofNat 64 256=_
  rw [←BitVec.ofNat_add]
  congr 1
  change index.val/65536+256=(16777216+index.val)/65536
  omega
theorem checker_seed_address_eq (s : MachineState) (index : Index) (base : s.getReg .x4=4096#64)
    (loaded : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val) :
    checkerSeedAddress s=BitVec.ofNat 64 (4096+8*capGroup index) := by
  rw [checkerSeedAddress,loaded,checker_seed_group_word,base,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (capGroup index)*BitVec.ofNat 64 8+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Installed leaf-mark iteration, with physical access and original-ABI frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_seed_group_bounds (index : Index) : 256≤capGroup index ∧ capGroup index<512 := by
  have bound : index.val<16777216 := index.isLt
  change 256≤(16777216+index.val)/65536 ∧ (16777216+index.val)/65536<512
  omega
theorem checker_seed_prepare_pc (n : Nat) (s : MachineState) (small : n≤8) :
    (checkerSeedPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 8) : (execInstrBr t (checkerSeedOps.getD i.val .EBREAK)).pc=t.pc+4 := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_seed_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_seed_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1
theorem checker_seed_store_access (s : MachineState) (index : Index) (base : s.getReg .x4=4096#64)
    (loaded : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val) :
    accessValid ((checkerSeedPrefix 5 s).getReg .x31) 8=true := by
  rw [checker_seed_prepare_address,checker_seed_address_eq s index base loaded]
  have bounds := checker_seed_group_bounds index
  have fit : 4096+8*capGroup index<2^64 := by omega
  have aligned : (4096+8*capGroup index)%8=0 := by omega
  simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,MEMORY_BYTES,aligned]
  omega
theorem checker_seed_execution (s : MachineState) (pc : s.pc=4096+4*35)
    (index : Index) (base : s.getReg .x4=4096#64)
    (loaded : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val)
    (loadValid : accessValid (s.getReg .x2) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSeedPrefix 9 s) coins
          return result.charge 9 0) := by
  have storeValid := checker_seed_store_access s index base loaded
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_seed_zero s]
  apply execute_unit_steps (states := fun n => checkerSeedPrefix n s)
  intro i inside
  refine ⟨.base (checkerSeedOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_seed_at i inside
    rw [checker_seed_prepare_pc i s (by omega),pc]
  · rw [checker_seed_succ]
    interval_cases i
    · change (if accessValid ((checkerSeedPrefix 0 s).getReg .x2+0) 8 then _ else _)=_
      rw [checker_seed_zero]
      exact ite_eq_left (by simpa using loadValid)
    · rfl
    · rfl
    · rfl
    · rfl
    · change (if accessValid ((checkerSeedPrefix 5 s).getReg .x31+0) 8 then _ else _)=_
      exact ite_eq_left (by simpa using storeValid)
    · rfl
    · rfl
    · rfl
  · interval_cases i <;> rfl

theorem checker_seed_next_counter (s : MachineState) (count : Nat)
    (counter : s.getReg .x3=BitVec.ofNat 64 (count+1)) :
    (checkerSeedPrefix 9 s).getReg .x3=BitVec.ofNat 64 count := by
  rw [checker_seed_counter,counter]
  change BitVec.ofNat 64 (count+1)-BitVec.ofNat 64 1=_
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),Nat.add_sub_cancel]
theorem checker_seed_next_pc (s : MachineState) (count : Nat) (small : count<LENGTH)
    (pc : s.pc=4096+4*35) (counter : s.getReg .x3=BitVec.ofNat 64 (count+1)) :
    (checkerSeedPrefix 9 s).pc=if count=0 then 4096+4*44 else 4096+4*35 := by
  have prior : (checkerSeedPrefix 8 s).getReg .x3=BitVec.ofNat 64 count := by
    have frame (t : MachineState) : (execInstrBr t (.BNE .x3 .x0 8160)).getReg .x3=t.getReg .x3 := by
      change (if _ then t.setPC _ else t.setPC _).getReg .x3=_
      split <;> exact MachineState.getReg_setPC
    have result := checker_seed_next_counter s count counter
    rw [checker_seed_succ] at result
    exact (frame _).symm.trans result
  rw [checker_seed_succ]
  change (execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)).pc=_
  by_cases last : count=0
  · have same : execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)=
        (checkerSeedPrefix 8 s).setPC ((checkerSeedPrefix 8 s).pc+4) := by
      apply ite_eq_right
      change ¬((checkerSeedPrefix 8 s).getReg .x3 != 0#64)=true
      rw [prior,last]
      decide
    rw [same]
    change (checkerSeedPrefix 8 s).pc+4=_
    rw [checker_seed_prepare_pc 8 s (by decide),pc,ite_eq_left last]
    rfl
  · have fit : count<2^64 := Nat.lt_trans small (by decide +kernel)
    have different : BitVec.ofNat 64 count≠0#64 := word_of_nat_ne count 0 fit (by decide) last
    have same : execInstrBr (checkerSeedPrefix 8 s) (.BNE .x3 .x0 8160)=
        (checkerSeedPrefix 8 s).setPC ((checkerSeedPrefix 8 s).pc+signExtend13 8160) := by
      apply ite_eq_left
      change ((checkerSeedPrefix 8 s).getReg .x3 != 0#64)=true
      rw [prior]
      exact bne_iff_ne.mpr different
    rw [same]
    change (checkerSeedPrefix 8 s).pc+signExtend13 8160=_
    rw [checker_seed_prepare_pc 8 s (by decide),pc,ite_eq_right last]
    rfl

theorem checker_seed_node_memory (s : MachineState) (index : Index) (base : s.getReg .x4=4096#64)
    (loaded : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val) (one : s.getReg .x10=1#64)
    (node : Nat) (small : node<512) :
    (checkerSeedPrefix 9 s).getMem (BitVec.ofNat 64 (4096+8*node))=
      if node=capGroup index then 1#64 else s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  rw [checker_seed_memory,checker_seed_address_eq s index base loaded,one]
  by_cases same : node=capGroup index
  · simp [same]
  · have bounds := checker_seed_group_bounds index
    have different : BitVec.ofNat 64 (4096+8*node)≠BitVec.ofNat 64 (4096+8*capGroup index) :=
      word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    rw [ite_eq_right different,ite_eq_right same]
theorem checker_seed_saved_abi (original s : MachineState) (index : Index) (base : s.getReg .x4=4096#64)
    (loaded : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val) (saved : CheckerSavedABI original s) :
    CheckerSavedABI original (checkerSeedPrefix 9 s) := by
  apply checker_saved_abi_frame original s _ saved
  intro slot
  rw [checker_seed_memory,checker_seed_address_eq s index base loaded]
  apply ite_eq_right
  have bounds := checker_seed_group_bounds index
  have range := checker_saved_byte_range slot 0 (by decide)
  have low : 8192<checkingMetadataBase := by decide +kernel
  apply word_of_nat_ne _ _ (by omega) (by omega)
  omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Leaf seeding reads only the ABI position words and preserves all saved ABI slots. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
attribute [local irreducible] execute

structure CheckerSeedReady (indices : List Index) (s : MachineState) (base : Nat) : Prop where
  pointer : s.getReg .x2=BitVec.ofNat 64 base
  counter : s.getReg .x3=BitVec.ofNat 64 indices.length
  markBase : s.getReg .x4=4096#64
  one : s.getReg .x10=1#64
  bounded : indices.length≤LENGTH
  lower : 32768≤base
  room : base+8*indices.length≤MEMORY_BYTES
  aligned : base%8=0
  words : ∀ ordinal : Nat, ∀ present : ordinal < indices.length,
    s.getMem (BitVec.ofNat 64 (base+8*ordinal))=BitVec.ofNat 64 indices[ordinal].val

theorem CheckerSeedReady.head {index : Index} {indices : List Index} {s : MachineState} {base : Nat}
    (ready : CheckerSeedReady (index::indices) s base) : s.getMem (s.getReg .x2)=BitVec.ofNat 64 index.val := by
  rw [ready.pointer]
  have point := ready.words 0 (by simp)
  rw [Nat.mul_zero,Nat.add_zero,List.getElem_cons_zero] at point
  exact point
theorem CheckerSeedReady.access {index : Index} {indices : List Index} {s : MachineState} {base : Nat}
    (ready : CheckerSeedReady (index::indices) s base) : accessValid (s.getReg .x2) 8=true := by
  have room := ready.room
  have memoryFit : MEMORY_BYTES<2^64 := by decide +kernel
  have fit : base<2^64 := by simp only [List.length_cons] at room; omega
  rw [ready.pointer]
  simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,ready.aligned]
  simp only [List.length_cons] at room
  omega
theorem CheckerSeedReady.tail {index : Index} {indices : List Index} {s : MachineState} {base : Nat}
    (ready : CheckerSeedReady (index::indices) s base) :
    CheckerSeedReady indices (checkerSeedPrefix 9 s) (base+8) := by
  have lengthBound := ready.bounded
  have room := ready.room
  simp only [List.length_cons] at lengthBound room
  have memoryFit : MEMORY_BYTES<2^64 := by decide +kernel
  refine ⟨?_,?_,?_,?_,by omega,by have := ready.lower; omega,by omega,by have := ready.aligned; omega,?_⟩
  · rw [checker_seed_pointer,ready.pointer]
    exact (BitVec.ofNat_add _ _).symm
  · exact checker_seed_next_counter s indices.length ready.counter
  · rw [checker_seed_register s .x4 (by decide)]; exact ready.markBase
  · rw [checker_seed_register s .x10 (by decide)]; exact ready.one
  · intro ordinal present
    rw [checker_seed_memory,checker_seed_address_eq s index ready.markBase ready.head,ite_eq_right]
    · have source := ready.words (ordinal+1) (by simp; omega)
      have address : base+8*(ordinal+1)=base+8+8*ordinal := by omega
      simpa only [address,List.getElem_cons_succ] using source
    · have groupBound := checker_seed_group_bounds index
      apply word_of_nat_ne _ _ (by omega) (by omega)
      have lower := ready.lower
      omega

@[irreducible] def checkerSeedStream : List Index → MachineState → MachineState
  | [],s => s
  | _::indices,s => checkerSeedStream indices (checkerSeedPrefix 9 s)
theorem checker_seed_stream_nil (s : MachineState) : checkerSeedStream [] s=s := by rw [checkerSeedStream]
theorem checker_seed_stream_cons (index : Index) (indices : List Index) (s : MachineState) :
    checkerSeedStream (index::indices) s=checkerSeedStream indices (checkerSeedPrefix 9 s) := by rw [checkerSeedStream]

theorem checker_seed_stream_execution (indices : List Index) (s : MachineState) (base : Nat)
    (ready : CheckerSeedReady indices s base) (pc : s.pc=if indices=[] then 4096+4*44 else 4096+4*35)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9*indices.length+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSeedStream indices s) coins
          return result.charge (9*indices.length) 0) := by
  induction indices generalizing s base with
  | nil => simp [checker_seed_stream_nil,Execution.charge]
  | cons index indices ih =>
    have headPC : s.pc=4096+4*35 := by simpa using pc
    have small : indices.length<LENGTH := by have := ready.bounded; simp only [List.length_cons] at this; omega
    have nextPC : (checkerSeedPrefix 9 s).pc=if indices=[] then 4096+4*44 else 4096+4*35 := by
      simpa only [List.length_eq_zero_iff] using checker_seed_next_pc s indices.length small headPC ready.counter
    rw [List.length_cons,show 9*(indices.length+1)+fuel=9+(9*indices.length+fuel) by omega,
      checker_seed_execution s headPC index ready.markBase ready.head ready.access,
      ih _ (base+8) ready.tail nextPC,checker_seed_stream_cons]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem checker_seed_stream_register (indices : List Index) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x30,.x31]) : (checkerSeedStream indices s).getReg reg=s.getReg reg := by
  induction indices generalizing s with
  | nil => rw [checker_seed_stream_nil]
  | cons index indices ih => rw [checker_seed_stream_cons,ih,checker_seed_register s reg kept]
theorem checker_seed_stream_memory_frame (indices : List Index) (s : MachineState) (base : Nat)
    (ready : CheckerSeedReady indices s base) (query : Word)
    (away : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerSeedStream indices s).getMem query=s.getMem query := by
  induction indices generalizing s base with
  | nil => rw [checker_seed_stream_nil]
  | cons index indices ih =>
    rw [checker_seed_stream_cons,ih _ (base+8) ready.tail,checker_seed_memory,
      checker_seed_address_eq s index ready.markBase ready.head]
    exact ite_eq_right (away _ (checker_seed_group_bounds index).2)
theorem checker_seed_stream_content (indices : List Index) (s : MachineState) (base : Nat)
    (ready : CheckerSeedReady indices s base) (node : Nat) (inside : node<512) :
    (checkerSeedStream indices s).getMem (BitVec.ofNat 64 (4096+8*node))=
      if node∈indices.map capGroup then 1#64 else s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  induction indices generalizing s base with
  | nil => simp [checker_seed_stream_nil]
  | cons index indices ih =>
    rw [checker_seed_stream_cons,ih _ (base+8) ready.tail,
      checker_seed_node_memory s index ready.markBase ready.head ready.one node inside]
    by_cases same : node=capGroup index <;> by_cases member : node∈indices.map capGroup <;> simp [same,member]
theorem checker_seed_stream_saved_abi (original : MachineState) (indices : List Index) (s : MachineState) (base : Nat)
    (ready : CheckerSeedReady indices s base) (saved : CheckerSavedABI original s) :
    CheckerSavedABI original (checkerSeedStream indices s) := by
  induction indices generalizing s base with
  | nil => rw [checker_seed_stream_nil]; exact saved
  | cons index indices ih =>
    rw [checker_seed_stream_cons]
    exact ih _ (base+8) ready.tail (checker_seed_saved_abi original s index ready.markBase ready.head saved)

end CommitGolfCandidate.Chained.Native

end

section

/-! Public ABI words loaded for the delivered checker, independently of proof contents. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem checker_input_registers (input : CheckInput) :
    let s := Artifact.submission.initialState .check input
    s.pc=4096 ∧ s.getReg .x11=4294971392 ∧ s.getReg .x13=5905584160 ∧
    s.getReg .x14=6039801952 ∧ s.getReg .x15=10334769248 ∧
    s.getReg .x16=BitVec.ofNat 64 input.positions.card ∧
    s.getReg .x17=BitVec.ofNat 64 input.proof.length := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem merged_ChainedCheckerInput_checker_input_read_word (state : MachineState) (address : Nat) (aligned : address%8=0) :
    readBuffer state address 8=state.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice state address 32 0 8 (by decide)
  have word := read_digest_word state address 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using slice.symm.trans word

theorem checker_input_position (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card) :
    (Artifact.submission.initialState .check input).getMem (BitVec.ofNat 64 (5905584160+8*ordinal))=
      BitVec.ofNat 64 ((input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)).val := by
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card≤16777216 := cardinal
  let index := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)
  have indexBound : index.val<16777216 := index.isLt
  have bytes (offset : Nat) (inside : offset<8) :
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 (5905584160+8*ordinal+offset))=
        (BitVec.ofNat 64 index.val).extractLsb' (8*offset) 8 := by
    rw [initial_input_byte Artifact.submission .check input _ (by omega)]
    have outside : ¬ (Artifact.submission.layout.commitment≤5905584160+8*ordinal+offset ∧
        5905584160+8*ordinal+offset<Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
      change ¬ (4294971392≤5905584160+8*ordinal+offset ∧ 5905584160+8*ordinal+offset<4294971424)
      omega
    have selected : Artifact.submission.layout.indices≤5905584160+8*ordinal+offset ∧
        5905584160+8*ordinal+offset<Artifact.submission.layout.indices+8*(input.positions.sort (· ≤ ·)).length := by
      change 5905584160≤_ ∧ _<5905584160+8*_
      rw [Finset.length_sort]
      omega
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,
      outside,decide_false,selected,and_self,decide_true]
    rw [show Artifact.submission.layout.indices=5905584160 by rfl]
    have quotient : (5905584160+8*ordinal+offset-5905584160)/8=ordinal := by omega
    have remainder : (5905584160+8*ordinal+offset-5905584160)%8=offset := by omega
    rw [quotient,remainder,List.getElem?_eq_getElem (by simpa using present)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,BitVec.extractLsb',Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : index.val<2^64)]
    rfl
  have decoded := read_serialized_slice (Artifact.submission.initialState .check input)
    (BitVec.ofNat 64 index.val) (5905584160+8*ordinal) 0 8 (by simpa only [Nat.zero_add] using bytes)
  rw [merged_ChainedCheckerInput_checker_input_read_word _ _ (by omega)] at decoded
  change (Artifact.submission.initialState .check input).getMem (BitVec.ofNat 64 (5905584160+8*ordinal))=
    (BitVec.ofNat 64 index.val).extractLsb' 0 64 at decoded
  rw [BitVec.extractLsb'_eq_self] at decoded
  exact decoded

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual source/count setup for the public-index leaf-seeding loop. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerSeedInitOps : List Instr := [.ADDI .x2 .x13 0,.ADDI .x3 .x16 0,.ADDI .x10 .x0 1]
@[irreducible] def checkerSeedInitPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerSeedInitOps.getD index .EBREAK)) n
theorem checker_seed_init_zero (s : MachineState) : checkerSeedInitPrefix 0 s=s := by rw [checkerSeedInitPrefix]; rfl
theorem checker_seed_init_succ (n : Nat) (s : MachineState) : checkerSeedInitPrefix (n+1) s=
    execInstrBr (checkerSeedInitPrefix n s) (checkerSeedInitOps.getD n .EBREAK) := by unfold checkerSeedInitPrefix; rfl
theorem checker_seed_init_at : OpsAt chainedCheckerImage (4096+4*32) checkerSeedInitOps :=
  chained_checker_slice_at 32 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_seed_init_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3,.x10]) :
    (checkerSeedInitPrefix 3 s).getReg reg=s.getReg reg := by
  rw [checkerSeedInitPrefix]
  cases reg <;> simp at kept <;> rfl
theorem checker_seed_init_memory (s : MachineState) (query : Word) :
    (checkerSeedInitPrefix 3 s).getMem query=s.getMem query := by rw [checkerSeedInitPrefix]; rfl
theorem checker_seed_init_pointer (s : MachineState) : (checkerSeedInitPrefix 3 s).getReg .x2=s.getReg .x13 := by
  rw [checkerSeedInitPrefix]
  change s.getReg .x13+0#64=_
  exact BitVec.add_zero _
theorem checker_seed_init_count (s : MachineState) : (checkerSeedInitPrefix 3 s).getReg .x3=s.getReg .x16 := by
  rw [checkerSeedInitPrefix]
  change s.getReg .x16+0#64=_
  exact BitVec.add_zero _
theorem checker_seed_init_one (s : MachineState) : (checkerSeedInitPrefix 3 s).getReg .x10=1#64 := by
  rw [checkerSeedInitPrefix]; rfl
theorem checker_seed_init_pc (n : Nat) (s : MachineState) (small : n≤3) :
    (checkerSeedInitPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 3) : (execInstrBr t (checkerSeedInitOps.getD i.val .EBREAK)).pc=t.pc+4 := by fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_seed_init_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_seed_init_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1
theorem checker_seed_init_execution (s : MachineState) (pc : s.pc=4096+4*32) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (3+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSeedInitPrefix 3 s) coins
          return result.charge 3 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_seed_init_zero s]
  apply execute_unit_steps (states := fun n => checkerSeedInitPrefix n s)
  intro i inside
  refine ⟨.base (checkerSeedInitOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_seed_init_at i inside
    rw [checker_seed_init_pc i s (by omega),pc]
  · rw [checker_seed_init_succ]; interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native

end

section

/-! Entry through leaf seeding, instantiated with the delivered input loader. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
attribute [local irreducible] execute

private theorem merged_ChainedCheckerSeedEntry_input_card_bound (input : CheckInput) : input.positions.card≤16777216 := by
  have bound : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  exact bound

@[irreducible] def checkerSeedInputStart (input : CheckInput) : MachineState :=
  checkerSeedInitPrefix 3 (checkerMarksClearedState (Artifact.submission.initialState .check input))
theorem checker_seed_input_start_eq (input : CheckInput) : checkerSeedInputStart input=
    checkerSeedInitPrefix 3 (checkerMarksClearedState (Artifact.submission.initialState .check input)) := by rw [checkerSeedInputStart]

theorem checker_input_indices_preserved (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card) :
    (checkerMarksClearedState (Artifact.submission.initialState .check input)).getMem
      (BitVec.ofNat 64 (5905584160+8*ordinal))=
    (Artifact.submission.initialState .check input).getMem (BitVec.ofNat 64 (5905584160+8*ordinal)) := by
  have card := merged_ChainedCheckerSeedEntry_input_card_bound input
  have sourceFit : 5905584160+8*16777216<2^64 := by decide +kernel
  have before : 5905584160+8*16777216<checkingMetadataBase := by decide +kernel
  apply checker_marks_cleared_memory_frame
  · intro slot
    have range := checker_saved_byte_range slot 0 (by decide)
    apply word_of_nat_ne _ _ (by omega) (by omega)
    omega
  · intro node inside
    apply word_of_nat_ne _ _ (by omega) (by omega)
    omega

theorem checker_seed_input_ready (input : CheckInput) :
    CheckerSeedReady (input.positions.sort (· ≤ ·)) (checkerSeedInputStart input) 5905584160 := by
  have regs := checker_input_registers input
  have card := merged_ChainedCheckerSeedEntry_input_card_bound input
  rw [checker_seed_input_start_eq]
  refine ⟨?_,?_,?_,checker_seed_init_one _,?_,by decide,?_,by decide,?_⟩
  · rw [checker_seed_init_pointer,checker_marks_cleared_register _ .x13 (by decide)]
    exact regs.2.2.1
  · rw [checker_seed_init_count,checker_marks_cleared_register _ .x16 (by decide),Finset.length_sort]
    exact regs.2.2.2.2.2.1
  · rw [checker_seed_init_register _ .x4 (by decide),checker_marks_cleared_base]
  · rw [Finset.length_sort]; exact card
  · rw [Finset.length_sort]
    change 5905584160+8*input.positions.card≤68719476736
    omega
  · intro ordinal present
    have present' : ordinal < input.positions.card := by simpa only [Finset.length_sort] using present
    rw [checker_seed_init_memory,checker_input_indices_preserved input ordinal present']
    exact checker_input_position input ordinal present'

theorem checker_seed_stream_control (indices : List Index) (s : MachineState) (base : Nat)
    (ready : CheckerSeedReady indices s base) (pc : s.pc=if indices=[] then 4096+4*44 else 4096+4*35) :
    (checkerSeedStream indices s).pc=4096+4*44 ∧ (checkerSeedStream indices s).getReg .x3=0#64 := by
  induction indices generalizing s base with
  | nil => rw [checker_seed_stream_nil]; exact ⟨by simpa using pc,ready.counter⟩
  | cons index indices ih =>
    have headPC : s.pc=4096+4*35 := by simpa using pc
    have small : indices.length<LENGTH := by have := ready.bounded; simp only [List.length_cons] at this; omega
    have nextPC : (checkerSeedPrefix 9 s).pc=if indices=[] then 4096+4*44 else 4096+4*35 := by
      simpa only [List.length_eq_zero_iff] using checker_seed_next_pc s indices.length small headPC ready.counter
    rw [checker_seed_stream_cons]
    exact ih _ (base+8) ready.tail nextPC

theorem checker_seed_input_nonempty (input : CheckInput) (nonempty : input.positions.card≠0) :
    (Artifact.submission.initialState .check input).getReg .x16≠0#64 := by
  rw [(checker_input_registers input).2.2.2.2.2.1]
  have card := merged_ChainedCheckerSeedEntry_input_card_bound input
  apply word_of_nat_ne _ _ (by omega) (by decide) nonempty
theorem checker_seed_input_bounds (input : CheckInput) (lower : 482*input.positions.card ≤ input.proof.length)
    (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerAdmissionBounds (Artifact.submission.initialState .check input) := by
  have regs := checker_input_registers input
  exact checker_admission_bounds_of_length _ _ _ (by simpa [Index] using Finset.card_le_univ input.positions)
    regs.2.2.2.2.2.1 regs.2.2.2.2.2.2 lower upper
theorem checker_seed_input_start_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerSeedInputStart input).pc=4096+4*35 := by
  rw [checker_seed_input_start_eq,checker_seed_init_pc 3 _ (by decide),
    checker_marks_cleared_pc _ (checker_input_registers input).1 (checker_seed_input_bounds input lower upper)
      (checker_seed_input_nonempty input nonempty)]
  rfl
theorem checker_seed_input_start_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2074+fuel) (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSeedInputStart input) coins
          return result.charge 2074 0) := by
  have bounds := checker_seed_input_bounds input lower upper
  have count := checker_seed_input_nonempty input nonempty
  have pc := (checker_input_registers input).1
  rw [checker_seed_input_start_eq,show 2074+fuel=2071+(3+fuel) by omega,
    checker_admission_marks_clear_execution _ pc bounds count,
    checker_seed_init_execution _ (checker_marks_cleared_pc _ pc bounds count)]
  simp [Execution.charge,←Nat.add_assoc]

@[irreducible] def checkerSeededInputState (input : CheckInput) : MachineState :=
  checkerSeedStream (input.positions.sort (· ≤ ·)) (checkerSeedInputStart input)
theorem checker_seeded_input_eq (input : CheckInput) : checkerSeededInputState input=
    checkerSeedStream (input.positions.sort (· ≤ ·)) (checkerSeedInputStart input) := by rw [checkerSeededInputState]
theorem checker_seeded_input_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2074+9*input.positions.card+fuel)
        (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSeededInputState input) coins
          return result.charge (2074+9*input.positions.card) 0) := by
  have present : input.positions.sort (· ≤ ·)≠[] := by
    intro empty
    have length := congrArg List.length empty
    rw [Finset.length_sort] at length
    exact nonempty length
  have pc : (checkerSeedInputStart input).pc=if input.positions.sort (· ≤ ·)=[] then 4096+4*44 else 4096+4*35 := by
    rw [ite_eq_right present]
    exact checker_seed_input_start_pc input nonempty lower upper
  rw [checker_seeded_input_eq,show 2074+9*input.positions.card+fuel=2074+(9*(input.positions.sort (· ≤ ·)).length+fuel) by rw [Finset.length_sort]; omega,
    checker_seed_input_start_execution input nonempty lower upper,
    checker_seed_stream_execution _ _ 5905584160 (checker_seed_input_ready input) pc]
  simp [Execution.charge,Finset.length_sort,←Nat.add_assoc]
theorem checker_seeded_input_marks (input : CheckInput) (node : Nat) (inside : node<512) :
    (checkerSeededInputState input).getMem (BitVec.ofNat 64 (4096+8*node))=
      if node∈(input.positions.sort (· ≤ ·)).map capGroup then 1#64 else 0#64 := by
  rw [checker_seeded_input_eq,checker_seed_stream_content _ _ 5905584160 (checker_seed_input_ready input) node inside,
    checker_seed_input_start_eq,checker_seed_init_memory,checker_marks_cleared_content _ node inside]
theorem checker_seeded_input_saved_abi (input : CheckInput) :
    CheckerSavedABI (Artifact.submission.initialState .check input) (checkerSeededInputState input) := by
  rw [checker_seeded_input_eq]
  apply checker_seed_stream_saved_abi _ _ _ 5905584160 (checker_seed_input_ready input)
  rw [checker_seed_input_start_eq]
  exact checker_saved_abi_frame _ _ _ (checker_marks_cleared_saved_abi _)
    (fun _ => checker_seed_init_memory _ _)

end CommitGolfCandidate.Chained.Native

end

section

/-! Projected state of one installed descending cap-mark parent iteration. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def checkerParentOps : List Instr := [.SLLI .x31 .x30 4,.ADD .x31 .x31 .x4,
  .LD .x2 .x31 0,.LD .x3 .x31 8,.OR .x2 .x2 .x3,.SLLI .x31 .x30 3,
  .ADD .x31 .x31 .x4,.SD .x31 .x2 0,.ADDI .x30 .x30 4095,.BNE .x30 .x0 8156]
@[irreducible] def checkerParentPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerParentOps.getD index .EBREAK)) n
def checkerParentChildAddress (s : MachineState) : Word := (s.getReg .x30 <<< 4)+s.getReg .x4
def checkerParentAddress (s : MachineState) : Word := (s.getReg .x30 <<< 3)+s.getReg .x4
def checkerParentValue (s : MachineState) : Word :=
  s.getMem (checkerParentChildAddress s) ||| s.getMem (checkerParentChildAddress s+8)
theorem checker_parent_zero (s : MachineState) : checkerParentPrefix 0 s=s := by rw [checkerParentPrefix]; rfl
theorem checker_parent_succ (n : Nat) (s : MachineState) : checkerParentPrefix (n+1) s=
    execInstrBr (checkerParentPrefix n s) (checkerParentOps.getD n .EBREAK) := by unfold checkerParentPrefix; rfl
theorem checker_parent_at : OpsAt chainedCheckerImage (4096+4*45) checkerParentOps :=
  chained_checker_slice_at 45 10 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_parent_prepare_register (n : Nat) (s : MachineState) (small : n≤7) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x31]) : (checkerParentPrefix n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 7) : (execInstrBr t (checkerParentOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i <;> cases reg <;> simp at kept <;> rfl
  induction n with
  | zero => rw [checker_parent_zero]
  | succ n ih => rw [checker_parent_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_parent_prepare_memory (n : Nat) (s : MachineState) (small : n≤7) (query : Word) :
    (checkerParentPrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 7) : (execInstrBr t (checkerParentOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_parent_zero]
  | succ n ih => rw [checker_parent_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_parent_child_address (s : MachineState) :
    (checkerParentPrefix 2 s).getReg .x31=checkerParentChildAddress s := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 1 s).getReg .x31+(checkerParentPrefix 1 s).getReg .x4=_
  rw [checker_parent_prepare_register 1 s (by decide) .x4 (by decide),checker_parent_succ,checker_parent_zero]
  rfl
theorem checker_parent_child_address_loaded (s : MachineState) :
    (checkerParentPrefix 3 s).getReg .x31=checkerParentChildAddress s := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 2 s).getReg .x31=_
  exact checker_parent_child_address s
theorem checker_parent_address (s : MachineState) :
    (checkerParentPrefix 7 s).getReg .x31=checkerParentAddress s := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 6 s).getReg .x31+(checkerParentPrefix 6 s).getReg .x4=_
  rw [checker_parent_prepare_register 6 s (by decide) .x4 (by decide),checker_parent_succ]
  change ((checkerParentPrefix 5 s).getReg .x30 <<< 3)+s.getReg .x4=_
  rw [checker_parent_prepare_register 5 s (by decide) .x30 (by decide)]
  rfl
theorem checker_parent_left (s : MachineState) :
    (checkerParentPrefix 3 s).getReg .x2=s.getMem (checkerParentChildAddress s) := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 2 s).getMem ((checkerParentPrefix 2 s).getReg .x31+signExtend12 0)=_
  rw [show signExtend12 0=0#64 by rfl,BitVec.add_zero,checker_parent_child_address,
    checker_parent_prepare_memory 2 s (by decide)]
theorem checker_parent_right (s : MachineState) :
    (checkerParentPrefix 4 s).getReg .x3=s.getMem (checkerParentChildAddress s+8) := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 3 s).getMem ((checkerParentPrefix 3 s).getReg .x31+8)=_
  rw [checker_parent_child_address_loaded,checker_parent_prepare_memory 3 s (by decide)]
theorem checker_parent_value (s : MachineState) :
    (checkerParentPrefix 7 s).getReg .x2=checkerParentValue s := by
  rw [checker_parent_succ]
  change (checkerParentPrefix 6 s).getReg .x2=_
  rw [checker_parent_succ]
  change (checkerParentPrefix 5 s).getReg .x2=_
  rw [checker_parent_succ]
  change (checkerParentPrefix 4 s).getReg .x2 ||| (checkerParentPrefix 4 s).getReg .x3=_
  rw [checker_parent_right,checker_parent_succ]
  change (checkerParentPrefix 3 s).getReg .x2 ||| s.getMem (checkerParentChildAddress s+8)=_
  rw [checker_parent_left]
  rfl

private theorem merged_ChainedCheckerParentState_parent_guard_register (s : MachineState) (reg : Reg) :
    (execInstrBr s (.BNE .x30 .x0 8156)).getReg reg=s.getReg reg := by
  change (if _ then s.setPC _ else s.setPC _).getReg reg=_
  split <;> exact MachineState.getReg_setPC
private theorem merged_ChainedCheckerParentState_parent_guard_memory (s : MachineState) (query : Word) :
    (execInstrBr s (.BNE .x30 .x0 8156)).getMem query=s.getMem query := by
  change (if _ then s.setPC _ else s.setPC _).getMem query=_
  split <;> exact MachineState.getMem_setPC
theorem checker_parent_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3,.x30,.x31]) :
    (checkerParentPrefix 10 s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 10) : (execInstrBr t (checkerParentOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i
    all_goals first | exact merged_ChainedCheckerParentState_parent_guard_register t reg | (cases reg <;> simp at kept <;> rfl)
  have frame (n : Nat) (small : n≤10) : (checkerParentPrefix n s).getReg reg=s.getReg reg := by
    induction n with
    | zero => rw [checker_parent_zero]
    | succ n ih => rw [checker_parent_succ,step _ ⟨n,by omega⟩,ih (by omega)]
  exact frame 10 (by decide)
theorem checker_parent_counter (s : MachineState) :
    (checkerParentPrefix 10 s).getReg .x30=s.getReg .x30-1 := by
  rw [checker_parent_succ]
  change (execInstrBr (checkerParentPrefix 9 s) (.BNE .x30 .x0 8156)).getReg .x30=_
  rw [merged_ChainedCheckerParentState_parent_guard_register,checker_parent_succ]
  change (checkerParentPrefix 8 s).getReg .x30+signExtend12 4095=_
  rw [checker_parent_succ]
  change (checkerParentPrefix 7 s).getReg .x30+signExtend12 4095=_
  rw [checker_parent_prepare_register 7 s (by decide) .x30 (by decide),BitVec.sub_eq_add_neg]
  rfl
theorem checker_parent_memory (s : MachineState) (query : Word) :
    (checkerParentPrefix 10 s).getMem query=
      if query=checkerParentAddress s then checkerParentValue s else s.getMem query := by
  have store (t : MachineState) : (execInstrBr t (.SD .x31 .x2 0)).getMem query=
      if query=t.getReg .x31 then t.getReg .x2 else t.getMem query := by
    change (if query==t.getReg .x31+signExtend12 0 then _ else _)=_
    simp only [show signExtend12 0=0#64 by rfl,BitVec.add_zero,beq_iff_eq,MachineState.getMem]
  rw [checker_parent_succ]
  change (execInstrBr (checkerParentPrefix 9 s) (.BNE .x30 .x0 8156)).getMem query=_
  rw [merged_ChainedCheckerParentState_parent_guard_memory,checker_parent_succ]
  change (checkerParentPrefix 8 s).getMem query=_
  rw [checker_parent_succ]
  change (execInstrBr (checkerParentPrefix 7 s) (.SD .x31 .x2 0)).getMem query=_
  rw [store,checker_parent_address,checker_parent_value,checker_parent_prepare_memory 7 s (by decide)]

end CommitGolfCandidate.Chained.Native

end

section

/-! Physical accesses, installed execution and loop control of a mark parent. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_parent_child_address_eq (s : MachineState) (node : Nat)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 node) :
    checkerParentChildAddress s=BitVec.ofNat 64 (4096+16*node) := by
  rw [checkerParentChildAddress,counter,base,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 node*BitVec.ofNat 64 16+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega
theorem checker_parent_address_eq (s : MachineState) (node : Nat)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 node) :
    checkerParentAddress s=BitVec.ofNat 64 (4096+8*node) := by
  rw [checkerParentAddress,counter,base,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 node*BitVec.ofNat 64 8+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega
theorem checker_parent_value_eq (s : MachineState) (node : Nat)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 node) :
    checkerParentValue s=s.getMem (BitVec.ofNat 64 (4096+8*(2*node))) |||
      s.getMem (BitVec.ofNat 64 (4096+8*(2*node+1))) := by
  rw [checkerParentValue,checker_parent_child_address_eq s node base counter]
  change s.getMem (BitVec.ofNat 64 (4096+16*node)) |||
    s.getMem (BitVec.ofNat 64 (4096+16*node)+BitVec.ofNat 64 8)=_
  rw [←BitVec.ofNat_add]
  have left : 4096+16*node=4096+8*(2*node) := by omega
  have right : 4096+16*node+8=4096+8*(2*node+1) := by omega
  rw [right,left]
theorem checker_mark_access (node : Nat) (small : node<512) :
    accessValid (BitVec.ofNat 64 (4096+8*node)) 8=true := by
  have fit : 4096+8*node<2^64 := by omega
  have aligned : (4096+8*node)%8=0 := by omega
  simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,MEMORY_BYTES,aligned]
  omega
theorem checker_parent_prefix_pc (n : Nat) (s : MachineState) (small : n≤9) :
    (checkerParentPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 9) : (execInstrBr t (checkerParentOps.getD i.val .EBREAK)).pc=t.pc+4 := by fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_parent_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_parent_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1
theorem checker_parent_execution (s : MachineState) (node : Nat) (small : node<256)
    (pc : s.pc=4096+4*45) (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 node)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (10+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerParentPrefix 10 s) coins
          return result.charge 10 0) := by
  have left : accessValid ((checkerParentPrefix 2 s).getReg .x31) 8=true := by
    rw [checker_parent_child_address,checker_parent_child_address_eq s node base counter]
    convert checker_mark_access (2*node) (by omega) using 1 <;> congr 2 <;> omega
  have right : accessValid ((checkerParentPrefix 3 s).getReg .x31+8) 8=true := by
    rw [checker_parent_child_address_loaded,checker_parent_child_address_eq s node base counter]
    change accessValid (BitVec.ofNat 64 (4096+16*node)+BitVec.ofNat 64 8) 8=true
    rw [←BitVec.ofNat_add]
    convert checker_mark_access (2*node+1) (by omega) using 1 <;> congr 2 <;> omega
  have store : accessValid ((checkerParentPrefix 7 s).getReg .x31) 8=true := by
    rw [checker_parent_address,checker_parent_address_eq s node base counter]
    exact checker_mark_access node (by omega)
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_parent_zero s]
  apply execute_unit_steps (states := fun n => checkerParentPrefix n s)
  intro i inside
  refine ⟨.base (checkerParentOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_parent_at i inside
    rw [checker_parent_prefix_pc i s (by omega),pc]
  · rw [checker_parent_succ]
    interval_cases i
    · rfl
    · rfl
    · change (if accessValid ((checkerParentPrefix 2 s).getReg .x31+0) 8 then _ else _)=_
      exact ite_eq_left (by simpa using left)
    · change (if accessValid ((checkerParentPrefix 3 s).getReg .x31+8) 8 then _ else _)=_
      exact ite_eq_left right
    · rfl
    · rfl
    · rfl
    · change (if accessValid ((checkerParentPrefix 7 s).getReg .x31+0) 8 then _ else _)=_
      exact ite_eq_left (by simpa using store)
    · rfl
    · rfl
  · interval_cases i <;> rfl

theorem checker_parent_next_counter (s : MachineState) (count : Nat)
    (counter : s.getReg .x30=BitVec.ofNat 64 (count+1)) :
    (checkerParentPrefix 10 s).getReg .x30=BitVec.ofNat 64 count := by
  rw [checker_parent_counter,counter]
  change BitVec.ofNat 64 (count+1)-BitVec.ofNat 64 1=_
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),Nat.add_sub_cancel]
theorem checker_parent_next_pc (s : MachineState) (count : Nat) (small : count<256)
    (pc : s.pc=4096+4*45) (counter : s.getReg .x30=BitVec.ofNat 64 (count+1)) :
    (checkerParentPrefix 10 s).pc=if count=0 then 4096+4*55 else 4096+4*45 := by
  have prior : (checkerParentPrefix 9 s).getReg .x30=BitVec.ofNat 64 count := by
    have frame (t : MachineState) : (execInstrBr t (.BNE .x30 .x0 8156)).getReg .x30=t.getReg .x30 := by
      change (if _ then t.setPC _ else t.setPC _).getReg .x30=_
      split <;> exact MachineState.getReg_setPC
    have result := checker_parent_next_counter s count counter
    rw [checker_parent_succ] at result
    exact (frame _).symm.trans result
  rw [checker_parent_succ]
  change (execInstrBr (checkerParentPrefix 9 s) (.BNE .x30 .x0 8156)).pc=_
  by_cases last : count=0
  · have same : execInstrBr (checkerParentPrefix 9 s) (.BNE .x30 .x0 8156)=
        (checkerParentPrefix 9 s).setPC ((checkerParentPrefix 9 s).pc+4) := by
      apply ite_eq_right
      change ¬((checkerParentPrefix 9 s).getReg .x30 != 0#64)=true
      rw [prior,last]
      decide
    rw [same]
    change (checkerParentPrefix 9 s).pc+4=_
    rw [checker_parent_prefix_pc 9 s (by decide),pc,ite_eq_left last]
    rfl
  · have different : BitVec.ofNat 64 count≠0#64 := word_of_nat_ne count 0 (by omega) (by decide) last
    have same : execInstrBr (checkerParentPrefix 9 s) (.BNE .x30 .x0 8156)=
        (checkerParentPrefix 9 s).setPC ((checkerParentPrefix 9 s).pc+signExtend13 8156) := by
      apply ite_eq_left
      change ((checkerParentPrefix 9 s).getReg .x30 != 0#64)=true
      rw [prior]
      exact bne_iff_ne.mpr different
    rw [same]
    change (checkerParentPrefix 9 s).pc+signExtend13 8156=_
    rw [checker_parent_prefix_pc 9 s (by decide),pc,ite_eq_right last]
    rfl

theorem checker_parent_node_memory (s : MachineState) (parent node : Nat) (small : parent<256) (inside : node<512)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 parent) :
    (checkerParentPrefix 10 s).getMem (BitVec.ofNat 64 (4096+8*node))=
      if node=parent then s.getMem (BitVec.ofNat 64 (4096+8*(2*parent))) |||
        s.getMem (BitVec.ofNat 64 (4096+8*(2*parent+1))) else s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  rw [checker_parent_memory,checker_parent_address_eq s parent base counter,checker_parent_value_eq s parent base counter]
  by_cases same : node=parent
  · simp [same]
  · have different : BitVec.ofNat 64 (4096+8*node)≠BitVec.ofNat 64 (4096+8*parent) :=
      word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    rw [ite_eq_right different,ite_eq_right same]

end CommitGolfCandidate.Chained.Native

end

section

/-! Complete descending mark sweep, with canonical occupancy and ABI frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerParentRows : Nat → MachineState → MachineState
  | 0,s => s
  | count+1,s => checkerParentRows count (checkerParentPrefix 10 s)
theorem checker_parent_rows_zero (s : MachineState) : checkerParentRows 0 s=s := by rw [checkerParentRows]
theorem checker_parent_rows_succ (count : Nat) (s : MachineState) :
    checkerParentRows (count+1) s=checkerParentRows count (checkerParentPrefix 10 s) := by rw [checkerParentRows]
theorem checker_parent_rows_register (count : Nat) (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3,.x30,.x31]) :
    (checkerParentRows count s).getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero => rw [checker_parent_rows_zero]
  | succ count ih => rw [checker_parent_rows_succ,ih,checker_parent_register s reg kept]
theorem checker_parent_rows_execution (count : Nat) (s : MachineState) (small : count<256)
    (pc : s.pc=if count=0 then 4096+4*55 else 4096+4*45)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 count) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (10*count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerParentRows count s) coins
          return result.charge (10*count) 0) := by
  induction count generalizing s with
  | zero => simp [checker_parent_rows_zero,Execution.charge]
  | succ count ih =>
    have headPC : s.pc=4096+4*45 := by simpa using pc
    have nextBase : (checkerParentPrefix 10 s).getReg .x4=4096#64 :=
      (checker_parent_register s .x4 (by decide)).trans base
    rw [show 10*(count+1)+fuel=10+(10*count+fuel) by omega,
      checker_parent_execution s (count+1) small headPC base counter,
      ih _ (by omega) (checker_parent_next_pc s count (by omega) headPC counter) nextBase
        (checker_parent_next_counter s count counter),←checker_parent_rows_succ]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem checker_parent_rows_control (count : Nat) (s : MachineState) (small : count<256)
    (pc : s.pc=if count=0 then 4096+4*55 else 4096+4*45)
    (counter : s.getReg .x30=BitVec.ofNat 64 count) :
    (checkerParentRows count s).pc=4096+4*55 ∧ (checkerParentRows count s).getReg .x30=0#64 := by
  induction count generalizing s with
  | zero => rw [checker_parent_rows_zero]; exact ⟨by simpa using pc,counter⟩
  | succ count ih =>
    have headPC : s.pc=4096+4*45 := by simpa using pc
    rw [checker_parent_rows_succ]
    exact ih _ (by omega) (checker_parent_next_pc s count (by omega) headPC counter)
      (checker_parent_next_counter s count counter)
theorem checker_parent_rows_memory_frame (count : Nat) (s : MachineState) (small : count<256)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 count) (query : Word)
    (away : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerParentRows count s).getMem query=s.getMem query := by
  induction count generalizing s with
  | zero => rw [checker_parent_rows_zero]
  | succ count ih =>
    have nextBase := (checker_parent_register s .x4 (by decide)).trans base
    rw [checker_parent_rows_succ,ih _ (by omega) nextBase (checker_parent_next_counter s count counter),
      checker_parent_memory,checker_parent_address_eq s (count+1) base counter]
    exact ite_eq_right (away _ (by omega))
theorem checker_parent_rows_node_zero (count : Nat) (s : MachineState) (small : count<256)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 count) :
    (checkerParentRows count s).getMem (BitVec.ofNat 64 4096)=s.getMem (BitVec.ofNat 64 4096) := by
  induction count generalizing s with
  | zero => rw [checker_parent_rows_zero]
  | succ count ih =>
    have nextBase := (checker_parent_register s .x4 (by decide)).trans base
    rw [checker_parent_rows_succ,ih _ (by omega) nextBase (checker_parent_next_counter s count counter)]
    have point := checker_parent_node_memory s (count+1) 0 small (by decide) base counter
    simpa using point
theorem checker_parent_rows_saved_abi (original s : MachineState) (count : Nat) (small : count<256)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 count)
    (saved : CheckerSavedABI original s) : CheckerSavedABI original (checkerParentRows count s) := by
  apply checker_saved_abi_frame original s _ saved
  intro slot
  apply checker_parent_rows_memory_frame count s small base counter
  intro node inside
  have range := checker_saved_byte_range slot 0 (by decide)
  have low : 8192<checkingMetadataBase := by decide +kernel
  apply word_of_nat_ne _ _ (by omega) (by omega)
  omega

theorem checker_parent_rows_canonical (groups : List Nat) (count : Nat) (s : MachineState) (small : count<256)
    (base : s.getReg .x4=4096#64) (counter : s.getReg .x30=BitVec.ofNat 64 count)
    (finished : ∀ node, count<node → node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node) :
    ∀ node, 0<node → node<512 →
      (checkerParentRows count s).getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node := by
  induction count generalizing s with
  | zero => rw [checker_parent_rows_zero]; exact finished
  | succ count ih =>
    rw [checker_parent_rows_succ]
    apply ih _ (by omega) ((checker_parent_register s .x4 (by decide)).trans base)
      (checker_parent_next_counter s count counter)
    intro node greater inside
    rw [checker_parent_node_memory s (count+1) node small inside base counter]
    by_cases same : node=count+1
    · subst node
      rw [ite_eq_left rfl,finished _ (by omega) (by omega),finished _ (by omega) (by omega)]
      exact (mark_word_parent groups ⟨count+1,small⟩ (show 0<count+1 by omega)).symm
    · rw [ite_eq_right same]
      exact finished _ (by omega) inside

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual parent-counter initialization and final source/output pointer copies. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

inductive CheckerMarkBoundary where | parents | records
def CheckerMarkBoundary.index : CheckerMarkBoundary → Nat | .parents => 44 | .records => 55
abbrev CheckerMarkBoundary.count : CheckerMarkBoundary → Nat | .parents => 1 | .records => 2
abbrev CheckerMarkBoundary.ops : CheckerMarkBoundary → List Instr
  | .parents => [.ADDI .x30 .x0 255]
  | .records => [.ADDI .x18 .x15 0,.ADDI .x6 .x12 0]
@[irreducible] def checkerMarkBoundaryPrefix (b : CheckerMarkBoundary) (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (b.ops.getD index .EBREAK)) n
theorem checker_mark_boundary_zero (b : CheckerMarkBoundary) (s : MachineState) : checkerMarkBoundaryPrefix b 0 s=s := by
  rw [checkerMarkBoundaryPrefix]; rfl
theorem checker_mark_boundary_succ (b : CheckerMarkBoundary) (n : Nat) (s : MachineState) :
    checkerMarkBoundaryPrefix b (n+1) s=execInstrBr (checkerMarkBoundaryPrefix b n s) (b.ops.getD n .EBREAK) := by
  unfold checkerMarkBoundaryPrefix; rfl
theorem checker_mark_boundary_at (b : CheckerMarkBoundary) : OpsAt chainedCheckerImage (4096+4*b.index) b.ops := by
  cases b
  · exact chained_checker_slice_at 44 1 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 55 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_mark_boundary_memory (b : CheckerMarkBoundary) (s : MachineState) (query : Word) :
    (checkerMarkBoundaryPrefix b b.count s).getMem query=s.getMem query := by
  cases b <;> rw [checkerMarkBoundaryPrefix] <;> rfl
theorem checker_mark_boundary_register (b : CheckerMarkBoundary) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x6,.x18,.x30]) : (checkerMarkBoundaryPrefix b b.count s).getReg reg=s.getReg reg := by
  cases b <;> rw [checkerMarkBoundaryPrefix]
  all_goals cases reg <;> simp at kept <;> rfl
theorem checker_mark_boundary_count (s : MachineState) :
    (checkerMarkBoundaryPrefix .parents 1 s).getReg .x30=255#64 := by rw [checkerMarkBoundaryPrefix]; rfl
theorem checker_mark_boundary_source (s : MachineState) :
    (checkerMarkBoundaryPrefix .records 2 s).getReg .x18=s.getReg .x15 := by
  rw [checkerMarkBoundaryPrefix]
  change s.getReg .x15+0#64=_
  exact BitVec.add_zero _
theorem checker_mark_boundary_output (s : MachineState) :
    (checkerMarkBoundaryPrefix .records 2 s).getReg .x6=s.getReg .x12 := by
  rw [checkerMarkBoundaryPrefix]
  change s.getReg .x12+0#64=_
  exact BitVec.add_zero _
theorem checker_mark_boundary_pc (b : CheckerMarkBoundary) (n : Nat) (s : MachineState) (small : n≤b.count) :
    (checkerMarkBoundaryPrefix b n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin b.count) : (execInstrBr t (b.ops.getD i.val .EBREAK)).pc=t.pc+4 := by
    cases b <;> fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_mark_boundary_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_mark_boundary_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1
theorem checker_mark_boundary_execution (b : CheckerMarkBoundary) (s : MachineState)
    (pc : s.pc=4096+4*BitVec.ofNat 64 b.index) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (b.count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerMarkBoundaryPrefix b b.count s) coins
          return result.charge b.count 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_mark_boundary_zero b s]
  apply execute_unit_steps (states := fun n => checkerMarkBoundaryPrefix b n s)
  intro i inside
  refine ⟨.base (b.ops.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_mark_boundary_at b i (by cases b <;> exact inside)
    rw [checker_mark_boundary_pc b i s (by omega),pc]
    cases b <;> rfl
  · rw [checker_mark_boundary_succ]
    cases b <;> simp only [CheckerMarkBoundary.count] at inside <;> interval_cases i <;> rfl
  · cases b <;> simp only [CheckerMarkBoundary.count] at inside <;> interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native

end

section

/-! Canonical mark sweep instantiated with the exact delivered public input. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_seeded_input_base (input : CheckInput) : (checkerSeededInputState input).getReg .x4=4096#64 := by
  rw [checker_seeded_input_eq,checker_seed_stream_register _ _ .x4 (by decide),checker_seed_input_start_eq,
    checker_seed_init_register _ .x4 (by decide),checker_marks_cleared_base]
theorem checker_seeded_input_metadata (input : CheckInput) :
    (checkerSeededInputState input).getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
  rw [checker_seeded_input_eq,checker_seed_stream_register _ _ .x8 (by decide),checker_seed_input_start_eq,
    checker_seed_init_register _ .x8 (by decide),checker_marks_cleared_metadata]
theorem checker_seeded_input_raw (input : CheckInput) :
    (checkerSeededInputState input).getReg .x12=BitVec.ofNat 64 checkingRawBase := by
  rw [checker_seeded_input_eq,checker_seed_stream_register _ _ .x12 (by decide),checker_seed_input_start_eq,
    checker_seed_init_register _ .x12 (by decide),checker_marks_cleared_eq,
    checker_clear_rows_register 512 _ .x12 (by decide),checker_marks_init_register _ .x12 (by decide),
    checker_saved_state_register _ .x12 (by decide),checker_admission_raw_pointer,
    (checker_input_registers input).2.2.2.2.1]
  rfl
theorem checker_seeded_input_register (input : CheckInput) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x4,.x8,.x10,.x12,.x30,.x31]) :
    (checkerSeededInputState input).getReg reg=(Artifact.submission.initialState .check input).getReg reg := by
  have seedKept : reg∉[.x2,.x3,.x30,.x31] := by cases reg <;> simp at kept ⊢
  have initKept : reg∉[.x2,.x3,.x10] := by cases reg <;> simp at kept ⊢
  have clearKept : reg∉[.x2,.x3,.x4,.x8,.x12,.x30] := by cases reg <;> simp at kept ⊢
  rw [checker_seeded_input_eq,checker_seed_stream_register _ _ reg seedKept,checker_seed_input_start_eq,
    checker_seed_init_register _ reg initKept,checker_marks_cleared_register _ reg clearKept]
theorem checker_seeded_input_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerSeededInputState input).pc=4096+4*44 := by
  have present : input.positions.sort (· ≤ ·)≠[] := by
    intro empty
    have length := congrArg List.length empty
    rw [Finset.length_sort] at length
    exact nonempty length
  have pc : (checkerSeedInputStart input).pc=if input.positions.sort (· ≤ ·)=[] then 4096+4*44 else 4096+4*35 := by
    rw [ite_eq_right present]
    exact checker_seed_input_start_pc input nonempty lower upper
  rw [checker_seeded_input_eq]
  exact (checker_seed_stream_control _ _ 5905584160 (checker_seed_input_ready input) pc).1
theorem checker_seeded_input_memory_frame (input : CheckInput) (query : Word)
    (savedAway : ∀ slot : Fin 4, query≠BitVec.ofNat 64 (checkerSavedAddress slot))
    (markAway : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerSeededInputState input).getMem query=(Artifact.submission.initialState .check input).getMem query := by
  rw [checker_seeded_input_eq,checker_seed_stream_memory_frame _ _ 5905584160 (checker_seed_input_ready input) query markAway,
    checker_seed_input_start_eq,checker_seed_init_memory,checker_marks_cleared_memory_frame _ query savedAway markAway]

@[irreducible] def checkerParentInputStart (input : CheckInput) : MachineState :=
  checkerMarkBoundaryPrefix .parents 1 (checkerSeededInputState input)
theorem checker_parent_input_start_eq (input : CheckInput) : checkerParentInputStart input=
    checkerMarkBoundaryPrefix .parents 1 (checkerSeededInputState input) := by rw [checkerParentInputStart]
theorem checker_parent_input_start_base (input : CheckInput) : (checkerParentInputStart input).getReg .x4=4096#64 := by
  rw [checker_parent_input_start_eq,checker_mark_boundary_register .parents _ .x4 (by decide),checker_seeded_input_base]
theorem checker_parent_input_start_count (input : CheckInput) : (checkerParentInputStart input).getReg .x30=255#64 := by
  rw [checker_parent_input_start_eq,checker_mark_boundary_count]
theorem checker_parent_input_start_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerParentInputStart input).pc=4096+4*45 := by
  rw [checker_parent_input_start_eq,checker_mark_boundary_pc .parents 1 _ (by decide),
    checker_seeded_input_pc input nonempty lower upper]
  rfl
theorem checker_parent_input_start_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2075+9*input.positions.card+fuel)
        (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerParentInputStart input) coins
          return result.charge (2075+9*input.positions.card) 0) := by
  rw [checker_parent_input_start_eq,show 2075+9*input.positions.card+fuel=(2074+9*input.positions.card)+(1+fuel) by omega,
    checker_seeded_input_execution input nonempty lower upper,
    checker_mark_boundary_execution .parents _ (checker_seeded_input_pc input nonempty lower upper)]
  simp [CheckerMarkBoundary.count,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  simp only [show 1+(9*input.positions.card+2074)=9*input.positions.card+2075 by omega]

@[irreducible] def checkerMarksReadyInputState (input : CheckInput) : MachineState := checkerParentRows 255 (checkerParentInputStart input)
theorem checker_marks_ready_input_eq (input : CheckInput) : checkerMarksReadyInputState input=
    checkerParentRows 255 (checkerParentInputStart input) := by rw [checkerMarksReadyInputState]
theorem checker_marks_ready_input_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerMarksReadyInputState input).pc=4096+4*55 := by
  rw [checker_marks_ready_input_eq]
  exact (checker_parent_rows_control 255 _ (by decide)
    (by simpa using checker_parent_input_start_pc input nonempty lower upper) (checker_parent_input_start_count input)).1

theorem checker_input_mark_zero (input : CheckInput) : markWord ((input.positions.sort (· ≤ ·)).map capGroup) 0=0#64 := by
  have absent : capIsMarked ((input.positions.sort (· ≤ ·)).map capGroup) 0 8=false := by
    rw [capIsMarked,List.any_eq_false]
    intro group member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    have bounds := checker_seed_group_bounds index
    change ¬ (capGroup index/256 == 0)=true
    rw [beq_iff_eq]
    omega
  rw [markWord,show TwoPermutationPrototype.Opening.capHeight 0=8 by decide +kernel,absent]
  rfl
theorem checker_marks_ready_input_marks (input : CheckInput) (node : Nat) (inside : node<512) :
    (checkerMarksReadyInputState input).getMem (BitVec.ofNat 64 (4096+8*node))=
      markWord ((input.positions.sort (· ≤ ·)).map capGroup) node := by
  rw [checker_marks_ready_input_eq]
  by_cases zero : node=0
  · subst node
    rw [checker_parent_rows_node_zero 255 _ (by decide) (checker_parent_input_start_base input) (checker_parent_input_start_count input),
      checker_parent_input_start_eq,checker_mark_boundary_memory .parents,checker_seeded_input_marks input 0 (by decide),
      checker_input_mark_zero]
    apply ite_eq_right
    intro member
    obtain ⟨index,_,equal⟩ := List.mem_map.mp member
    have bounds := checker_seed_group_bounds index
    omega
  · apply checker_parent_rows_canonical _ 255 _ (by decide) (checker_parent_input_start_base input)
      (checker_parent_input_start_count input) _ node (by omega) inside
    intro leaf greater bounded
    rw [checker_parent_input_start_eq,checker_mark_boundary_memory .parents,checker_seeded_input_marks input leaf bounded]
    exact (mark_word_leaf _ ⟨leaf,bounded⟩ (show 256≤leaf by omega)).symm
theorem checker_marks_ready_input_saved_abi (input : CheckInput) :
    CheckerSavedABI (Artifact.submission.initialState .check input) (checkerMarksReadyInputState input) := by
  rw [checker_marks_ready_input_eq]
  apply checker_parent_rows_saved_abi _ _ 255 (by decide) (checker_parent_input_start_base input) (checker_parent_input_start_count input)
  rw [checker_parent_input_start_eq]
  exact checker_saved_abi_frame _ _ _ (checker_seeded_input_saved_abi input)
    (fun _ => checker_mark_boundary_memory .parents _ _)

end CommitGolfCandidate.Chained.Native

end

section

/-! Complete delivered nonempty entry, with canonical marks and original ABI. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_marks_ready_input_register (input : CheckInput) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x6,.x18,.x30,.x31]) :
    (checkerMarksReadyInputState input).getReg reg=(checkerSeededInputState input).getReg reg := by
  have parents : reg∉[.x2,.x3,.x30,.x31] := by cases reg <;> simp at kept ⊢
  have boundary : reg∉[.x6,.x18,.x30] := by cases reg <;> simp at kept ⊢
  rw [checker_marks_ready_input_eq,checker_parent_rows_register 255 _ reg parents,
    checker_parent_input_start_eq,checker_mark_boundary_register .parents _ reg boundary]

@[irreducible] def checkerRecordInputState (input : CheckInput) : MachineState :=
  checkerMarkBoundaryPrefix .records 2 (checkerMarksReadyInputState input)
theorem checker_record_input_eq (input : CheckInput) : checkerRecordInputState input=
    checkerMarkBoundaryPrefix .records 2 (checkerMarksReadyInputState input) := by rw [checkerRecordInputState]
theorem checker_record_input_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerRecordInputState input).pc=4096+4*57 := by
  rw [checker_record_input_eq,checker_mark_boundary_pc .records 2 _ (by decide),
    checker_marks_ready_input_pc input nonempty lower upper]
  rfl
theorem checker_record_input_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4627+9*input.positions.card+fuel)
        (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordInputState input) coins
          return result.charge (4627+9*input.positions.card) 0) := by
  have parentPC : (checkerParentInputStart input).pc=if 255=0 then 4096+4*55 else 4096+4*45 := by
    simpa using checker_parent_input_start_pc input nonempty lower upper
  have endPC : (checkerParentRows 255 (checkerParentInputStart input)).pc=4096+4*55 := by
    rw [←checker_marks_ready_input_eq]
    exact checker_marks_ready_input_pc input nonempty lower upper
  rw [checker_record_input_eq,checker_marks_ready_input_eq,
    show 4627+9*input.positions.card+fuel=(2075+9*input.positions.card)+(10*255+(2+fuel)) by omega,
    checker_parent_input_start_execution input nonempty lower upper,
    checker_parent_rows_execution 255 _ (by decide) parentPC (checker_parent_input_start_base input)
      (checker_parent_input_start_count input),checker_mark_boundary_execution .records _ endPC]
  simp [CheckerMarkBoundary.count,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem checker_record_input_marks (input : CheckInput) (node : Nat) (inside : node<512) :
    (checkerRecordInputState input).getMem (BitVec.ofNat 64 (4096+8*node))=
      markWord ((input.positions.sort (· ≤ ·)).map capGroup) node := by
  rw [checker_record_input_eq,checker_mark_boundary_memory .records,checker_marks_ready_input_marks input node inside]
theorem checker_record_input_saved_abi (input : CheckInput) :
    CheckerSavedABI (Artifact.submission.initialState .check input) (checkerRecordInputState input) := by
  rw [checker_record_input_eq]
  exact checker_saved_abi_frame _ _ _ (checker_marks_ready_input_saved_abi input)
    (fun _ => checker_mark_boundary_memory .records _ _)
theorem checker_record_input_memory_frame (input : CheckInput) (query : Word)
    (savedAway : ∀ slot : Fin 4, query≠BitVec.ofNat 64 (checkerSavedAddress slot))
    (markAway : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerRecordInputState input).getMem query=(Artifact.submission.initialState .check input).getMem query := by
  rw [checker_record_input_eq,checker_mark_boundary_memory .records,checker_marks_ready_input_eq,
    checker_parent_rows_memory_frame 255 _ (by decide) (checker_parent_input_start_base input)
      (checker_parent_input_start_count input) query markAway,
    checker_parent_input_start_eq,checker_mark_boundary_memory .parents,
    checker_seeded_input_memory_frame input query savedAway markAway]
theorem checker_record_input_register (input : CheckInput) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x4,.x6,.x8,.x10,.x12,.x18,.x30,.x31]) :
    (checkerRecordInputState input).getReg reg=(Artifact.submission.initialState .check input).getReg reg := by
  have boundary : reg∉[.x6,.x18,.x30] := by cases reg <;> simp at kept ⊢
  have parents : reg∉[.x2,.x3,.x6,.x18,.x30,.x31] := by cases reg <;> simp at kept ⊢
  have seedKept : reg∉[.x2,.x3,.x4,.x8,.x10,.x12,.x30,.x31] := by cases reg <;> simp at kept ⊢
  rw [checker_record_input_eq,checker_mark_boundary_register .records _ reg boundary,
    checker_marks_ready_input_register input reg parents,checker_seeded_input_register input reg seedKept]
theorem checker_record_input_base (input : CheckInput) : (checkerRecordInputState input).getReg .x4=4096#64 := by
  rw [checker_record_input_eq,checker_mark_boundary_register .records _ .x4 (by decide),
    checker_marks_ready_input_register input .x4 (by decide),checker_seeded_input_base]
theorem checker_record_input_metadata (input : CheckInput) :
    (checkerRecordInputState input).getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
  rw [checker_record_input_eq,checker_mark_boundary_register .records _ .x8 (by decide),
    checker_marks_ready_input_register input .x8 (by decide),checker_seeded_input_metadata]
theorem checker_record_input_source (input : CheckInput) :
    (checkerRecordInputState input).getReg .x18=BitVec.ofNat 64 Artifact.submission.layout.proof := by
  rw [checker_record_input_eq,checker_mark_boundary_source,checker_marks_ready_input_register input .x15 (by decide),
    checker_seeded_input_register input .x15 (by decide),(checker_input_registers input).2.2.2.2.1]
  rfl
theorem checker_record_input_output (input : CheckInput) :
    (checkerRecordInputState input).getReg .x6=BitVec.ofNat 64 checkingRawBase := by
  rw [checker_record_input_eq,checker_mark_boundary_output,checker_marks_ready_input_register input .x12 (by decide),checker_seeded_input_raw]
theorem checker_record_input_count (input : CheckInput) :
    (checkerRecordInputState input).getReg .x16=BitVec.ofNat 64 input.positions.card := by
  rw [checker_record_input_register input .x16 (by decide),(checker_input_registers input).2.2.2.2.2.1]

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual host-loaded supplied proof bytes survive the complete mark setup. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem checker_input_proof_size (input : CheckInput) (upper : input.proof.length≤482*input.positions.card+3776) :
    input.proof.length≤Artifact.submission.sizes.proof := by
  have card : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card≤16777216 := card
  change input.proof.length≤8355061248
  omega
theorem checker_input_proof_byte (input : CheckInput) (valid : input.proof.length≤Artifact.submission.sizes.proof)
    (offset : Nat) (inside : offset < input.proof.length) :
    (Artifact.submission.initialState .check input).getByte
      (BitVec.ofNat 64 (Artifact.submission.layout.proof+offset))=input.proof[offset] := by
  have card : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card≤16777216 := card
  rw [initial_input_byte Artifact.submission .check input _ (by
    change 10334769248+offset<2^64
    change input.proof.length≤8355061248 at valid
    omega)]
  have outsideRoot : ¬ (Artifact.submission.layout.commitment≤Artifact.submission.layout.proof+offset ∧
      Artifact.submission.layout.proof+offset<Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392≤10334769248+offset ∧ 10334769248+offset<4294971424)
    omega
  have outsideIndices : ¬ (Artifact.submission.layout.indices≤Artifact.submission.layout.proof+offset ∧
      Artifact.submission.layout.proof+offset<Artifact.submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160≤10334769248+offset ∧ 10334769248+offset<5905584160+8*input.positions.card)
    omega
  have outsideValues : ¬ (Artifact.submission.layout.values≤Artifact.submission.layout.proof+offset ∧
      Artifact.submission.layout.proof+offset<Artifact.submission.layout.values+(LEAF_SIZE/8)*input.positions.card) := by
    change ¬ (6039801952≤10334769248+offset ∧ 10334769248+offset<6039801952+256*input.positions.card)
    omega
  have selected : Artifact.submission.layout.proof≤Artifact.submission.layout.proof+offset ∧
      Artifact.submission.layout.proof+offset<Artifact.submission.layout.proof+input.proof.length := by omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,valuesBuffer,
    Finset.length_sort,Finset.card_attach,outsideRoot,outsideIndices,outsideValues,decide_false,selected,
    and_self,decide_true,Nat.add_sub_cancel_left,List.getElem?_eq_getElem inside,Option.getD_some]

theorem checker_record_input_byte_frame (input : CheckInput) (address : Nat)
    (lower : 8192≤address) (upper : address<checkingMetadataBase) :
    (checkerRecordInputState input).getByte (BitVec.ofNat 64 address)=
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 address) := by
  have alignedFrame : (checkerRecordInputState input).getMem (BitVec.ofNat 64 (8*(address/8)))=
      (Artifact.submission.initialState .check input).getMem (BitVec.ofNat 64 (8*(address/8))) := by
    apply checker_record_input_memory_frame
    · intro slot
      have range := checker_saved_byte_range slot 0 (by decide)
      have metaFit := checking_metadata_room
      apply word_of_nat_ne _ _ (by omega) (by omega)
      omega
    · intro node inside
      have metaFit := checking_metadata_room
      apply word_of_nat_ne _ _ (by omega) (by omega)
      omega
  have small : address%8<8 := Nat.mod_lt _ (by decide)
  have joined : 8*(address/8)+address%8=address := by omega
  have after := aligned_byte (checkerRecordInputState input) (address/8) (address%8) (by omega)
  have before := aligned_byte (Artifact.submission.initialState .check input) (address/8) (address%8) (by omega)
  simp only [joined,Nat.div_eq_of_lt small,Nat.mul_zero,Nat.add_zero,Nat.mod_mod] at after before
  rw [after,before,alignedFrame]
theorem checker_record_input_proof (input : CheckInput) (upper : input.proof.length≤482*input.positions.card+3776) :
    BytesAt (checkerRecordInputState input) (BitVec.ofNat 64 Artifact.submission.layout.proof) input.proof := by
  intro offset inside
  rw [←BitVec.ofNat_add]
  have sourceRange := checking_source_before_raw input.positions.card input.proof.length
    (by simpa [Index] using Finset.card_le_univ input.positions) upper
  have rawBefore : checkingRawBase<checkingMetadataBase := by decide +kernel
  rw [checker_record_input_byte_frame input _ (by change 8192≤10334769248+offset; omega) (by omega)]
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some] using
    checker_input_proof_byte input (checker_input_proof_size input upper) offset inside

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual loaded, untrusted record bytes execute through the complete record loop. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_record_input_untrusted_ready (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerRecordStreamReady (checkerDecodeRecords input.positions.card input.proof) (input.proof.drop (482*input.positions.card))
      (checkerRecordInputState input) Artifact.submission.layout.proof checkingRawBase := by
  have card : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  apply checker_record_untrusted_ready input.positions.card input.proof _ _ _ lower card
  · rw [ite_eq_right nonempty]; exact checker_record_input_pc input nonempty lower upper
  · exact checker_record_input_source input
  · exact checker_record_input_output input
  · exact checker_record_input_metadata input
  · exact checker_record_input_count input
  · exact checker_record_input_proof input upper
  · exact checking_source_before_raw _ _ card upper
  · exact Nat.le_refl _
  · exact checking_raw_before_metadata _ card

@[irreducible] def checkerDecodedRecordsInputState (input : CheckInput) : MachineState :=
  checkerRecordLoopState (checkerDecodeRecords input.positions.card input.proof) (checkerRecordInputState input)
theorem checker_decoded_records_input_eq (input : CheckInput) : checkerDecodedRecordsInputState input=
    checkerRecordLoopState (checkerDecodeRecords input.positions.card input.proof) (checkerRecordInputState input) := by
  rw [checkerDecodedRecordsInputState]
@[irreducible] def checkerDecodedRecordsInputCycles (input : CheckInput) : Nat :=
  4627+9*input.positions.card+checkerRecordLoopCycles (checkerDecodeRecords input.positions.card input.proof) (checkerRecordInputState input)
theorem checker_decoded_records_input_cycles_eq (input : CheckInput) : checkerDecodedRecordsInputCycles input=
    4627+9*input.positions.card+checkerRecordLoopCycles (checkerDecodeRecords input.positions.card input.proof) (checkerRecordInputState input) := by
  rw [checkerDecodedRecordsInputCycles]
theorem checker_decoded_records_input_bound (input : CheckInput) :
    checkerDecodedRecordsInputCycles input≤4627+2387*input.positions.card := by
  have loop := checker_record_loop_bound (checkerDecodeRecords input.positions.card input.proof) (checkerRecordInputState input)
  rw [checker_decode_records_length] at loop
  rw [checker_decoded_records_input_cycles_eq]
  omega
theorem checker_decoded_records_input_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerDecodedRecordsInputCycles input+fuel)
        (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerDecodedRecordsInputState input) coins
          return result.charge (checkerDecodedRecordsInputCycles input) 0) := by
  rw [checker_decoded_records_input_cycles_eq,checker_decoded_records_input_eq,Nat.add_assoc,
    checker_record_input_execution input nonempty lower upper,
    checker_record_loop_execution _ _ _ Artifact.submission.layout.proof checkingRawBase
      (checker_record_input_untrusted_ready input nonempty lower upper)]
  simp [Execution.charge,Nat.add_assoc]
theorem checker_decoded_records_input_ready (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerRecordStreamReady [] (input.proof.drop (482*input.positions.card)) (checkerDecodedRecordsInputState input)
      (Artifact.submission.layout.proof+482*input.positions.card) (checkingRawBase+498*input.positions.card) := by
  rw [checker_decoded_records_input_eq]
  simpa only [checker_decode_records_length] using checker_record_loop_ready _ _ _ _ _
    (checker_record_input_untrusted_ready input nonempty lower upper)
theorem checker_decoded_records_input_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerDecodedRecordsInputState input).pc=4096+4*2164 := by
  simpa using (checker_decoded_records_input_ready input nonempty lower upper).pc
theorem checker_decoded_records_input_memory (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    BytesAt (checkerDecodedRecordsInputState input) (BitVec.ofNat 64 checkingRawBase)
      (rawRecordStream (checkerDecodeRecords input.positions.card input.proof)) := by
  rw [checker_decoded_records_input_eq]
  exact checker_record_loop_memory _ _ _ _ _ (checker_record_input_untrusted_ready input nonempty lower upper)
theorem checker_decoded_records_input_saved_abi (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerSavedABI (Artifact.submission.initialState .check input) (checkerDecodedRecordsInputState input) := by
  rw [checker_decoded_records_input_eq]
  exact checker_record_loop_saved_abi _ _ _ _ _ _ (checker_record_input_untrusted_ready input nonempty lower upper)
    (checker_record_input_saved_abi input)

end CommitGolfCandidate.Chained.Native

end

section

/-! Canonical marks and physical footer-width readiness after actual record decoding. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_decoded_records_input_marks (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (node : Nat) (inside : node<512) :
    (checkerDecodedRecordsInputState input).getMem (BitVec.ofNat 64 (4096+8*node))=
      markWord ((input.positions.sort (· ≤ ·)).map capGroup) node := by
  have ready := checker_record_input_untrusted_ready input nonempty lower upper
  have room := ready.outputRoom
  have metaFit := checking_metadata_room
  have low : 8192<checkingRawBase ∧ 8192<checkingMetadataBase := by decide +kernel
  have frame : (checkerDecodedRecordsInputState input).getMem (BitVec.ofNat 64 (4096+8*node))=
      (checkerRecordInputState input).getMem (BitVec.ofNat 64 (4096+8*node)) := by
    apply aligned_word_of_byte_frame _ _ _ (by omega)
    intro offset small
    rw [checker_decoded_records_input_eq]
    apply checker_record_loop_byte_frame _ _ _ Artifact.submission.layout.proof checkingRawBase _ ready
    · intro written before
      rw [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · intro written before
      rw [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  rw [frame,checker_record_input_marks input node inside]

@[irreducible] def checkerFooterInputStart (input : CheckInput) : MachineState :=
  checkerFooterInitPrefix (checkerDecodedRecordsInputState input) 4
theorem checker_footer_input_start_eq (input : CheckInput) : checkerFooterInputStart input=
    checkerFooterInitPrefix (checkerDecodedRecordsInputState input) 4 := by rw [checkerFooterInputStart]
theorem checker_footer_input_start_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (checkerFooterInputStart input).pc=4096+4*2168 := by
  rw [checker_footer_input_start_eq,checker_footer_init_pc _ 4 (by decide),
    checker_decoded_records_input_pc input nonempty lower upper]
  rfl
theorem checker_footer_input_start_ready (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerFooterWidthsReady ((input.positions.sort (· ≤ ·)).map capGroup) []
      (checkerFooterInputStart input) (checkerFooterInputStart input) 1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,by decide,?_,?_,?_⟩
  · rw [checker_footer_input_start_eq,checker_footer_init_register _ .x4 (by decide),
      checker_decoded_records_input_eq,checker_record_loop_register _ _ .x4 (by decide),checker_record_input_base]
    rfl
  · rw [checker_footer_input_start_eq,checker_footer_init_limit]
  · intro node inside
    rw [checker_footer_input_start_eq,checker_footer_init_memory]
    exact checker_decoded_records_input_marks input nonempty lower upper node inside
  · rw [checker_footer_input_start_eq,checker_footer_init_node]
    rfl
  · rw [checker_footer_input_start_eq,checker_footer_init_metadata]
    exact (checker_decoded_records_input_ready input nonempty lower upper).metadata
  · rw [checker_footer_input_start_eq,checker_footer_init_count]
    rfl
  · intro index inside; simp at inside
  · intro _ _ _; rfl
  · intro _ _; rfl
theorem checker_footer_input_start_saved_abi (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    CheckerSavedABI (Artifact.submission.initialState .check input) (checkerFooterInputStart input) := by
  rw [checker_footer_input_start_eq]
  exact checker_footer_init_saved_abi _ _ (checker_decoded_records_input_saved_abi input nonempty lower upper)
theorem checker_footer_input_start_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerDecodedRecordsInputCycles input+4+fuel)
        (Artifact.submission.initialState .check input) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterInputStart input) coins
          return result.charge (checkerDecodedRecordsInputCycles input+4) 0) := by
  rw [checker_footer_input_start_eq,Nat.add_assoc,checker_decoded_records_input_execution input nonempty lower upper,
    checker_footer_init_execution _ (checker_decoded_records_input_pc input nonempty lower upper)]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_footer_widths_from_input (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    ∃ after cycles, RunsCheckerFooterBlock (Artifact.submission.initialState .check input) after cycles ∧
      cycles≤12038+2387*input.positions.card ∧ after.pc=4096+4*2190 ∧
      CheckerFooterWidthsReady ((input.positions.sort (· ≤ ·)).map capGroup)
        ((capFrontierNodes ((input.positions.sort (· ≤ ·)).map capGroup) 1 8).map checkerFooterHighWidth)
        (checkerFooterInputStart input) after 1 ∧
      CheckerSavedABI (Artifact.submission.initialState .check input) after := by
  obtain ⟨after,cycles,ran,bound,pc,ready⟩ := checker_footer_widths_complete _ _ _
    (checker_footer_input_start_ready input nonempty lower upper) (checker_footer_input_start_pc input nonempty lower upper)
  refine ⟨after,checkerDecodedRecordsInputCycles input+4+cycles,?_,?_,pc,ready,?_⟩
  · exact RunsCheckerFooterBlock.next (checker_footer_input_start_execution input nonempty lower upper) ran
  · have before := checker_decoded_records_input_bound input
    omega
  · exact checker_footer_widths_saved_abi _ _ _ _ _ _ ready (checker_footer_input_start_saved_abi input nonempty lower upper)

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual supplied footer bytes, reconstructed records and physical parser ABI. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def checkerInputFooterNodes (input : CheckInput) : List Nat := capFrontierNodes ((input.positions.sort (· ≤ ·)).map capGroup) 1 8
def checkerInputFooterSource (input : CheckInput) : Nat := Artifact.submission.layout.proof+482*input.positions.card
def checkerInputFooterBytes (input : CheckInput) : Proof := input.proof.drop (482*input.positions.card)
def checkerInputRawRecords (input : CheckInput) : Proof := rawRecordStream (checkerDecodeRecords input.positions.card input.proof)
theorem checker_input_raw_records_length (input : CheckInput) : (checkerInputRawRecords input).length=498*input.positions.card := by
  rw [checkerInputRawRecords,raw_record_stream_length,checker_decode_records_length]
theorem checker_input_footer_source_fit (input : CheckInput)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    checkerInputFooterSource input+(checkerInputFooterBytes input).length+512≤checkingRawBase := by
  have before := checking_source_before_raw input.positions.card input.proof.length
    (by simpa [Index] using Finset.card_le_univ input.positions) upper
  rw [checkerInputFooterSource,checkerInputFooterBytes,List.length_drop]
  omega

theorem checker_footer_input_origin_register (input : CheckInput) (reg : Reg) (member : reg∈[.x8,.x12,.x13,.x14,.x15,.x17]) :
    (checkerFooterInputStart input).getReg reg=(checkerRecordInputState input).getReg reg := by
  cases reg <;> simp at member
  all_goals rw [checker_footer_input_start_eq,checker_footer_init_register _ _ (by decide),
    checker_decoded_records_input_eq,checker_record_loop_register _ _ _ (by decide)]
theorem checker_footer_input_origin_byte (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (query : Nat) (above : 8192≤query) (before : query<checkingRawBase) :
    (checkerFooterInputStart input).getByte (BitVec.ofNat 64 query)=
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query) := by
  have ready := checker_record_input_untrusted_ready input nonempty lower upper
  have room := ready.outputRoom
  have metaFit := checking_metadata_room
  have rawBefore : checkingRawBase<checkingMetadataBase := by decide +kernel
  rw [checker_footer_input_start_eq,checker_footer_init_byte,checker_decoded_records_input_eq,
    checker_record_loop_byte_frame _ _ _ Artifact.submission.layout.proof checkingRawBase _ ready]
  · exact checker_record_input_byte_frame input query above (by omega)
  · intro written inside
    rw [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  · intro written inside
    rw [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

structure CheckerFooterInputReady (input : CheckInput) (s : MachineState) : Prop where
  pc : s.pc=4096+4*2190
  bounded : (checkerInputFooterNodes input).length≤256
  pointer : s.getReg .x18=BitVec.ofNat 64 (checkerInputFooterSource input)
  rows : s.getReg .x22=BitVec.ofNat 64 (checkerInputFooterNodes input).length
  metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase
  raw : s.getReg .x12=BitVec.ofNat 64 checkingRawBase
  table : ParseWidthsAt s (s.getReg .x8) ((checkerInputFooterNodes input).map checkerFooterHighWidth)
  proofFit : checkerInputFooterSource input+(checkerInputFooterBytes input).length+512≤checkingRawBase
  endPointer : s.getReg .x15+s.getReg .x17=
    BitVec.ofNat 64 (checkerInputFooterSource input+(checkerInputFooterBytes input).length)
  outputPointer : s.getReg .x6=BitVec.ofNat 64 (checkingRawBase+(checkerInputRawRecords input).length)
  outputEnd : checkingRawBase+(checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length≤checkingMetadataBase
  memory : BytesAt s (BitVec.ofNat 64 (checkerInputFooterSource input)) (checkerInputFooterBytes input)
  previous : BytesAt s (BitVec.ofNat 64 checkingRawBase) (checkerInputRawRecords input)
  publicBytes : ∀ query, 8192≤query → query<checkingRawBase →
    s.getByte (BitVec.ofNat 64 query)=(Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query)
  saved : CheckerSavedABI (Artifact.submission.initialState .check input) s

theorem checker_footer_input_ready_of_widths (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (s : MachineState) (pc : s.pc=4096+4*2190)
    (ready : CheckerFooterWidthsReady ((input.positions.sort (· ≤ ·)).map capGroup)
      ((checkerInputFooterNodes input).map checkerFooterHighWidth) (checkerFooterInputStart input) s 1)
    (saved : CheckerSavedABI (Artifact.submission.initialState .check input) s) : CheckerFooterInputReady input s := by
  have final := checker_decoded_records_input_ready input nonempty lower upper
  have proofFit := checker_input_footer_source_fit input lower upper
  have rawBefore : checkingRawBase<checkingMetadataBase := by decide +kernel
  have low : 8192≤Artifact.submission.layout.proof := by decide +kernel
  have metaFit := checking_metadata_room
  have count : (checkerInputFooterNodes input).length≤256 := by simpa only [List.length_map] using ready.capacity
  have metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
    rw [ready.registers .x8 (by decide),checker_footer_input_origin_register input .x8 (by decide),checker_record_input_metadata]
  have publicBytes : ∀ query, 8192≤query → query<checkingRawBase →
      s.getByte (BitVec.ofNat 64 query)=(Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query) := by
    intro query above before
    rw [ready.outside query (Or.inl (by omega)) (by omega)]
    exact checker_footer_input_origin_byte input nonempty lower upper query above before
  refine ⟨pc,count,?_,?_,metadata,?_,?_,proofFit,?_,?_,?_,?_,?_,publicBytes,saved⟩
  · rw [ready.registers .x18 (by decide),checker_footer_input_start_eq,checker_footer_init_register _ .x18 (by decide)]
    exact final.sourcePointer
  · simpa only [List.length_map] using ready.count
  · rw [ready.registers .x12 (by decide),checker_footer_input_origin_register input .x12 (by decide),checker_record_input_eq,
      checker_mark_boundary_register .records _ .x12 (by decide),checker_marks_ready_input_register input .x12 (by decide),checker_seeded_input_raw]
  · rw [metadata]
    exact ready.widths
  · rw [ready.registers .x15 (by decide),ready.registers .x17 (by decide),
      checker_footer_input_origin_register input .x15 (by decide),checker_footer_input_origin_register input .x17 (by decide),
      checker_record_input_register input .x15 (by decide),checker_record_input_register input .x17 (by decide),
      (checker_input_registers input).2.2.2.2.1,(checker_input_registers input).2.2.2.2.2.2]
    change BitVec.ofNat 64 Artifact.submission.layout.proof+BitVec.ofNat 64 input.proof.length=_
    rw [←BitVec.ofNat_add]
    congr 1
    rw [checkerInputFooterSource,checkerInputFooterBytes,List.length_drop]
    omega
  · rw [ready.registers .x6 (by decide),checker_footer_input_start_eq,checker_footer_init_register _ .x6 (by decide),
      checker_input_raw_records_length]
    exact final.outputPointer
  · have room := checking_raw_before_metadata input.positions.card (by simpa [Index] using Finset.card_le_univ input.positions)
    rw [checker_input_raw_records_length]
    omega
  · have memory : BytesAt (checkerDecodedRecordsInputState input) (BitVec.ofNat 64 (checkerInputFooterSource input))
        (checkerInputFooterBytes input) := by
      simpa only [checkerInputFooterSource,checkerInputFooterBytes,encodedRecords,List.flatMap_nil,List.nil_append] using final.input
    intro offset inside
    rw [←BitVec.ofNat_add,ready.outside _ (Or.inl (by omega)) (by omega),
      checker_footer_input_start_eq,checker_footer_init_byte]
    have point := memory offset inside
    rw [←BitVec.ofNat_add] at point
    exact point
  · have previous := checker_decoded_records_input_memory input nonempty lower upper
    have room := checking_raw_before_metadata input.positions.card (by simpa [Index] using Finset.card_le_univ input.positions)
    intro offset inside
    have before : offset<498*input.positions.card := by simpa only [checker_input_raw_records_length] using inside
    rw [←BitVec.ofNat_add,ready.outside _ (Or.inl (by omega)) (by omega),
      checker_footer_input_start_eq,checker_footer_init_byte]
    have point := previous offset inside
    rw [←BitVec.ofNat_add] at point
    exact point

theorem checker_footer_input_delivered (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    ∃ s cycles, RunsCheckerFooterBlock (Artifact.submission.initialState .check input) s cycles ∧
      cycles≤12038+2387*input.positions.card ∧ CheckerFooterInputReady input s := by
  obtain ⟨s,cycles,ran,bound,pc,ready,saved⟩ := checker_footer_widths_from_input input nonempty lower upper
  exact ⟨s,cycles,ran,bound,checker_footer_input_ready_of_widths input nonempty lower upper s pc ready saved⟩

end CommitGolfCandidate.Chained.Native

end

section

/-! Complete supplied-footer reconstruction and original-ABI cryptographic entry. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

private theorem merged_ChainedCheckerDecodedInput_record_footer_length_sub (base records footer : Nat) :
    base+records+30*footer-base=records+30*footer := by omega

theorem checker_footer_input_source_end {input : CheckInput} {s : MachineState} (ready : CheckerFooterInputReady input s)
    (enough : CheckerFooterLowBodyFits s) :
    checkerInputFooterSource input+30*(checkerInputFooterNodes input).length+1≤checkingRawBase := by
  have body := checker_footer_guarded_body_length s (checkerInputFooterSource input) (checkerInputFooterNodes input)
    (checkerInputFooterBytes input) ready.bounded ready.pointer ready.rows ready.proofFit ready.endPointer enough
  have fit := ready.proofFit
  have bounded := ready.bounded
  omega
theorem checker_decoder_restored_byte (s : MachineState) (query : Word) :
    (checkerDecoderRestoredState s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_decoder_restored_memory]
theorem checker_footer_input_reconstructed_saved {input : CheckInput} {s : MachineState}
    (ready : CheckerFooterInputReady input s) (enough : CheckerFooterLowBodyFits s) :
    CheckerSavedABI (Artifact.submission.initialState .check input)
      (checkerFooterReconstructedState (checkerInputFooterNodes input).length s) := by
  have small : ∀ width∈(checkerInputFooterNodes input).map checkerFooterHighWidth, width≤6 := by
    intro width member
    obtain ⟨node,_,rfl⟩ := List.mem_map.mp member
    exact checker_footer_high_width_small node
  simpa only [List.length_map] using checker_footer_reconstructed_saved_abi _ s (checkerInputFooterSource input)
    (checkingRawBase+(checkerInputRawRecords input).length) ((checkerInputFooterNodes input).map checkerFooterHighWidth)
    (by simpa only [List.length_map] using ready.bounded) ready.pointer
    (by simpa only [List.length_map] using ready.rows) ready.metadata
    (by simpa only [List.length_map] using checker_footer_input_source_end ready enough) small ready.table
    ready.outputPointer (by simpa only [List.length_map] using ready.outputEnd) ready.saved
theorem checker_footer_input_reconstructed_public {input : CheckInput} {s : MachineState}
    (ready : CheckerFooterInputReady input s) (enough : CheckerFooterLowBodyFits s)
    (query : Nat) (above : 8192≤query) (before : query<checkingRawBase) :
    (checkerFooterReconstructedState (checkerInputFooterNodes input).length s).getByte (BitVec.ofNat 64 query)=
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query) := by
  have small : ∀ width∈(checkerInputFooterNodes input).map checkerFooterHighWidth, width≤6 := by
    intro width member
    obtain ⟨node,_,rfl⟩ := List.mem_map.mp member
    exact checker_footer_high_width_small node
  have metaFit := checking_metadata_room
  have rawBefore : checkingRawBase<checkingMetadataBase := by decide +kernel
  have frame := checker_footer_reconstructed_byte_frame s (checkerInputFooterSource input)
    ((checkerInputFooterNodes input).map checkerFooterHighWidth)
    (by simpa only [List.length_map] using ready.bounded) ready.pointer
    (by simpa only [List.length_map] using ready.rows) ready.metadata
    (by simpa only [List.length_map] using checker_footer_input_source_end ready enough) small ready.table
    (BitVec.ofNat 64 query) (by
      intro index inside
      have room := ready.outputEnd
      rw [List.length_map] at inside
      rw [ready.outputPointer,←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)) (by
      intro index inside
      have bounded := ready.bounded
      rw [List.length_map] at inside
      rw [ready.metadata,←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega))
  simp only [List.length_map] at frame
  exact frame.trans (ready.publicBytes query above before)

structure CheckerDecodedInput (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState) : Prop where
  pc : s.pc=4096+4*2367
  abi : ∀ slot : Fin 4, s.getReg (checkerSavedReg slot)=
    (Artifact.submission.initialState .check input).getReg (checkerSavedReg slot)
  source : s.getReg .x15=BitVec.ofNat 64 checkingRawBase
  length : s.getReg .x17=BitVec.ofNat 64 ((checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length)
  canonical : unpack (InteriorCodec.footerSpec (checkerInputFooterNodes input)) (checkerInputFooterBytes input)=some footer
  memory : BytesAt s (BitVec.ofNat 64 checkingRawBase)
    (checkerInputRawRecords input++rawFieldsBytes (footerRawFields (checkerInputFooterNodes input) footer))
  publicBytes : ∀ query, 8192≤query → query<checkingRawBase →
    s.getByte (BitVec.ofNat 64 query)=(Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query)

theorem checker_footer_input_decodes (input : CheckInput) (nonempty : input.positions.card≠0) (s : MachineState)
    (ready : CheckerFooterInputReady input s) (enough : CheckerFooterLowBodyFits s)
    (accepted : (checkerFooterParsedState (checkerInputFooterNodes input).length s).getReg .x24=1#64) :
    ∃ footer after cycles, RunsCheckerFooterBlock s after cycles ∧ cycles≤139*(checkerInputFooterNodes input).length+30 ∧
      CheckerDecodedInput input footer after := by
  obtain ⟨cycles,bound,ran,pc,canonical,memory,source,output,metadata,count⟩ := checker_footer_decode_complete s
    (checkerInputFooterSource input) checkingRawBase (checkerInputFooterNodes input) (checkerInputFooterBytes input)
    (checkerInputRawRecords input) ready.bounded ready.pointer ready.rows ready.metadata ready.table ready.proofFit
    ready.endPointer (Nat.le_refl _) ready.outputPointer ready.outputEnd ready.memory ready.previous ready.pc enough accepted
  let before := checkerFooterReconstructedState (checkerInputFooterNodes input).length s
  have finalMeta : before.getReg .x8=BitVec.ofNat 64 checkingMetadataBase :=
    (checker_footer_reconstructed_register _ s .x8 (by decide)).trans ready.metadata
  have finalSaved : CheckerSavedABI (Artifact.submission.initialState .check input) before :=
    checker_footer_input_reconstructed_saved ready enough
  have finalRaw : before.getReg .x12=BitVec.ofNat 64 checkingRawBase :=
    (checker_footer_reconstructed_register _ s .x12 (by decide)).trans ready.raw
  have restore : RunsCheckerFooterBlock before (checkerDecoderRestoredState before) 9 := by
    exact checker_decoder_restore_execution before pc finalMeta
      (checker_restore_original_nonempty _ before finalMeta finalSaved (checker_seed_input_nonempty input nonempty))
  refine ⟨checkerFooterParsedPayload (checkerInputFooterNodes input) (checkerInputFooterBytes input) s
    (checkerInputFooterSource input),checkerDecoderRestoredState before,cycles+9,RunsCheckerFooterBlock.next ran restore,by omega,?_⟩
  refine ⟨(checker_decoder_restored_view before).1,checker_restore_original_abi _ before finalMeta finalSaved,?_,?_,canonical,?_,?_⟩
  · exact (checker_decoder_restored_view before).2.2.2.2.2.1.trans finalRaw
  · rw [(checker_decoder_restored_view before).2.2.2.2.2.2,output,finalRaw]
    change BitVec.ofNat 64 (checkingRawBase+(checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length)-
      BitVec.ofNat 64 checkingRawBase=_
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide +kernel) (by omega)]
    exact congrArg (BitVec.ofNat 64) (merged_ChainedCheckerDecodedInput_record_footer_length_sub checkingRawBase
      (checkerInputRawRecords input).length (checkerInputFooterNodes input).length)
  · intro index inside
    rw [checker_decoder_restored_byte]
    exact memory index inside
  · intro query above beforeRaw
    rw [checker_decoder_restored_byte]
    exact checker_footer_input_reconstructed_public ready enough query above beforeRaw

theorem checker_footer_input_invalid (input : CheckInput) (s : MachineState) (ready : CheckerFooterInputReady input s)
    (enough : CheckerFooterLowBodyFits s)
    (invalid : (checkerFooterParsedState (checkerInputFooterNodes input).length s).getReg .x24=0#64) :
    ∃ after cycles, cycles≤17*(checkerInputFooterNodes input).length+20 ∧
      ∀ fuel coins, execute (Artifact.submission.image .check) (cycles+fuel) s coins=pure ⟨.failure,after,cycles,0⟩ := by
  have small : ∀ width∈(checkerInputFooterNodes input).map checkerFooterHighWidth, width≤6 := by
    intro width member
    obtain ⟨node,_,rfl⟩ := List.mem_map.mp member
    exact checker_footer_high_width_small node
  obtain ⟨after,rejects⟩ := checker_footer_invalid_complete s (checkerInputFooterSource input)
    ((checkerInputFooterNodes input).map checkerFooterHighWidth) (by simpa only [List.length_map] using ready.bounded)
    ready.pointer (by simpa only [List.length_map] using ready.rows) ready.metadata
    (by simpa only [List.length_map] using checker_footer_input_source_end ready enough) small ready.table ready.pc enough
    (by simpa only [List.length_map] using invalid)
  simp only [List.length_map] at rejects
  refine ⟨after,11+checkerFooterParserCycles (checkerInputFooterNodes input).length s+5,?_,rejects⟩
  have bound := checker_footer_parser_cycles_bound (checkerInputFooterNodes input).length s
  omega

def CheckerRejectedBlock (s : MachineState) (cycles : Nat) : Prop :=
  ∃ after, ∀ fuel coins, execute (Artifact.submission.image .check) (cycles+fuel) s coins=pure ⟨.failure,after,cycles,0⟩

theorem checker_rejected_after_block {before middle : MachineState} {first second : Nat}
    (ran : RunsCheckerFooterBlock before middle first) (rejected : CheckerRejectedBlock middle second) :
    CheckerRejectedBlock before (first+second) := by
  obtain ⟨after,rejects⟩ := rejected
  refine ⟨after,?_⟩
  intro fuel coins
  rw [Nat.add_assoc,ran,rejects]
  simp [Execution.charge,Nat.add_comm]

theorem checker_decoded_input_cases (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (∃ cycles, cycles≤47652+2387*input.positions.card ∧
      CheckerRejectedBlock (Artifact.submission.initialState .check input) cycles) ∨
    (∃ footer after cycles, cycles≤47652+2387*input.positions.card ∧
      RunsCheckerFooterBlock (Artifact.submission.initialState .check input) after cycles ∧ CheckerDecodedInput input footer after) := by
  obtain ⟨s,first,ran,before,ready⟩ := checker_footer_input_delivered input nonempty lower upper
  have bounded := ready.bounded
  by_cases enough : CheckerFooterLowBodyFits s
  · rcases checker_footer_flag_cases (checkerInputFooterNodes input).length s with invalid | accepted
    · obtain ⟨after,second,bound,rejects⟩ := checker_footer_input_invalid input s ready enough invalid
      exact Or.inl ⟨first+second,by omega,checker_rejected_after_block ran ⟨after,rejects⟩⟩
    · obtain ⟨footer,after,second,run,bound,decoded⟩ := checker_footer_input_decodes input nonempty s ready enough accepted
      exact Or.inr ⟨footer,after,first+second,by omega,RunsCheckerFooterBlock.next ran run,decoded⟩
  · obtain ⟨after,rejects⟩ := checker_footer_short_rejects s ready.pc enough
    exact Or.inl ⟨first+12,by omega,checker_rejected_after_block ran ⟨after,rejects⟩⟩

theorem checker_decoded_input_fuel (input : CheckInput) :
    47652+2387*input.positions.card≤Artifact.submission.steps .check := by
  have cardinal : input.positions.card≤16777216 := by
    have bound : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bound
  change 47652+2387*input.positions.card≤1099511627776
  omega

theorem checker_encoded_input_decodes (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input)))
    (encoded : checkerInputFooterBytes input=encode footer) :
    ∃ after cycles, RunsCheckerFooterBlock (Artifact.submission.initialState .check input) after cycles ∧
      cycles≤47652+2387*input.positions.card ∧ CheckerDecodedInput input footer after := by
  obtain ⟨state,first,ran,bound,ready⟩ := checker_footer_input_delivered input nonempty lower upper
  have enough := checker_footer_encoded_fits state (checkerInputFooterSource input) (checkerInputFooterNodes input)
    footer ready.bounded ready.pointer ready.rows (by rw [←encoded]; exact ready.proofFit)
    (by rw [←encoded]; exact ready.endPointer)
  have accepted := checker_footer_encoded_accepts state (checkerInputFooterSource input) (checkerInputFooterNodes input)
    footer ready.bounded ready.pointer ready.rows ready.metadata ready.table (by rw [←encoded]; exact ready.proofFit)
    (by rw [←encoded]; exact ready.endPointer) (by rw [←encoded]; exact ready.memory)
  obtain ⟨decoded,after,last,continued,lastBound,complete⟩ := checker_footer_input_decodes input nonempty state ready enough accepted
  have same : decoded=footer := by
    have canonical := complete.canonical
    rw [encoded,unpack_encode] at canonical
    exact (Option.some.inj canonical).symm
  subst decoded
  exact ⟨after,first+last,RunsCheckerFooterBlock.next ran continued,by have := ready.bounded; omega,complete⟩

end CommitGolfCandidate.Chained.Native

end
