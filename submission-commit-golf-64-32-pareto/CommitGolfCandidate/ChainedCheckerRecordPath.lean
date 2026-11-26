import CommitGolfCandidate.ChainedCheckerCryptoEntry
import CommitGolfCandidate.TwoPermutationPackedCopy

/-! Delivered nonce/path/frontier copies and the public-index leaf header. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Packed
set_option maxRecDepth 8192
attribute [local irreducible] execute

inductive CheckerCopySite where | nonce | odd | even | firstOdd | firstEven | frontier
def CheckerCopySite.start : CheckerCopySite → Nat
  | .nonce => 2402 | .odd => 2442 | .even => 2490 | .firstOdd => 2525 | .firstEven => 2574 | .frontier => 2672
def CheckerCopySite.count : CheckerCopySite → Nat
  | .nonce => 8 | .firstOdd | .firstEven => 16 | _ => 15
def CheckerCopySite.dest : CheckerCopySite → Reg
  | .nonce => .x4 | .frontier => .x7 | _ => .x24
def CheckerCopySite.offset : CheckerCopySite → Nat
  | .even | .firstEven => 32 | _ => 0
def CheckerCopySite.ops (site : CheckerCopySite) : List Instr :=
  (List.range site.count).flatMap fun j =>
    [.LHU .x31 .x21 (BitVec.ofNat 12 (2*j)),.SH site.dest .x31 (BitVec.ofNat 12 (site.offset+2*j))]
theorem checker_copy_at (site : CheckerCopySite) :
    OpsAt chainedCheckerImage (BitVec.ofNat 64 (4096+4*site.start)) site.ops := by
  cases site
  · exact chained_checker_slice_at 2402 16 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2442 30 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2490 30 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2525 32 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2574 32 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2672 30 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
private theorem checker_copy_length (site : CheckerCopySite) : site.ops.length=2*site.count := by
  cases site <;> decide +kernel
def checkerCopyCode (site : CheckerCopySite) : CopyCode where
  image := chainedCheckerImage
  start := site.start
  count := site.count
  source := .x21
  dest := site.dest
  destOffset := site.offset
  sourceTemp := by decide
  destTemp := by cases site <;> decide
  offsetBound := by cases site <;> decide
  load := by
    intro j inside s pc
    have shape : site.ops.getD (2*j) .EBREAK=.LHU .x31 .x21 (BitVec.ofNat 12 (2*j)) := by
      cases site <;> simp only [CheckerCopySite.count] at inside
      all_goals interval_cases j <;> rfl
    have located : s.pc=BitVec.ofNat 64 (4096+4*site.start)+BitVec.ofNat 64 (4*(2*j)) := by
      rw [pc]
      change BitVec.ofNat 64 (4096+4*(site.start+2*j))=BitVec.ofNat 64 (4096+4*site.start)+BitVec.ofNat 64 (4*(2*j))
      rw [←BitVec.ofNat_add]
      congr 1
      omega
    simpa only [shape] using checker_copy_at site (2*j) (by rw [checker_copy_length]; omega) s located
  store := by
    intro j inside s pc
    have shape : site.ops.getD (2*j+1) .EBREAK=.SH site.dest .x31 (BitVec.ofNat 12 (site.offset+2*j)) := by
      cases site <;> simp only [CheckerCopySite.count] at inside
      all_goals interval_cases j <;> rfl
    have located : s.pc=BitVec.ofNat 64 (4096+4*site.start)+BitVec.ofNat 64 (4*(2*j+1)) := by
      rw [pc]
      change BitVec.ofNat 64 (4096+4*(site.start+2*j+1))=BitVec.ofNat 64 (4096+4*site.start)+BitVec.ofNat 64 (4*(2*j+1))
      rw [←BitVec.ofNat_add]
      congr 1
      omega
    simpa only [shape] using checker_copy_at site (2*j+1) (by rw [checker_copy_length]; omega) s located
@[irreducible] def checkerCopyState (site : CheckerCopySite) (s : MachineState) : MachineState :=
  copyField (checkerCopyCode site) s
theorem checker_copy_state_eq (site : CheckerCopySite) (s : MachineState) :
    checkerCopyState site s=copyField (checkerCopyCode site) s := by rw [checkerCopyState]
theorem checker_copy_execution (site : CheckerCopySite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (checkerCopyCode site) s source target 0) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2*site.count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCopyState site s) coins
          return result.charge (2*site.count) 0) := by
  rw [checking_manifest_image,checker_copy_state_eq]
  exact copy_field_execute (checkerCopyCode site) s source target ready fuel coins
theorem checker_copy_register (site : CheckerCopySite) (s : MachineState) (reg : Reg) (kept : reg≠.x31) :
    (checkerCopyState site s).getReg reg=s.getReg reg := by
  rw [checker_copy_state_eq]
  exact copy_field_register _ _ _ kept
theorem checker_copy_pc (site : CheckerCopySite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (checkerCopyCode site) s source target 0) :
    (checkerCopyState site s).pc=BitVec.ofNat 64 (4096+4*(site.start+2*site.count)) := by
  rw [checker_copy_state_eq]
  exact copy_field_pc _ _ _ _ ready
theorem checker_copy_bytes (site : CheckerCopySite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (checkerCopyCode site) s source target 0) (ordered : target≤source) :
    (∀ index, index<2*site.count → (checkerCopyState site s).getByte (BitVec.ofNat 64 (target+index))=
      s.getByte (BitVec.ofNat 64 (source+index))) ∧
    (∀ query, (∀ index, index<2*site.count → query≠BitVec.ofNat 64 (target+index)) →
      (checkerCopyState site s).getByte query=s.getByte query) := by
  have memory := copy_field_memory (checkerCopyCode site) s source target ready
  have limit : MEMORY_BYTES≤2^64 := by decide
  have sourceBound : source+2*site.count≤2^64 := ready.srcBound.trans limit
  have targetBound : target+2*site.count≤2^64 := ready.dstBound.trans limit
  have result := ProjectedHalfword.forward_memory site.count s source target ordered sourceBound targetBound ready.srcAligned ready.dstAligned
  rw [checker_copy_state_eq]
  simpa only [MachineState.getByte,MachineState.getMem,memory,show (checkerCopyCode site).count=site.count from rfl] using result

def checkerLeafHeadOps : List Instr := [.ADDI .x5 .x0 0,.LD .x6 .x8 0,.SLLI .x28 .x6 8,
  .ADD .x28 .x3 .x28,.ADDI .x10 .x19 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1]
@[irreducible] def checkerLeafHeadPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (checkerLeafHeadOps.getD i .EBREAK)) n
theorem checker_leaf_head_zero (s : MachineState) : checkerLeafHeadPrefix 0 s=s := by rw [checkerLeafHeadPrefix]; rfl
theorem checker_leaf_head_succ (n : Nat) (s : MachineState) : checkerLeafHeadPrefix (n+1) s=
    execInstrBr (checkerLeafHeadPrefix n s) (checkerLeafHeadOps.getD n .EBREAK) := by unfold checkerLeafHeadPrefix; rfl
theorem checker_leaf_head_at : OpsAt chainedCheckerImage (4096+4*2395) checkerLeafHeadOps :=
  chained_checker_slice_at 2395 7 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_leaf_head_pc (n : Nat) (s : MachineState) (small : n≤7) :
    (checkerLeafHeadPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 7) : (execInstrBr t (checkerLeafHeadOps.getD i.val .EBREAK)).pc=t.pc+4 := by fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_leaf_head_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_leaf_head_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    change s.pc+(BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4)=s.pc+BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 2
theorem checker_leaf_head_register (n : Nat) (s : MachineState) (small : n≤7) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x28,.x10,.x11,.x13]) : (checkerLeafHeadPrefix n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 7) : (execInstrBr t (checkerLeafHeadOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i <;> cases reg <;> simp at kept <;> rfl
  induction n with
  | zero => rw [checker_leaf_head_zero]
  | succ n ih => rw [checker_leaf_head_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_leaf_head_memory (n : Nat) (s : MachineState) (small : n≤7) (query : Word) :
    (checkerLeafHeadPrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 7) : (execInstrBr t (checkerLeafHeadOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_leaf_head_zero]
  | succ n ih => rw [checker_leaf_head_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_leaf_head_execution (s : MachineState) (pc : s.pc=4096+4*2395)
    (valid : accessValid (s.getReg .x8) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (7+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLeafHeadPrefix 7 s) coins
          return result.charge 7 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_leaf_head_zero s]
  apply execute_unit_steps (states := fun n => checkerLeafHeadPrefix n s)
  intro i inside
  refine ⟨.base (checkerLeafHeadOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_leaf_head_at i inside
    rw [checker_leaf_head_pc i s (by omega),pc]
  · rw [checker_leaf_head_succ]
    interval_cases i
    · rfl
    · change (if accessValid ((checkerLeafHeadPrefix 1 s).getReg .x8+0#64) 8 then _ else _)=_
      rw [BitVec.add_zero,checker_leaf_head_register 1 s (by decide) .x8 (by decide)]
      exact ite_eq_left valid
    all_goals rfl
  · interval_cases i <;> rfl

theorem checker_leaf_head_byte (n : Nat) (s : MachineState) (small : n≤7) (query : Word) :
    (checkerLeafHeadPrefix n s).getByte query=s.getByte query := by
  have memory : (checkerLeafHeadPrefix n s).mem=s.mem := by
    funext address
    exact checker_leaf_head_memory n s small address
  simp only [MachineState.getByte,MachineState.getMem,memory]
theorem checker_record_first_indices (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) : (checkerCryptoRecordState s).getReg .x8=5905584160#64 := by
  rw [checker_crypto_record_assigned s .x8 (by decide +kernel)]
  change s.getReg .x13=5905584160#64
  exact (ready.abi ⟨1,by decide⟩).trans (checker_input_registers input).2.2.1
theorem checker_record_first_index_access (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) : accessValid ((checkerCryptoRecordState s).getReg .x8) 8=true := by
  rw [checker_record_first_indices input footer s ready]
  decide +kernel
theorem checker_record_nonce_ready (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    CopyReady (checkerCopyCode .nonce) (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s)) checkingRawBase 12272 0 := by
  refine ⟨?_,?_,?_,by decide +kernel,by decide +kernel,by decide +kernel,by decide⟩
  · change (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s)).pc=BitVec.ofNat 64 (4096+4*2402)
    rw [checker_leaf_head_pc 7 _ (by decide),checker_crypto_record_pc]
    rfl
  · change (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s)).getReg .x21=BitVec.ofNat 64 checkingRawBase
    rw [checker_leaf_head_register 7 _ (by decide) .x21 (by decide),checker_crypto_record_assigned s .x21 (by decide +kernel)]
    exact ready.source
  · change (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s)).getReg .x4+0#64=12272#64
    rw [BitVec.add_zero,checker_leaf_head_register 7 _ (by decide) .x4 (by decide),checker_crypto_record_assigned s .x4 (by decide +kernel)]
    rfl
@[irreducible] def checkerRecordNonceState (s : MachineState) : MachineState :=
  checkerCopyState .nonce (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s))
theorem checker_record_nonce_eq (s : MachineState) : checkerRecordNonceState s=
    checkerCopyState .nonce (checkerLeafHeadPrefix 7 (checkerCryptoRecordState s)) := by rw [checkerRecordNonceState]
theorem checker_decoded_nonce_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2095+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordNonceState s) coins
          return result.charge 2095 0) := by
  rw [checker_record_nonce_eq,show 2095+fuel=2072+(7+(2*CheckerCopySite.nonce.count+fuel)) by simp only [CheckerCopySite.count]; omega,
    checker_decoded_record_execution input nonempty footer s ready,
    checker_leaf_head_execution _ (checker_crypto_record_pc s) (checker_record_first_index_access input footer s ready),
    checker_copy_execution .nonce _ checkingRawBase 12272 (checker_record_nonce_ready input footer s ready)]
  simp [Execution.charge,CheckerCopySite.count,←Nat.add_assoc]
theorem checker_record_nonce_pc (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) : (checkerRecordNonceState s).pc=4096+4*2418 := by
  rw [checker_record_nonce_eq,checker_copy_pc .nonce _ checkingRawBase 12272 (checker_record_nonce_ready input footer s ready)]
  rfl
theorem checker_record_nonce_byte (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (index : Nat) (inside : index<16) :
    (checkerRecordNonceState s).getByte (BitVec.ofNat 64 (12272+index))=
      s.getByte (BitVec.ofNat 64 (checkingRawBase+index)) := by
  have result := (checker_copy_bytes .nonce _ checkingRawBase 12272
    (checker_record_nonce_ready input footer s ready) (by decide +kernel)).1 index inside
  have low : 8192≤checkingRawBase := by decide +kernel
  have fit : checkingRawBase+16<2^64 := by decide +kernel
  rw [←checker_record_nonce_eq,checker_leaf_head_byte 7 _ (by decide),checker_crypto_record_byte s _ (by omega) (by omega)] at result
  exact result

private def leafHeadDestination (index : Nat) : Reg := [.x5,.x6,.x28,.x28,.x10,.x11,.x13].getD index .x0
private theorem leaf_head_step_kept (s : MachineState) (index : Fin 7) (reg : Reg) (kept : reg≠leafHeadDestination index.val) :
    (execInstrBr s (checkerLeafHeadOps.getD index.val .EBREAK)).getReg reg=s.getReg reg := by
  fin_cases index <;> cases reg <;> simp [leafHeadDestination] at kept <;> rfl
private theorem leaf_head_suffix (s : MachineState) (start stop : Nat) (reg : Reg)
    (ordered : start≤stop) (small : stop≤7)
    (kept : ∀ index : Fin 7, start ≤ index.val → index.val<stop → reg≠leafHeadDestination index.val) :
    (checkerLeafHeadPrefix stop s).getReg reg=(checkerLeafHeadPrefix start s).getReg reg := by
  induction stop with
  | zero =>
    have eq : start=0 := by omega
    subst start
    rfl
  | succ stop ih =>
    by_cases last : start=stop+1
    · rw [last]
    · have untouched : reg≠leafHeadDestination stop := kept ⟨stop,by omega⟩ (by change start≤stop; omega) (by change stop<stop+1; omega)
      rw [checker_leaf_head_succ,leaf_head_step_kept _ ⟨stop,by omega⟩ reg untouched]
      exact ih (by omega) (by omega) (fun index low high => kept index low (by omega))
private theorem leaf_head_last_write (s : MachineState) (reg : Reg) (index : Fin 7)
    (last : ∀ next : Fin 7, index.val<next.val → reg≠leafHeadDestination next.val) :
    (checkerLeafHeadPrefix 7 s).getReg reg=
      (execInstrBr (checkerLeafHeadPrefix index.val s) (checkerLeafHeadOps.getD index.val .EBREAK)).getReg reg := by
  rw [←checker_leaf_head_succ]
  exact leaf_head_suffix s _ 7 reg (by have := index.isLt; omega) (by decide) (fun next low _ => last next (by omega))
theorem checker_leaf_head_loaded (s : MachineState) : (checkerLeafHeadPrefix 2 s).getReg .x6=s.getMem (s.getReg .x8) := by
  rw [checker_leaf_head_succ]
  change (checkerLeafHeadPrefix 1 s).getMem ((checkerLeafHeadPrefix 1 s).getReg .x8+0#64)=_
  rw [BitVec.add_zero,checker_leaf_head_memory 1 s (by decide),checker_leaf_head_register 1 s (by decide) .x8 (by decide)]
theorem checker_leaf_head_index (s : MachineState) : (checkerLeafHeadPrefix 7 s).getReg .x6=s.getMem (s.getReg .x8) := by
  rw [leaf_head_last_write s .x6 ⟨1,by decide⟩ (by decide +kernel),←checker_leaf_head_succ]
  exact checker_leaf_head_loaded s
theorem checker_leaf_head_tag (s : MachineState) :
    (checkerLeafHeadPrefix 7 s).getReg .x28=s.getReg .x3+(s.getMem (s.getReg .x8) <<< 8) := by
  rw [leaf_head_last_write s .x28 ⟨3,by decide⟩ (by decide +kernel)]
  change (checkerLeafHeadPrefix 3 s).getReg .x3+(checkerLeafHeadPrefix 3 s).getReg .x28=_
  rw [checker_leaf_head_register 3 s (by decide) .x3 (by decide),checker_leaf_head_succ]
  change s.getReg .x3+((checkerLeafHeadPrefix 2 s).getReg .x6 <<< 8)=_
  rw [checker_leaf_head_loaded]
theorem checker_leaf_head_source (s : MachineState) : (checkerLeafHeadPrefix 7 s).getReg .x10=s.getReg .x19 := by
  rw [leaf_head_last_write s .x10 ⟨4,by decide⟩ (by decide +kernel)]
  change (checkerLeafHeadPrefix 4 s).getReg .x19+0#64=_
  rw [checker_leaf_head_register 4 s (by decide) .x19 (by decide),BitVec.add_zero]
theorem checker_leaf_head_selector (s : MachineState) : (checkerLeafHeadPrefix 7 s).getReg .x5=0#64 := by
  rw [leaf_head_last_write s .x5 ⟨0,by decide⟩ (by decide +kernel)]
  rfl
theorem checker_leaf_head_size (s : MachineState) : (checkerLeafHeadPrefix 7 s).getReg .x11=200#64 := by
  rw [leaf_head_last_write s .x11 ⟨5,by decide⟩ (by decide +kernel)]
  rfl
theorem checker_leaf_head_primitive (s : MachineState) : (checkerLeafHeadPrefix 7 s).getReg .x13=1#64 := by
  rw [leaf_head_last_write s .x13 ⟨6,by decide⟩ (by decide +kernel)]
  rfl

private theorem leaf_read_aligned_word (s : MachineState) (address : Nat) (aligned : address%8=0) :
    readBuffer s address 8=s.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice s address 32 0 8 (by decide)
  have word := read_digest_word s address 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using slice.symm.trans word
theorem checker_record_public_word (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (address : Nat) (aligned : address%8=0)
    (above : 8192≤address) (before : address+8≤checkingRawBase) :
    (checkerCryptoRecordState s).getMem (BitVec.ofNat 64 address)=
      (Artifact.submission.initialState .check input).getMem (BitVec.ofNat 64 address) := by
  rw [←leaf_read_aligned_word _ address aligned,←leaf_read_aligned_word _ address aligned]
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset inside
  have bound := Finset.mem_range.mp inside
  rw [checker_crypto_record_public input footer s ready _ (by omega) (by omega)]
def checkerFirstInputIndex (input : CheckInput) (nonempty : input.positions.card≠0) : Index :=
  (input.positions.sort (· ≤ ·))[0]'(by rw [Finset.length_sort]; omega)
theorem checker_record_nonce_index (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    (checkerRecordNonceState s).getReg .x6=BitVec.ofNat 64 (checkerFirstInputIndex input nonempty).val := by
  rw [checker_record_nonce_eq,checker_copy_register .nonce _ .x6 (by decide),checker_leaf_head_index,
    checker_record_first_indices input footer s ready,
    checker_record_public_word input footer s ready 5905584160 (by decide) (by decide) (by decide +kernel)]
  exact checker_input_position input 0 (by omega)

end CommitGolfCandidate.Chained.Native
