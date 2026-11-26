import CommitGolfCandidate.HeadStreamCheckRun
import CommitGolfCandidate.TailStreamCheckRun
import CommitGolfCandidate.TwoPermutationPackedUnpackRun

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamZero
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def headStart (input : CheckInput) : MachineState :=
  (execInstrBr (Assembly.submission.initialState .check input) (.ADDI .x6 .x0 498)).setPC (pcOf 0)

def zeroInput (input : CheckInput) : CheckInput :=
  { input with proof := restore input.positions.card input.proof }

@[simp] theorem zero_positions (input : CheckInput) : (zeroInput input).positions=input.positions := rfl

@[simp] theorem zero_length (input : CheckInput) :
    (zeroInput input).proof.length=input.proof.length+input.positions.card := by
  simp [zeroInput,expandedLength]

variable [UnpackOrigin]

theorem head_start_byte (input : CheckInput) (a : Word) :
    (headStart input).getByte a=inputByte Assembly.submission .check input a.toNat := by
  change (Assembly.submission.initialState .check input).getByte a=_
  exact initial_byte input a

theorem entry_source (input : CheckInput) (j : Nat) (hj : j<2^34) :
    (headStart input).getByte (BitVec.ofNat 64 (proofBase+j))=input.proof.getD j 0 := by
  rw [head_start_byte,PackedOpening.Pack.toNat_w _ (by unfold proofBase;omega),
    input_byte_high _ _ (by omega),Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD]

theorem entry_scratch_zero (input : CheckInput) (fits : input.proof.length≤8355061248)
    (a : Word) (ha : proofBase+2^33≤a.toNat ∧ a.toNat<proofBase+2^33+input.positions.card) :
    (headStart input).getByte a=0 := by
  rw [head_start_byte,input_byte_high _ _ (by omega),List.getElem?_eq_none (by omega),Option.getD_none]

theorem zero_input_byte (input : CheckInput) (a : Word) :
    (if proofBase≤a.toNat ∧ a.toNat<proofBase+input.proof.length+input.positions.card
     then expandedByte input.positions.card input.proof (a.toNat-proofBase) else (headStart input).getByte a)=
      inputByte Assembly.submission .check (zeroInput input) a.toNat := by
  by_cases inside : proofBase≤a.toNat ∧ a.toNat<proofBase+input.proof.length+input.positions.card
  · rw [if_pos inside,input_byte_high _ _ inside.1]
    change _=(List.ofFn (fun p : Fin (expandedLength input.positions.card input.proof.length) =>
      expandedByte input.positions.card input.proof p.val))[a.toNat-proofBase]?.getD 0
    have bound : a.toNat-proofBase<expandedLength input.positions.card input.proof.length := by
      unfold expandedLength
      omega
    rw [List.getElem?_ofFn,dif_pos bound,Option.getD_some]
  · rw [if_neg inside,head_start_byte]
    by_cases low : a.toNat<proofBase
    · exact (input_byte_low input _ _ low).symm
    · rw [input_byte_high _ _ (by omega),input_byte_high _ _ (by omega),
        List.getElem?_eq_none (by omega),List.getElem?_eq_none (by rw [zero_length];omega)]

theorem state_eq_origin (origin : Word → Word) (s t : MachineState)
    (regs : ∀ r,s.getReg r=t.getReg r) (pc : s.pc=t.pc) (metadata : other s=other t)
    (bytes : ∀ a,s.getByte a=t.getByte a)
    (frame : ∀ a,alignToDword a≠a → s.mem a=origin a) : s=withMemoryOrigin origin t := by
  have mem := mem_eq_origin origin s t bytes frame
  have zero : s.regs .x0=t.regs .x0 := congrArg (fun p => p.2.2.2.2.2) metadata
  have registerFile : s.regs=t.regs := by
    funext r
    by_cases hr : r=.x0
    · subst r
      exact zero
    · have left : s.getReg r=s.regs r := by cases r <;> simp_all [MachineState.getReg]
      have right : t.getReg r=t.regs r := by cases r <;> simp_all [MachineState.getReg]
      rw [←left,←right]
      exact regs r
  cases s
  cases t
  simp_all only [other,withMemoryOrigin,Prod.mk.injEq,MachineState.mk.injEq]

def loaderRegs (candidate : Submission) (p : Program) (input : Input candidate.sizes p) : Reg → Word
  | .x2 => BitVec.ofNat 64 (dataBase (candidate.image p))
  | .x10 => BitVec.ofNat 64 candidate.layout.message
  | .x11 => BitVec.ofNat 64 candidate.layout.commitment
  | .x12 => BitVec.ofNat 64 candidate.layout.trapdoor
  | .x13 => BitVec.ofNat 64 candidate.layout.indices
  | .x14 => BitVec.ofNat 64 candidate.layout.values
  | .x15 => BitVec.ofNat 64 candidate.layout.proof
  | .x16 => BitVec.ofNat 64 (inputCount p input)
  | .x17 => BitVec.ofNat 64 (inputProofLength candidate.sizes p input)
  | r => initialMachine.regs r

theorem initial_getReg (candidate : Submission) (p : Program) (input : Input candidate.sizes p) (r : Reg) :
    (candidate.initialState p input).getReg r=loaderRegs candidate p input r := by
  cases r <;> rfl

theorem initial_other (candidate : Submission) (p : Program) (input : Input candidate.sizes p) :
    other (candidate.initialState p input)=other initialMachine := rfl

theorem factor_getReg (s : MachineState) (pc : Word) (r : Reg) :
    ((execInstrBr s (.ADDI .x6 .x0 498)).setPC pc).getReg r=
      if r=.x6 then 498 else s.getReg r := by
  cases r <;> rfl

theorem factor_other (s : MachineState) (pc : Word) :
    other ((execInstrBr s (.ADDI .x6 .x0 498)).setPC pc)=other s := rfl

theorem assembly_getReg (input : CheckInput) (r : Reg) :
    (Assembly.submission.initialState .check input).getReg r=loaderRegs Assembly.submission .check input r :=
  initial_getReg Assembly.submission .check input r

theorem assembly_other (input : CheckInput) :
    other (Assembly.submission.initialState .check input)=other initialMachine :=
  initial_other Assembly.submission .check input


def sevenInput (input : CheckInput) : CheckInput :=
  { input with proof := ProofCodec.HeadStreamSeven.restore input.positions.card input.proof }

@[simp] theorem seven_positions (input : CheckInput) : (sevenInput input).positions=input.positions := rfl
@[simp] theorem seven_length (input : CheckInput) :
    (sevenInput input).proof.length=input.proof.length+input.positions.card/8 := by
  simp [sevenInput,ProofCodec.HeadStreamSeven.expandedLength]

def restoredInput (input : CheckInput) : CheckInput := zeroInput (sevenInput input)
@[simp] theorem restored_positions (input : CheckInput) : (restoredInput input).positions=input.positions := rfl
@[simp] theorem restored_length (input : CheckInput) :
    (restoredInput input).proof.length=input.proof.length+input.positions.card/8+input.positions.card := by
  simp [restoredInput]

def tailStart (input : CheckInput) : MachineState :=
  (execInstrBr (Assembly.submission.initialState .check input) (.ADDI .x6 .x0 498)).setPC (TailRestore.pcOf 0)

theorem tail_entry_hop (input : CheckInput) :
    Hop (Assembly.submission.initialState .check input) (tailStart input) 2 2 := by
  have first := hop_one (Assembly.submission.initialState .check input) 0 (.ADDI .x6 .x0 498)
    (by decide) rfl rfl (alu_ordinary _ _ rfl)
  have next := hop_one (execInstrBr (Assembly.submission.initialState .check input) (.ADDI .x6 .x0 498))
    1 (.JAL .x0 2500) (by decide) rfl rfl (branch_ordinary _ _ rfl)
  rw [jal0_exec] at next
  exact first.thenDo next

theorem seven_input_byte (input : CheckInput) (a : Word) :
    (if proofBase≤a.toNat ∧ a.toNat<proofBase+input.proof.length+input.positions.card/8
     then ProofCodec.HeadStreamSeven.expandedByte input.positions.card input.proof (a.toNat-proofBase) else (headStart input).getByte a)=
      inputByte Assembly.submission .check (sevenInput input) a.toNat := by
  by_cases inside : proofBase≤a.toNat ∧ a.toNat<proofBase+input.proof.length+input.positions.card/8
  · rw [if_pos inside,input_byte_high _ _ inside.1]
    change _=(List.ofFn (fun p : Fin (ProofCodec.HeadStreamSeven.expandedLength input.positions.card input.proof.length) =>
      ProofCodec.HeadStreamSeven.expandedByte input.positions.card input.proof p.val))[a.toNat-proofBase]?.getD 0
    have bound : a.toNat-proofBase<ProofCodec.HeadStreamSeven.expandedLength input.positions.card input.proof.length := by
      unfold ProofCodec.HeadStreamSeven.expandedLength
      omega
    rw [List.getElem?_ofFn,dif_pos bound,Option.getD_some]
  · rw [if_neg inside,head_start_byte]
    by_cases low : a.toNat<proofBase
    · exact (input_byte_low input _ _ low).symm
    · rw [input_byte_high _ _ (by omega),input_byte_high _ _ (by omega),
        List.getElem?_eq_none (by omega),List.getElem?_eq_none (by rw [seven_length];omega)]


structure TailStage (input : CheckInput) (s : MachineState) : Prop where
  pc : s.pc=pcOf 0
  length : s.getReg .x17=BitVec.ofNat 64 (sevenInput input).proof.length
  temps : ∀ r∈restoredTemps,s.getReg r=0
  low : ∀ r,r≠.x17 → r∉restoredTemps → s.getReg r=(headStart input).getReg r
  bytes : ∀ a,s.getByte a=inputByte Assembly.submission .check (sevenInput input) a.toNat
  metadata : other s=other (headStart input)
  unaligned : ∀ a,alignToDword a≠a → s.mem a=(headStart input).mem a

def tailSteps (k N : Nat) : Nat := 3+TailRestore.restoreSteps k (N+k/8)
def tailCycles (k N : Nat) : Nat := 3+TailRestore.restoreCycles k (N+k/8)

theorem tail_stage (input : CheckInput) (fits : input.proof.length≤8355061248)
    (capacity : input.proof.length+input.positions.card/8≤8355061248)
    (records : 480*input.positions.card ≤ input.proof.length+input.positions.card/8) :
    ∃ s,TailStage input s ∧ Hop (Assembly.submission.initialState .check input) s
      (tailSteps input.positions.card input.proof.length) (tailCycles input.positions.card input.proof.length) := by
  obtain ⟨t,pc,x17,temps,low,bytes,hop,reach⟩ := TailRestore.restore_run input.positions.card
    (input.proof.length+input.positions.card/8) proofBase input.proof (tailStart input)
    rfl (by rw [tailStart,factor_getReg,assembly_getReg];rfl)
    (by rw [tailStart,factor_getReg,assembly_getReg];rfl)
    (by rw [tailStart,factor_getReg,assembly_getReg];rfl)
    rfl (TwoPermutationPrototype.Checker.checker_positions_bound input)
    capacity records (by decide) (entry_source input) (entry_scratch_zero input fits)
  have jump := hop_one t 700 (.JAL .x0 2096544) (by decide) pc rfl (branch_ordinary _ _ rfl)
  rw [jal0_exec] at jump
  simp only [pc] at jump
  change Hop t (t.setPC (pcOf 0)) 1 1 at jump
  refine ⟨t.setPC (pcOf 0),⟨rfl,?_,temps,low,?_,reach.other_eq,reach.unaligned⟩,?_⟩
  · change t.getReg .x17=_
    simpa only [seven_length] using x17
  · intro a
    change t.getByte a=_
    rw [bytes]
    rw [show (tailStart input).getByte a=(headStart input).getByte a from rfl]
    simpa only [Nat.add_assoc] using seven_input_byte input a
  · exact ((tail_entry_hop input).thenDo (hop.thenDo jump)).cast (by unfold tailSteps;omega) (by unfold tailCycles;omega)

def entrySteps (k N : Nat) : Nat := tailSteps k N+restoreSteps k (N+k/8+k)
def entryCycles (k N : Nat) : Nat := tailCycles k N+restoreCycles k (N+k/8+k)

attribute [local irreducible] Submission.initialState

theorem restored_entry (input : CheckInput) (fits : input.proof.length≤8355061248)
    (capacity : input.proof.length+input.positions.card/8+input.positions.card≤8355061248)
    (records : 481*input.positions.card ≤ input.proof.length+input.positions.card/8+input.positions.card) :
    letI : UnpackOrigin := ⟨(headStart input).mem⟩
    Hop (Assembly.submission.initialState .check input) (unpackStart (restoredInput input))
      (entrySteps input.positions.card input.proof.length) (entryCycles input.positions.card input.proof.length) := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  obtain ⟨middle,stage,first⟩ := tail_stage input fits (by omega) (by omega)
  have canonical (a : Word) : middle.getByte a=(headStart (sevenInput input)).getByte a :=
    (stage.bytes a).trans (head_start_byte _ a).symm
  have source (j : Nat) (hj : j<2^34) :
      middle.getByte (BitVec.ofNat 64 (proofBase+j))=(sevenInput input).proof.getD j 0 := by
    rw [canonical]
    exact entry_source (sevenInput input) j hj
  have scratch (a : Word) (ha : proofBase+2^33≤a.toNat ∧ a.toNat<proofBase+2^33+input.positions.card) :
      middle.getByte a=0 := by
    rw [canonical]
    exact entry_scratch_zero (sevenInput input) (by rw [seven_length];omega) a ha
  obtain ⟨t,pc,x17,temps,low,bytes,hop,reach⟩ := restore_run input.positions.card
    (input.proof.length+input.positions.card/8+input.positions.card) proofBase (sevenInput input).proof middle
    stage.pc
    (by rw [stage.low .x15 (by decide) (by decide),headStart,factor_getReg,assembly_getReg];rfl)
    (by rw [stage.low .x16 (by decide) (by decide),headStart,factor_getReg,assembly_getReg];rfl)
    stage.length (by rw [seven_length]) (TwoPermutationPrototype.Checker.checker_positions_bound input)
    capacity records (by decide) source scratch
  have same : ∀ r,r≠.x17 → (headStart input).getReg r=
      ((execInstrBr (Assembly.submission.initialState .check (restoredInput input)) (.ADDI .x6 .x0 498)).setPC 6596).getReg r := by
    intro r hr
    rw [headStart,factor_getReg,factor_getReg,assembly_getReg,assembly_getReg]
    cases r <;> first | exact (hr rfl).elim | rfl
  have oldzero : ∀ r∈restoredTemps,
      ((execInstrBr (Assembly.submission.initialState .check (restoredInput input)) (.ADDI .x6 .x0 498)).setPC 6596).getReg r=0 := by
    intro r hr
    simp only [restoredTemps,List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [factor_getReg,assembly_getReg]
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have equal : t=unpackStart (restoredInput input) := by
    unfold unpackStart
    apply state_eq_origin
    · intro r
      by_cases h17 : r=.x17
      · subst r
        rw [x17,factor_getReg,assembly_getReg]
        change BitVec.ofNat 64 (input.proof.length+input.positions.card/8+input.positions.card)=
          BitVec.ofNat 64 (restoredInput input).proof.length
        rw [restored_length]
      · by_cases ht : r∈restoredTemps
        · exact (temps r ht).trans (oldzero r ht).symm
        · exact (low r h17 ht).trans ((stage.low r h17 ht).trans (same r h17))
    · exact pc
    · rw [factor_other,assembly_other]
      exact reach.other_eq.trans (stage.metadata.trans (by rw [headStart,factor_other,assembly_other]))
    · intro a
      have target :
          ((execInstrBr (Assembly.submission.initialState .check (restoredInput input)) (.ADDI .x6 .x0 498)).setPC 6596).getByte a=
            inputByte Assembly.submission .check (restoredInput input) a.toNat := by
        change (Assembly.submission.initialState .check (restoredInput input)).getByte a=_
        exact initial_byte _ _
      rw [target,bytes,canonical]
      simpa only [restoredInput,seven_positions,seven_length,Nat.add_assoc] using zero_input_byte (sevenInput input) a
    · intro a ha
      exact (reach.unaligned a ha).trans (stage.unaligned a ha)
  rw [equal] at hop
  exact first.thenDo hop

end TwoPermutationPrototype.Packed.Checker.HeadRestore
