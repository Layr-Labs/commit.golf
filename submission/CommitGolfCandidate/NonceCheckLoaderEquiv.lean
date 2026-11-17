import CommitGolfCandidate.NonceActualExpandMemory
import CommitGolfCandidate.NonceExpandLoaderMemory
import CommitGolfCandidate.NonceLoadedProof
import CommitGolfCandidate.NonceExpandedLoaderFrame

/-! Observational equivalence of the real expansion endpoint and the old
checker initialized with the expanded adversarial proof. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

abbrev nonceCheckExpansionStart (input : CheckInput) : MachineState :=
  (capProgram.initialState .check input).setPC 4896

abbrev nonceCheckExpansionEnd (input : CheckInput) : MachineState :=
  nonceExpandCoreState (nonceCheckExpansionStart input) input.positions.card input.proof.length

theorem nonce_check_loader_equiv (input : CheckInput)
    (aligned : input.proof.length%8=0)
    (enough : 536*input.positions.card ≤ input.proof.length)
    (admitted : (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof) :
    NonceStateEquiv (nonceOldCheckTailState (nonceExpandedInput input)) (nonceCheckExpansionEnd input) := by
  let base:=capProgram.layout.proof
  let count:=input.positions.card
  let length:=input.proof.length
  let words:=nonceExpandFooterWords count length
  have baseStart : 8 ≤ base := by decide
  have baseAligned : base%8=0 := by decide
  have cardinal : count ≤ LENGTH := by simpa [count,Index] using Finset.card_le_univ input.positions
  have countSmall : count<2^64 := by norm_num [LENGTH,LOG_LENGTH] at cardinal; omega
  have lengthEq : length=536*count+8*words := by dsimp only [length,count,words,nonceExpandFooterWords]; omega
  have expandedLength:=nonce_expanded_input_length input enough
  have capacity : length+8*count ≤ 13421772800 := by
    have limit : capProgram.sizes.proof=13421772800 := by rfl
    rw [expandedLength,limit] at admitted
    exact admitted
  have window : base+length+8*count ≤ MEMORY_BYTES := by
    have loader:=(cap_check_loader_bounds (nonceExpandedInput input) admitted).1
    rw [expandedLength] at loader
    dsimp only [base,count,length]
    omega
  have facts:=nonce_expand_setup_facts (nonceCheckExpansionStart input) base count length rfl
    baseStart aligned enough capacity rfl rfl rfl
  have ready:=nonce_expand_record_entry_ready (nonceCheckExpansionStart input) base count length facts
    baseStart countSmall baseAligned aligned enough window
  have finished:=nonce_expand_outer_finished base count count _ ready
  have effect:=nonce_expand_complete_memory (nonceCheckExpansionStart input) base count length rfl
    baseStart countSmall baseAligned aligned enough capacity window rfl rfl rfl
  have originalEffect : NonceFullExpandMemory base count words (capProgram.initialState .check input)
      (nonceCheckExpansionEnd input) := by
    constructor
    · intro index inside
      exact effect.copied index inside
    · intro location outside
      exact effect.frame location outside
  refine ⟨?_,?_,?_⟩
  · change (4100:Word)=(nonceExpandFinishPrefix _ 12).pc
    exact (nonce_expand_finish_pc _ finished.1).symm
  · intro reg
    exact (nonce_expand_initial_registers input base count length facts rfl rfl enough reg).symm
  · intro location locationAligned
    change (capProgram.initialState .check (nonceExpandedInput input)).getMem location=_
    apply nonce_expand_loader_memory base count words (capProgram.initialState .check input)
      (nonceCheckExpansionEnd input) (capProgram.initialState .check (nonceExpandedInput input))
      baseAligned (by norm_num [MEMORY_BYTES] at window; omega) originalEffect
    · exact nonce_loaded_expanded_proof input words lengthEq admitted
    · intro address addressBound addressAligned outside
      have lengthExpanded : (nonceExpandedInput input).proof.length=544*count+8*words := by omega
      apply nonce_expanded_loader_frame input aligned enough address addressAligned addressBound
      simpa only [lengthExpanded,base,Nat.add_assoc] using outside
    · exact locationAligned
end CommitGolfCandidate
