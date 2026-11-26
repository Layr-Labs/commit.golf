import CommitGolfCandidate.ChainedInverseFooterMemory

/-! Entry branch, zero-count nonaccess and composition for the actual footer component. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] execute

def inverseFooterEntryState (s : MachineState) : MachineState := execInstrBr s (.BEQ .x22 .x0 492)

theorem inverse_footer_entry_register (s : MachineState) (reg : Reg) :
    (inverseFooterEntryState s).getReg reg=s.getReg reg := by
  by_cases empty : s.getReg .x22==0#64
  · have same : inverseFooterEntryState s=s.setPC (s.pc+signExtend13 492) := ite_eq_left empty
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : inverseFooterEntryState s=s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC

theorem inverse_footer_entry_memory (s : MachineState) (query : Word) :
    (inverseFooterEntryState s).getMem query=s.getMem query := by
  by_cases empty : s.getReg .x22==0#64
  · have same : inverseFooterEntryState s=s.setPC (s.pc+signExtend13 492) := ite_eq_left empty
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : inverseFooterEntryState s=s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC

theorem inverse_footer_entry_byte (s : MachineState) (query : Word) :
    (inverseFooterEntryState s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,inverse_footer_entry_memory]

theorem inverse_footer_entry_pc (s : MachineState) (n : Nat)
    (count : s.getReg .x22=BitVec.ofNat 64 n) (fit : n<2^64) :
    (inverseFooterEntryState s).pc=if n=0 then s.pc+492 else s.pc+4 := by
  by_cases empty : n=0
  · subst n
    have same : inverseFooterEntryState s=s.setPC (s.pc+signExtend13 492) :=
      ite_eq_left (by rw [count]; rfl)
    have projected := inverse_footer_project_pc s _ _ same
    have offset : signExtend13 (492 : BitVec 13)=(492 : Word) := by rfl
    exact projected.trans (congrArg (fun address : Word => s.pc+address) offset)
  · have nonzero : s.getReg .x22≠0#64 := by
      intro equal
      have number := congrArg BitVec.toNat equal
      rw [count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at number
      exact empty number
    have same : inverseFooterEntryState s=s.setPC (s.pc+4) :=
      ite_eq_right (by simpa [MachineState.getReg] using nonzero)
    have projected := inverse_footer_project_pc s _ _ same
    simpa only [ite_eq_right empty] using projected

theorem inverse_footer_entry_execution (image : Image) (base : Word)
    (code : OpsAt image base inverseFooterOps) (s : MachineState) (pc : s.pc=base)
    (fuel : Nat) (coins : Bool) :
    execute image (1+fuel) s coins=
      (do let result ← execute image fuel (inverseFooterEntryState s) coins
          return result.charge 1 0) := by
  have fetched : fetch image s=some (.base (.BEQ .x22 .x0 492)) :=
    code 0 (by decide) s (by simpa using pc)
  rw [show 1+fuel=fuel+1 by omega]
  exact execute_ordinary_step image _ _ _ fuel coins fetched (by rfl)

theorem inverse_footer_empty_execution (image : Image) (base : Word)
    (code : OpsAt image base inverseFooterOps) (s : MachineState) (pc : s.pc=base)
    (count : s.getReg .x22=0#64) (fuel : Nat) (coins : Bool) :
    execute image (1+fuel) s coins=
      (do let result ← execute image fuel (s.setPC (s.pc+signExtend13 492)) coins
          return result.charge 1 0) := by
  have same : inverseFooterEntryState s=s.setPC (s.pc+signExtend13 492) :=
    ite_eq_left (by rw [count]; rfl)
  rw [inverse_footer_entry_execution image base code s pc,same]

theorem inverse_footer_execution (image : Image) (base : Word) (code : OpsAt image base inverseFooterOps)
    (n : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady n s source output metadata) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (1+122*n+fuel) s coins=
      (do let result ← execute image fuel (inverseFooterRowsState n (inverseFooterEntryState s)) coins
          return result.charge (1+122*n) 0) := by
  have memoryBound : MEMORY_BYTES≤2^64 := by decide
  have fit : n<2^64 := by have := ready.metaRoom; omega
  have nextPC : (inverseFooterEntryState s).pc=if n=0 then base+492 else base+4 := by
    rw [inverse_footer_entry_pc s n ready.count fit,pc]
  have next : InverseFooterReady n (inverseFooterEntryState s) source output metadata := by
    refine ⟨?_,?_,?_,?_,?_,ready.sourceRoom,ready.outputRoom,ready.metaRoom⟩
    · rw [inverse_footer_entry_register]; exact ready.sourcePointer
    · rw [inverse_footer_entry_register]; exact ready.outputPointer
    · rw [inverse_footer_entry_register]; exact ready.metaPointer
    · rw [inverse_footer_entry_register]; exact ready.skip
    · rw [inverse_footer_entry_register]; exact ready.count
  rw [show 1+122*n+fuel=1+(122*n+fuel) by omega,
    inverse_footer_entry_execution image base code s pc,
    inverse_footer_rows_execution image base code n _ source output metadata next nextPC]
  simp [Execution.charge,Nat.add_assoc]

theorem inverse_footer_memory (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady fields suffix completed s source outputBase metadata)
    (lows : ∀ field ∈ fields, field.low.length=29)
    (padding : ∀ field ∈ fields, field.padding=[])
    (skip : s.getReg .x9=1#64) :
    InverseFieldsReady [] suffix (completed++rawFieldsBytes fields)
      (inverseFooterRowsState fields.length (inverseFooterEntryState s)) (source+(rawFieldsLow fields).length)
      outputBase (metadata+2*fields.length) := by
  have next := inverse_fields_ready_congr fields suffix completed s (inverseFooterEntryState s)
    source outputBase metadata ready (inverse_footer_entry_byte s)
    (inverse_footer_entry_register s .x5) (inverse_footer_entry_register s .x6)
    (inverse_footer_entry_register s .x7)
  exact inverse_footer_rows_memory fields suffix completed _ source outputBase metadata next lows padding
    ((inverse_footer_entry_register s .x9).trans skip)

end CommitGolfCandidate.Chained.Native
