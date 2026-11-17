import CommitGolfCandidate.CapMarkImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def capCopySource (checking : Bool) : Reg := if checking then .x25 else .x23
def capCopyDestination (checking : Bool) : Reg := if checking then .x23 else .x25

def capDigestCopyInstructions (checking : Bool) : List Instr :=
  [.LD .x6 (capCopySource checking) 0, .SD (capCopyDestination checking) .x6 0,
   .LD .x6 (capCopySource checking) 8, .SD (capCopyDestination checking) .x6 8,
   .LD .x6 (capCopySource checking) 16, .SD (capCopyDestination checking) .x6 16,
   .LD .x6 (capCopySource checking) 24, .SD (capCopyDestination checking) .x6 24]

def capDigestCopyPrefix (checking : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((capDigestCopyInstructions checking).take count).foldl execInstrBr state

def CapDigestCopyFetched (image : Image) (checking : Bool) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 8, state.pc = entry →
    fetch image (capDigestCopyPrefix checking state i) =
      some (.base (((capDigestCopyInstructions checking)[i]?).getD .EBREAK))

private theorem store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem cap_copy_prefix_succ (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count < 8) :
    capDigestCopyPrefix checking state (count + 1) =
      execInstrBr (capDigestCopyPrefix checking state count)
        (((capDigestCopyInstructions checking)[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_copy_prefix_register (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (outside : reg ≠ .x6) :
    (capDigestCopyPrefix checking state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capDigestCopyPrefix, capDigestCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, store_register,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_copy_prefix_pc (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) :
    (capDigestCopyPrefix checking state count).pc =
      state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capDigestCopyPrefix, capDigestCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_digest_copy_execute (image : Image) (checking : Bool) (entry : Word)
    (fetched : CapDigestCopyFetched image checking entry)
    (state : MachineState) (pc : state.pc = entry)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (capCopySource checking) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg (capCopyDestination checking) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (8 + fuel) state allowCoins =
      (do let result ← execute image fuel (capDigestCopyPrefix checking state 8) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := capDigestCopyPrefix checking state)
  intro i bounded
  refine ⟨.base (((capDigestCopyInstructions checking)[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · have source := cap_copy_prefix_register checking state i (by omega)
      (capCopySource checking) (by cases checking <;> decide)
    have destination := cap_copy_prefix_register checking state i (by omega)
      (capCopyDestination checking) (by cases checking <;> decide)
    have valid : memoryArgumentsValid (capDigestCopyPrefix checking state i)
        (((capDigestCopyInstructions checking)[i]?).getD .EBREAK) = true := by
      have s0 := sourceValid ⟨0, by decide⟩
      have s1 := sourceValid ⟨1, by decide⟩
      have s2 := sourceValid ⟨2, by decide⟩
      have s3 := sourceValid ⟨3, by decide⟩
      have d0 := destinationValid ⟨0, by decide⟩
      have d1 := destinationValid ⟨1, by decide⟩
      have d2 := destinationValid ⟨2, by decide⟩
      have d3 := destinationValid ⟨3, by decide⟩
      interval_cases i <;>
        simp only [capDigestCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    rw [cap_copy_prefix_succ checking state i bounded]
    interval_cases i <;>
      simp only [capDigestCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte]
  · interval_cases i <;> rfl

theorem cap_open_boundary_copy_fetched :
    CapDigestCopyFetched ((capExperimental 24).image .opening) false 4460 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capDigestCopyPrefix false state i) (91 + i) _ (by omega)
  · rw [cap_copy_prefix_pc false state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_boundary_copy_fetched :
    CapDigestCopyFetched ((capExperimental 24).image .check) true 4652 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capDigestCopyPrefix true state i) (139 + i) _ (by omega)
  · rw [cap_copy_prefix_pc true state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
