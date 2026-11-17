import CommitGolfCandidate.NonceCompressedFetch
import CommitGolfCandidate.NonceCompressedAdmission

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def nonceOldOpeningImage : Image := capProgram.image .opening

def nonceIsEcall : Option Instruction → Bool
  | some (.base .ECALL) => true
  | _ => false

theorem nonce_old_opening_length : nonceOldOpeningImage.code.length=111 := by decide

theorem nonce_opening_ecall_table : ∀ index : Fin 111,
    nonceIsEcall ((nonceOldOpeningImage.code[index.val]?).bind decodeInstruction)=
      decide (index.val=110) := by decide

theorem nonce_opening_ecall_pc (state : MachineState)
    (fetched : fetch nonceOldOpeningImage state=some (.base .ECALL)) : state.pc=4536 := by
  have enabled : 4096 ≤ state.pc.toNat ∧ state.pc.toNat%4=0 := by
    by_contra invalid
    simp only [fetch, if_neg invalid] at fetched
    contradiction
  let index := (state.pc.toNat-4096)/4
  have decoded : (nonceOldOpeningImage.code[index]?).bind decodeInstruction=some (.base .ECALL) := by
    have equality := fetched
    simp only [fetch, if_pos enabled] at equality
    change (match nonceOldOpeningImage.code[index]? with
      | some word => decodeInstruction word | none => none)=some (.base .ECALL) at equality
    cases item : nonceOldOpeningImage.code[index]? <;>
      simpa only [item, Option.bind] using equality
  have bounded : index<111 := by
    by_contra outside
    have absent : nonceOldOpeningImage.code[index]?=none :=
      List.getElem?_eq_none (by rw [nonce_old_opening_length]; omega)
    simp only [absent, Option.bind_none] at decoded
    contradiction
  have only := nonce_opening_ecall_table ⟨index,bounded⟩
  rw [decoded] at only
  have last : index=110 := by simpa only [nonceIsEcall, decide_eq_true_eq] using only.symm
  have numeric : state.pc.toNat=4536 := by
    dsimp only [index] at last
    omega
  apply BitVec.eq_of_toNat_eq
  exact numeric

theorem nonce_opening_after_halt_fetch (state : MachineState) (pc : state.pc=4540) :
    fetch nonceOldOpeningImage state=none := by
  have absent : nonceOldOpeningImage.code[111]?=none :=
    List.getElem?_eq_none (by rw [nonce_old_opening_length])
  have numeric : state.pc.toNat=4540 := by rw [pc]; decide
  simp [fetch, numeric, absent]

theorem nonce_fetch_some_index (image : Image) (state : MachineState) (instruction : Instruction)
    (fetched : fetch image state=some instruction) :
    ∃ index, index < image.code.length ∧
      state.pc=BitVec.ofNat 64 (4096+4*index) ∧
      (image.code[index]?).bind decodeInstruction=some instruction := by
  have enabled : 4096 ≤ state.pc.toNat ∧ state.pc.toNat%4=0 := by
    by_contra invalid
    simp only [fetch, if_neg invalid] at fetched
    contradiction
  let index := (state.pc.toNat-4096)/4
  have decoded : (image.code[index]?).bind decodeInstruction=some instruction := by
    have equality:=fetched
    simp only [fetch, if_pos enabled] at equality
    change (match image.code[index]? with | some word => decodeInstruction word | none => none)=
      some instruction at equality
    cases item : image.code[index]? <;> simpa only [item, Option.bind] using equality
  have bounded : index < image.code.length := by
    by_contra outside
    have absent : image.code[index]?=none := List.getElem?_eq_none (by omega)
    simp only [absent, Option.bind_none] at decoded
    contradiction
  refine ⟨index,bounded,?_,decoded⟩
  have numeric : state.pc.toNat=4096+4*index := by dsimp only [index]; omega
  calc
    state.pc=BitVec.ofNat 64 state.pc.toNat := by simp
    _ = _ := by rw [numeric]

theorem nonce_opening_ordinary_fetch (state : MachineState) (instruction : Instruction)
    (fetched : fetch nonceOldOpeningImage state=some instruction)
    (ordinary : instruction≠.base .ECALL) :
    fetch nonceCompactImage state=some instruction := by
  obtain ⟨index,bounded,pc,decoded⟩:=nonce_fetch_some_index nonceOldOpeningImage state instruction fetched
  rw [nonce_old_opening_length] at bounded
  have notLast : index≠110 := by
    intro equal
    subst index
    have last : (nonceOldOpeningImage.code[110]?).bind decodeInstruction=some (.base .ECALL) := by rfl
    rw [last] at decoded
    exact ordinary (Option.some.inj decoded.symm)
  exact (nonce_compact_prefix_fetch state index (by omega) pc).trans fetched

theorem nonce_opening_halt_replacement (state : MachineState) (pc : state.pc=4536)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (1+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (state.setPC 4540) coins
          return result.charge 1 0) := by
  have fetched : fetch nonceCompactImage state=some (.base (.JAL .x0 4)) := by
    apply cap_image_fetch _ state 110 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 4))=some (state.setPC 4540) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, signExtend21,
      MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end CommitGolfCandidate
