import CommitGolfCandidate.CapCheckRecordOutcome
import CommitGolfCandidate.CapCheckRecordFrame
import CommitGolfCandidate.CapCheckRecordAdmission

/-! Natural ABI geometry for the outer checker loop. The high-byte frame
keeps the next sorted index available after every arbitrary-reply record.
Workspace root consistency is a separate semantic invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

structure CapCheckRecordsReady (input : CheckInput) (ordinal remaining : Nat)
    (state : MachineState) : Prop where
  partition : ordinal+remaining=input.positions.card
  pc : state.pc=if remaining=0 then 4548 else 4212
  indices : state.getReg .x24=BitVec.ofNat 64 (capProgram.layout.indices+8*ordinal)
  values : state.getReg .x8=BitVec.ofNat 64 (capProgram.layout.values+256*ordinal)
  proof : state.getReg .x25=BitVec.ofNat 64 (capProgram.layout.proof+576*ordinal)
  counter : state.getReg .x27=BitVec.ofNat 64 remaining
  endPointer : state.getReg .x22=
    BitVec.ofNat 64 (capProgram.layout.proof+input.proof.length)
  commitment : state.getReg .x26=BitVec.ofNat 64 capProgram.layout.commitment
  scratch : state.getReg .x21=256
  marks : state.getReg .x9=28672
  roots : state.getReg .x18=12288
  leaves : state.getReg .x19=256
  one : state.getReg .x31=1
  inputs : CapHighBytes state (capProgram.initialState .check input)

theorem cap_check_records_ready_index (input : CheckInput) (ordinal remaining : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal remaining state)
    (positive : 0<remaining) :
    ∃ index < 2^24, state.getMem (state.getReg .x24)=BitVec.ofNat 64 index := by
  have present : ordinal < input.positions.card := by have := ready.partition; omega
  let position := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)
  refine ⟨position.val,position.isLt,?_⟩
  rw [ready.indices]
  exact cap_check_retained_index input state ordinal present ready.inputs

theorem cap_check_records_ready_next (input : CheckInput) (ordinal remaining : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal (remaining+1) state)
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2=true) :
    CapCheckRecordsReady input (ordinal+1) remaining result.1 := by
  obtain ⟨index,bounded,loaded⟩ :=
    cap_check_records_ready_index input ordinal (remaining+1) state ready (by omega)
  have cardinal : input.positions.card≤LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : remaining+1<2^64 := by
    have partition := ready.partition
    norm_num [LENGTH,LOG_LENGTH] at cardinal
    omega
  have cursors := cap_check_record_run_cursors state result reachable passed
  have control := cap_check_record_run_control state result (remaining+1) (by omega)
    small ready.counter reachable passed
  have registers (reg : Reg)
      (outside : reg ∉ [.x20,.x6,.x7,.x25,.x1,.x28,.x29,.x5,
        .x8,.x10,.x11,.x12,.x13,.x30,.x23,.x24,.x27]) :=
    cap_check_record_run_register state result reachable passed reg outside
  refine ⟨by have := ready.partition; omega,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [control.2]
    by_cases zero : remaining = 0
    · simp only [zero,Nat.zero_add,ite_true]
    · simp only [show remaining+1 ≠ 1 by omega,zero,ite_false]
  · rw [cursors.2.2,ready.indices,
      show (8 : Word)=BitVec.ofNat 64 8 by rfl,← BitVec.ofNat_add]
    congr 1
  · rw [cursors.1,ready.values,
      show (256 : Word)=BitVec.ofNat 64 256 by rfl,← BitVec.ofNat_add]
    congr 1
  · rw [cursors.2.1,ready.proof,
      show (576 : Word)=BitVec.ofNat 64 576 by rfl,← BitVec.ofNat_add]
    congr 1
  · simpa only [Nat.add_sub_cancel] using control.1
  · exact (registers .x22 (by decide)).trans ready.endPointer
  · exact (registers .x26 (by decide)).trans ready.commitment
  · exact (registers .x21 (by decide)).trans ready.scratch
  · exact (registers .x9 (by decide)).trans ready.marks
  · exact (registers .x18 (by decide)).trans ready.roots
  · exact (registers .x19 (by decide)).trans ready.leaves
  · exact (registers .x31 (by decide)).trans ready.one
  · exact cap_check_record_run_high_frame state _ index bounded loaded ready.scratch
      ready.leaves ready.marks ready.roots ready.one ready.inputs result reachable

theorem cap_check_records_ready_initial (input : CheckInput)
    (nonempty : 0 < input.positions.card) :
    CapCheckRecordsReady input 0 input.positions.card
      (capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input))) := by
  let initial := capProgram.initialState .check input
  have pointers := cap_check_initial_pointers input
  have constants := cap_check_constants_registers
    ((capCheckLengthState initial).setPC 4144)
  have memory :
      (capCheckRecordEntry (capCheckLengthState initial)).mem=initial.mem :=
    (cap_check_record_entry_memory _).trans (cap_check_length_memory _)
  refine ⟨by omega,?_,?_,?_,?_,pointers.2.2.2.2.1,pointers.2.2.2.2.2,
    pointers.1,constants.1,constants.2.1,constants.2.2.1,
    constants.2.2.2.1,constants.2.2.2.2,?_⟩
  · rw [cap_check_record_entry_pc,if_neg (by omega)]
  · simpa only [Nat.mul_zero,Nat.add_zero] using pointers.2.1
  · simpa only [Nat.mul_zero,Nat.add_zero] using pointers.2.2.1
  · simpa only [Nat.mul_zero,Nat.add_zero] using pointers.2.2.2.1
  · exact cap_high_bytes_memory initial _ initial memory (cap_high_bytes_refl initial)

end CommitGolfCandidate
