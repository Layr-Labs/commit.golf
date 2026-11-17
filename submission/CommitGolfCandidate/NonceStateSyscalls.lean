import CommitGolfCandidate.NonceStateEquiv

namespace CommitGolfCandidate.NonceStateEquiv
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem set_bytes (indices : List Nat) (address : Nat → Word) (value : Nat → Byte)
    (left right : MachineState) (related : NonceStateEquiv left right) :
    NonceStateEquiv (indices.foldl (fun state index => state.setByte (address index) (value index)) left)
      (indices.foldl (fun state index => state.setByte (address index) (value index)) right) := by
  induction indices generalizing left right with
  | nil => exact related
  | cons index indices ih =>
    exact ih _ _ (set_byte left right related (address index) (value index))

theorem write_bits {bits : Nat} (left right : MachineState) (related : NonceStateEquiv left right)
    (address : Word) (answer : BitVec bits) :
    NonceStateEquiv (writeBits left address answer) (writeBits right address answer) := by
  have bytes:=set_bytes (List.range ((bits+7)/8)) (fun index => address+BitVec.ofNat 64 index)
    (fun index => BitVec.ofNat 8 (answer.toNat/2^(8*index))) left right related
  have finished:=set_pc _ _ bytes (right.pc+4)
  simpa only [writeBits,related.pc] using finished

private def oracleInputView (registers : Reg → Word) (reader : Nat → Nat → Nat) : Option PublicSpec.Domain := do
  let kind := (registers .x13).toNat
  let source := registers .x10
  let destination := registers .x12
  let inputBits := if kind = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH
  let outputBits := if kind = 0 then COMPRESSION_OUTPUT_LENGTH else PERMUTATION_WIDTH
  let inputBytes := (inputBits + 7) / 8
  let outputBytes := (outputBits + 7) / 8
  if kind ≤ 2 ∧ (registers .x11).toNat = inputBytes ∧ source.toNat % 8 = 0 ∧
      destination.toNat % 8 = 0 ∧ rangeValid source inputBytes = true ∧
      rangeValid destination outputBytes = true then
    let input := reader source.toNat inputBytes
    match kind with
    | 0 => return .inl (BitVec.ofNat COMPRESSION_INPUT_LENGTH input)
    | 1 => return .inr (.inl (BitVec.ofNat PERMUTATION_WIDTH input))
    | _ => return .inr (.inr (BitVec.ofNat PERMUTATION_WIDTH input))
  else none

theorem oracle_input (left right : MachineState) (related : NonceStateEquiv left right) :
    oracleInput left=oracleInput right := by
  change oracleInputView left.getReg (fun address count => (readBuffer left address count).toNat)=
    oracleInputView right.getReg (fun address count => (readBuffer right address count).toNat)
  apply congrArg₂ oracleInputView
  · exact funext related.registers
  · funext address count
    rw [read_buffer left right related]

theorem oracle_answer (left right : MachineState) (related : NonceStateEquiv left right)
    (address : Word) (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    NonceStateEquiv (writeOracleAnswer left address query answer)
      (writeOracleAnswer right address query answer) := by
  cases query with
  | inl input => exact write_bits left right related address answer
  | inr query => cases query <;> exact write_bits left right related address answer

end CommitGolfCandidate.NonceStateEquiv
