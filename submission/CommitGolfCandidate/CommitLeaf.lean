import CommitGolfCandidate.Check
import CommitGolfCandidate.HoistHelpers

/-! Execution of the commitment image's leaf subroutine. The actual instruction
addresses and return address differ from the checker; the scratch transform is the
same. Every oracle reply is covered by the execution and resource proofs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096

theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 200) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .commit).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

private theorem pointer_commit_code : (submission.image .commit).code =
  [0x00050413#32, 0x00058d13#32, 0x00060493#32, 0x010009b7#32, 0x0180006f#32, 0x00000013#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x40000337#32, 0x0180006f#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00648933#32,
   0x20000337#32, 0x0180006f#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32,
   0x00000013#32, 0x00648bb3#32, 0x00200293#32, 0x00090513#32, 0x200005b7#32, 0x0180006f#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000073#32,
   0x00000a93#32, 0x00ba9a93#32, 0x100a8a93#32, 0x00000a13#32, 0x00000293#32, 0x000a8513#32,
   0x04000593#32, 0x000a8613#32, 0x00000693#32, 0x00000e13#32, 0x00093303#32, 0x006ab023#32,
   0x00893303#32, 0x006ab423#32, 0x01093303#32, 0x006ab823#32, 0x01893303#32, 0x006abc23#32,
   0x090000ef#32, 0x000ab303#32, 0x006bb023#32, 0x008ab303#32, 0x006bb423#32, 0x010ab303#32,
   0x006bb823#32, 0x018ab303#32, 0x006bbc23#32, 0x02090913#32, 0x020b8b93#32, 0x001a0a13#32,
   0xfb3a68e3#32, 0x00c0006f#32, 0x04000593#32, 0x00000693#32, 0xfff98a13#32, 0x020a0063#32,
   0x006a1313#32, 0x00648533#32, 0x005a1393#32, 0x00748633#32, 0x00000073#32, 0xfffa0a13#32,
   0xfe0a14e3#32, 0x0204b303#32, 0x006d3023#32, 0x0284b303#32, 0x006d3423#32, 0x0304b303#32,
   0x006d3823#32, 0x0384b303#32, 0x006d3c23#32, 0x00100293#32, 0x00000513#32, 0x00000073#32,
   0x00043303#32, 0x026ab023#32, 0x00843303#32, 0x026ab423#32, 0x01043303#32, 0x026ab823#32,
   0x01843303#32, 0x026abc23#32, 0x00000073#32, 0x02043303#32, 0x026ab023#32, 0x02843303#32,
   0x026ab423#32, 0x03043303#32, 0x026ab823#32, 0x03843303#32, 0x026abc23#32, 0x00000073#32,
   0x04043303#32, 0x026ab023#32, 0x04843303#32, 0x026ab423#32, 0x05043303#32, 0x026ab823#32,
   0x05843303#32, 0x026abc23#32, 0x00000073#32, 0x06043303#32, 0x026ab023#32, 0x06843303#32,
   0x026ab423#32, 0x07043303#32, 0x026ab823#32, 0x07843303#32, 0x026abc23#32, 0x00000073#32,
   0x08043303#32, 0x026ab023#32, 0x08843303#32, 0x026ab423#32, 0x09043303#32, 0x026ab823#32,
   0x09843303#32, 0x026abc23#32, 0x00000073#32, 0x0a043303#32, 0x026ab023#32, 0x0a843303#32,
   0x026ab423#32, 0x0b043303#32, 0x026ab823#32, 0x0b843303#32, 0x026abc23#32, 0x00000073#32,
   0x0c043303#32, 0x026ab023#32, 0x0c843303#32, 0x026ab423#32, 0x0d043303#32, 0x026ab823#32,
   0x0d843303#32, 0x026abc23#32, 0x00000073#32, 0x0e043303#32, 0x026ab023#32, 0x0e843303#32,
   0x026ab423#32, 0x0f043303#32, 0x026ab823#32, 0x0f843303#32, 0x026abc23#32, 0x00000073#32,
   0x10040413#32, 0x00008067#32] := by rfl

private def commitCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def commitCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitCompressionInstructions.take count).foldl execInstrBr state

/-- The fixed syscall arguments remain live through every block. -/
def CommitLeafOracleReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x10 = 256 ∧ state.getReg .x11 = 64 ∧
    state.getReg .x12 = 256 ∧ state.getReg .x13 = 0

/-- Reference initialization for the eight-block leaf. The image establishes these
fixed arguments once before the outer loop; the entry bridge proves their equality. -/
def commitLeafReadyState (state : MachineState) : MachineState :=
  commitCompressionPrefix ((state.setReg .x28 8).setPC 4436) 5

@[simp] theorem commit_leaf_ready_register (state : MachineState) (reg : Reg)
    (preserved : reg ∉ [.x5,.x10,.x11,.x12,.x13,.x28]) :
    (commitLeafReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitLeafReadyState, commitCompressionPrefix,
    commitCompressionInstructions, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]

@[simp] theorem commit_leaf_ready_pc (state : MachineState) :
    (commitLeafReadyState state).pc = 4456 := by
  simp [commitLeafReadyState, commitCompressionPrefix, commitCompressionInstructions,
    execInstrBr, MachineState.setPC]

@[simp] theorem commit_leaf_ready_counter (state : MachineState) :
    (commitLeafReadyState state).getReg .x28 = 8 := rfl

@[simp] theorem commit_leaf_ready_oracle (state : MachineState)
    (scratch : state.getReg .x21 = 256) :
    CommitLeafOracleReady (commitLeafReadyState state) := by
  have r21 : state.regs .x21 = 256 := scratch
  simp [commitLeafReadyState, CommitLeafOracleReady, commitCompressionPrefix,
    commitCompressionInstructions, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, r21]

private theorem commit_compression_prefix_ready (state : MachineState)
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state) :
    commitCompressionPrefix state 5 = state.setPC (state.pc + 20) := by
  cases state with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    dsimp [CommitLeafOracleReady, MachineState.getReg] at ready scratch
    dsimp [commitCompressionPrefix, commitCompressionInstructions, List.take,
      List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    simp only [Bool.false_eq_true, reduceIte, BitVec.zero_add, BitVec.add_zero]
    congr 1
    · funext reg
      cases reg <;> simp_all
    · simp [BitVec.add_assoc]

/-- State after the compression reply overwrites the low half of scratch memory. -/
def commitCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (commitCompressionPrefix state 5) 256 answer

/-- With hoisted arguments the block executes only the eight-cycle syscall. -/
theorem commit_compression (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4488 + 36*block))
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state 256 64)))
          let result ← execute (submission.image .commit) fuel
            ((commitCompressionState state answer).setPC (state.pc + 4)) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ (98+9*block) _ (by omega)
    · rw [pc]; congr 1 <;> omega
    · rw [pointer_commit_code]
      interval_cases block <;> rfl
  rcases ready with ⟨r5,r10,r11,r12,r13⟩
  have input : oracleInput state = some (.inl (readBuffer state 256 64)) := by
    have kind : (state.getReg .x13).toNat = 0 := by rw [r13]; rfl
    unfold oracleInput
    simp only [kind]
    simp [r10,r11,r12, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      rangeValid, MEMORY_BYTES]
    exact hoist_read_width state 256 _ kind
  have normalized (answer : BitVec 256) :
      (commitCompressionState state answer).setPC (state.pc + 4) = writeBits state 256 answer := by
    rw [commitCompressionState, commit_compression_prefix_ready state scratch
      ⟨r5,r10,r11,r12,r13⟩, hoist_write_bits_pc]
    rw [hoist_pc_pc]
    have outputpc : (writeBits state 256 answer).pc = state.pc + 4 := rfl
    rw [← outputpc, hoist_pc_self]
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos r5, input]
  simp only [writeOracleAnswer, r12]
  simp only [oracleCycles, COMPRESSION_CYCLES]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [normalized answer]
  rfl

/-- Five setup instructions and the reply write advance to the next instruction. -/
theorem commit_compression_pc (state : MachineState) (answer : BitVec 256) :
    (commitCompressionState state answer).pc = state.pc + 24 := by
  simp [commitCompressionState, writeBits, commitCompressionPrefix, commitCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

/-- Compression preserves the loop counters, pointers, and return address. Only
syscall argument registers are overwritten by its five-instruction setup. -/
theorem commit_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
    (commitCompressionState state answer).getReg reg = state.getReg reg := by
  rw [commitCompressionState, writeBits_register]
  simp only [commitCompressionPrefix, commitCompressionInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13)]

private def commitLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56]

private def commitLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLeafCopyInstructions.take count).foldl execInstrBr state

def commitLeafCopyState (state : MachineState) : MachineState := commitLeafCopyPrefix state 8

theorem pointer_write {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (value : Word) :
    writeBits (state.setReg .x8 value) address answer =
      (writeBits state address answer).setReg .x8 value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg .x8 value).setByte a b = (s.setByte a b).setReg .x8 value := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg .x8 value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg .x8 value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons,byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl

theorem pointer_compression (state : MachineState) (value : Word) (answer : BitVec 256) :
    commitCompressionState (state.setReg .x8 value) answer =
      (commitCompressionState state answer).setReg .x8 value := by
  have argsShift : commitCompressionInstructions.foldl execInstrBr (state.setReg .x8 value) =
      (commitCompressionInstructions.foldl execInstrBr state).setReg .x8 value := by
    cases state
    dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
      MachineState.setReg,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  change writeBits (commitCompressionInstructions.foldl execInstrBr (state.setReg .x8 value)) 256 answer =
    (writeBits (commitCompressionInstructions.foldl execInstrBr state) 256 answer).setReg .x8 value
  rw [argsShift,pointer_write]

/-- The unrolled body can load at a fixed offset from one unchanged source base. -/
def pointerCopyOps (block : Nat) : List Instr :=
  [.LD .x6 .x8 (BitVec.ofNat 12 (32*block)), .SD .x21 .x6 32,
   .LD .x6 .x8 (BitVec.ofNat 12 (32*block+8)), .SD .x21 .x6 40,
   .LD .x6 .x8 (BitVec.ofNat 12 (32*block+16)), .SD .x21 .x6 48,
   .LD .x6 .x8 (BitVec.ofNat 12 (32*block+24)), .SD .x21 .x6 56]

def pointerCopyState (state : MachineState) (block : Nat) : MachineState :=
  (pointerCopyOps block).foldl execInstrBr state

theorem pointer_load_frame (state : MachineState) (baseOffset loadOffset : BitVec 12)
    (totalOffset : BitVec 12)
    (address : signExtend12 totalOffset = signExtend12 baseOffset + signExtend12 loadOffset) :
    (execInstrBr state (.LD .x6 .x8 totalOffset)).setReg .x8
      (state.getReg .x8 + signExtend12 baseOffset) =
      execInstrBr (state.setReg .x8 (state.getReg .x8 + signExtend12 baseOffset))
        (.LD .x6 .x8 loadOffset) := by
  have memory (value a : Word) : (state.setReg .x8 value).getMem a = state.getMem a := rfl
  have pc (value : Word) : (state.setReg .x8 value).pc = state.pc := rfl
  simp only [execInstrBr,MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    memory,pc,address,BitVec.add_assoc]
  cases state
  dsimp [MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem pointer_store_frame (state : MachineState) (value : Word) (offset : BitVec 12) :
    (execInstrBr state (.SD .x21 .x6 offset)).setReg .x8 value =
      execInstrBr (state.setReg .x8 value) (.SD .x21 .x6 offset) := by
  simp only [execInstrBr,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x6)]
  cases state
  rfl
private def PointerRelated (base advance : Word) (actual reference : MachineState) : Prop :=
  actual.getReg .x8 = base ∧ actual.setReg .x8 advance = reference

private theorem pointer_load_related (base advance : Word) (actual reference : MachineState)
    (related : PointerRelated base advance actual reference)
    (baseOffset loadOffset totalOffset : BitVec 12)
    (advanceEq : advance = base + signExtend12 baseOffset)
    (address : signExtend12 totalOffset = signExtend12 baseOffset + signExtend12 loadOffset) :
    PointerRelated base advance (execInstrBr actual (.LD .x6 .x8 totalOffset))
      (execInstrBr reference (.LD .x6 .x8 loadOffset)) := by
  constructor
  · simpa only [execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x8)] using related.1
  · rw [← related.2]
    have result := pointer_load_frame actual baseOffset loadOffset totalOffset address
    simpa only [related.1,← advanceEq] using result

private theorem pointer_store_related (base advance : Word) (actual reference : MachineState)
    (related : PointerRelated base advance actual reference) (offset : BitVec 12) :
    PointerRelated base advance (execInstrBr actual (.SD .x21 .x6 offset))
      (execInstrBr reference (.SD .x21 .x6 offset)) := by
  constructor
  · change actual.getReg .x8 = base
    exact related.1
  · rw [← related.2]
    exact pointer_store_frame actual advance offset

private def pointerPairs (block : Nat) : List (Instr × Instr) :=
  [(.LD .x6 .x8 (BitVec.ofNat 12 (32*block)),.LD .x6 .x8 0),
   (.SD .x21 .x6 32,.SD .x21 .x6 32),
   (.LD .x6 .x8 (BitVec.ofNat 12 (32*block+8)),.LD .x6 .x8 8),
   (.SD .x21 .x6 40,.SD .x21 .x6 40),
   (.LD .x6 .x8 (BitVec.ofNat 12 (32*block+16)),.LD .x6 .x8 16),
   (.SD .x21 .x6 48,.SD .x21 .x6 48),
   (.LD .x6 .x8 (BitVec.ofNat 12 (32*block+24)),.LD .x6 .x8 24),
   (.SD .x21 .x6 56,.SD .x21 .x6 56)]

set_option maxHeartbeats 1000000 in
theorem pointer_copy_reference (state : MachineState) (block : Nat) (bounded : block < 8) :
    pointerCopyState state block =
      (commitLeafCopyState (state.setReg .x8 (state.getReg .x8 + BitVec.ofNat 64 (32*block)))).setReg
        .x8 (state.getReg .x8) := by
  let base := state.getReg .x8
  let advance := base + BitVec.ofNat 64 (32*block)
  have oneStep (actual reference : MachineState)
      (related : PointerRelated base advance actual reference)
      (pair : Instr × Instr) (member : pair ∈ pointerPairs block) :
      PointerRelated base advance (execInstrBr actual pair.1) (execInstrBr reference pair.2) := by
    simp only [pointerPairs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | exact pointer_store_related base advance actual reference related _
    | apply pointer_load_related base advance actual reference related (BitVec.ofNat 12 (32*block))
      · dsimp only [advance]
        interval_cases block <;> rfl
      · interval_cases block <;> rfl
  have fold (pairs : List (Instr × Instr))
      (members : ∀ pair ∈ pairs, pair ∈ pointerPairs block)
      (actual reference : MachineState) (related : PointerRelated base advance actual reference) :
      PointerRelated base advance
        (pairs.foldl (fun current pair => execInstrBr current pair.1) actual)
        (pairs.foldl (fun current pair => execInstrBr current pair.2) reference) := by
    induction pairs generalizing actual reference with
    | nil => exact related
    | cons pair rest ih =>
      apply ih (fun p hp => members p (List.mem_cons_of_mem pair hp))
      exact oneStep actual reference related pair (members pair (by simp))
  have result := fold (pointerPairs block) (fun _ h => h) state (state.setReg .x8 advance)
    ⟨rfl,rfl⟩
  change PointerRelated base advance (pointerCopyState state block)
    (commitLeafCopyState (state.setReg .x8 advance)) at result
  rw [← result.2]
  apply Eq.symm
  cases h : pointerCopyState state block with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    have source : regs .x8 = base := by
      simpa only [h,MachineState.getReg] using result.1
    dsimp [MachineState.setReg]
    congr 1
    funext reg
    cases reg <;> first | exact source.symm | rfl

private theorem commit_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (commitLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitLeafCopyPrefix, commitLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

private def pointerCopyPrefix (state : MachineState) (block count : Nat) : MachineState :=
  ((pointerCopyOps block).take count).foldl execInstrBr state

private theorem pointer_copy_register (state : MachineState) (block count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (pointerCopyPrefix state block count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [pointerCopyPrefix, pointerCopyOps, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

set_option maxHeartbeats 8000000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem commit_leaf_copy (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+36*block))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (32*block + 8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (pointerCopyState state block) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := pointerCopyPrefix state block)
  intro i hi
  refine ⟨.base (((pointerCopyOps block)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (90 + 9*block + i) _ (by omega)
    · interval_cases block <;> interval_cases i <;>
        simp [pointerCopyPrefix, pointerCopyOps, execInstrBr, pc, MachineState.setPC]
    · rw [pointer_commit_code]
      interval_cases block <;> interval_cases i <;> rfl
  · have sourceReg := pointer_copy_register state block i (by omega) .x8 (by decide)
    have scratchReg := (pointer_copy_register state block i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have offsets (word : Fin 4) :
        BitVec.signExtend 64 (BitVec.ofNat 12 (32*block+8*word.val)) =
          BitVec.ofNat 64 (32*block+8*word.val) := by
      interval_cases block <;> fin_cases word <;> rfl
    have valid : memoryArgumentsValid (pointerCopyPrefix state block i)
        (((pointerCopyOps block)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [pointerCopyOps,List.getElem?_cons_zero,List.getElem?_cons_succ,
          Option.getD_some,memoryArgumentsValid,memAccess,sourceReg,scratchReg,signExtend12]
      case «0» =>
        exact (congrArg (fun offset : Word => accessValid (state.getReg .x8+offset) 8)
          (offsets ⟨0, by decide⟩)).trans s0
      case «2» =>
        exact (congrArg (fun offset : Word => accessValid (state.getReg .x8+offset) 8)
          (offsets ⟨1, by decide⟩)).trans s1
      case «4» =>
        exact (congrArg (fun offset : Word => accessValid (state.getReg .x8+offset) 8)
          (offsets ⟨2, by decide⟩)).trans s2
      case «6» =>
        exact (congrArg (fun offset : Word => accessValid (state.getReg .x8+offset) 8)
          (offsets ⟨3, by decide⟩)).trans s3
      all_goals rfl
    interval_cases i <;>
      simp only [pointerCopyOps, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Reference latch: advance the pointer and counter, and normalize the PC.
The unrolled execution lemmas explicitly replace this reference PC with its actual address. -/
def commitLeafNextState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 32)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4504 else 4456)

theorem commit_leaf_next_pc_irrel (state : MachineState) (pc : Word) :
    commitLeafNextState (state.setPC pc) = commitLeafNextState state := by
  cases state; rfl

/-- One final instruction advances the source base after all eight fixed-offset blocks. -/
theorem pointer_final_advance (state : MachineState) (pc : state.pc = 4744)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1+fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel
            ((state.setReg .x8 (state.getReg .x8+256)).setPC 4748) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.ADDI .x8 .x8 256)) := by
    apply commit_fetch _ 162 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.ADDI .x8 .x8 256)) =
      some ((state.setReg .x8 (state.getReg .x8+256)).setPC 4748) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,pc]
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- One leaf block: copy 32 bytes, compress, then advance the pointer and counter. -/
def commitLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  commitLeafNextState (commitCompressionState (commitLeafCopyState state) answer)

theorem commit_leaf_block_raw (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+36*block))
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (32*block+8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (9+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer (pointerCopyState state block) 256 64)))
          let result ← execute (submission.image .commit) fuel
            ((commitCompressionState (pointerCopyState state block) answer).setPC
              (BitVec.ofNat 64 (4456+36*(block+1)))) allowCoins
          return result.charge 16 1) := by
  have copyPC : (pointerCopyState state block).pc = BitVec.ofNat 64 (4488+36*block) := by
    interval_cases block <;> simp [pointerCopyState,pointerCopyOps,List.foldl,
      execInstrBr,MachineState.setPC,pc]
  have copyScratch : (pointerCopyState state block).getReg .x21 = 256 :=
    (pointer_copy_register state block 8 (by decide) .x21 (by decide)).trans scratch
  have copyReady : CommitLeafOracleReady (pointerCopyState state block) := by
    rcases ready with ⟨r5,r10,r11,r12,r13⟩
    unfold CommitLeafOracleReady
    exact ⟨(pointer_copy_register state block 8 (by decide) .x5 (by decide)).trans r5,
      (pointer_copy_register state block 8 (by decide) .x10 (by decide)).trans r10,
      (pointer_copy_register state block 8 (by decide) .x11 (by decide)).trans r11,
      (pointer_copy_register state block 8 (by decide) .x12 (by decide)).trans r12,
      (pointer_copy_register state block 8 (by decide) .x13 (by decide)).trans r13⟩
  rw [show 9+fuel=8+(1+fuel) by omega,
    commit_leaf_copy state block blockBound pc scratch sourceValid,
    commit_compression _ block blockBound copyPC copyScratch copyReady]
  simp only [bind_assoc,pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer (pointerCopyState state block) 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  have targetPC : (pointerCopyState state block).pc + 4 =
      BitVec.ofNat 64 (4456+36*(block+1)) := by
    rw [copyPC]; interval_cases block <;> rfl
  rw [targetPC]
  simp [Execution.charge,← Nat.add_assoc]

/-- The normalized reference transition records the fixed arguments for the next block. -/
theorem commit_leaf_step_ready (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    CommitLeafOracleReady (commitLeafStepState state answer) := by
  have copyScratch : (commitLeafCopyState state).regs .x21 = 256 :=
    (commit_copy_register state 8 (by decide) .x21 (by decide)).trans scratch
  have regs : CommitLeafOracleReady (commitCompressionPrefix (commitLeafCopyState state) 5) := by
    simp [CommitLeafOracleReady, commitCompressionPrefix, commitCompressionInstructions,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, copyScratch]
  change CommitLeafOracleReady (commitCompressionState (commitLeafCopyState state) answer)
  unfold CommitLeafOracleReady at regs ⊢
  simpa only [commitCompressionState, writeBits_register] using regs

/-- The next iteration has the advanced source pointer and decremented counter;
its scratch pointer and subroutine return address are unchanged. -/
theorem commit_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (commitLeafStepState state answer).getReg .x28 = state.getReg .x28 - 1 ∧
    (commitLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (commitLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (not6 : reg ≠ .x6) (not5 : reg ≠ .x5) (not10 : reg ≠ .x10)
      (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
      (commitCompressionState (commitLeafCopyState state) answer).getReg reg = state.getReg reg :=
    (commit_compression_register _ answer reg not5 not10 not11 not12 not13).trans
      (commit_copy_register state 8 (by decide) reg not6)
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x1),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem commit_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).pc =
      if state.getReg .x28 - 1 = 0 then 4504 else 4456 := by
  change (if (commitCompressionState (commitLeafCopyState state) answer).getReg .x28 - 1 = 0
    then 4504 else 4456) = _
  rw [commit_compression_register _ answer .x28 (by decide) (by decide) (by decide) (by decide) (by decide),
    commitLeafCopyState, commit_copy_register state 8 (by decide) .x28 (by decide)]

/-- Reference unfolding of the eight actual block computations. Each iteration issues
the image's exact scratch query and applies its byte writes and register transitions;
internal PCs are normalized and restored to actual addresses by the execution theorem. -/
def commitLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
      commitLeafLoop (commitLeafStepState state answer) count

theorem unroll_copy_pc (state : MachineState) (target : Word) :
    commitLeafCopyState (state.setPC target) =
      (commitLeafCopyState state).setPC (target + 32) := by
  change commitLeafCopyInstructions.foldl execInstrBr (state.setPC target) =
    (commitLeafCopyInstructions.foldl execInstrBr state).setPC (target + 32)
  cases state
  dsimp [commitLeafCopyInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  simp [BitVec.add_assoc]

theorem unroll_compression_pc (state : MachineState) (target : Word) (answer : BitVec 256) :
    commitCompressionState (state.setPC target) answer =
      (commitCompressionState state answer).setPC (target + 24) := by
  have argsShift : commitCompressionInstructions.foldl execInstrBr (state.setPC target) =
      (commitCompressionInstructions.foldl execInstrBr state).setPC (target + 20) := by
    cases state
    dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
      MachineState.setReg,MachineState.setPC]
    congr 1
    simp [BitVec.add_assoc]
  change writeBits (commitCompressionInstructions.foldl execInstrBr (state.setPC target)) 256 answer =
    (writeBits (commitCompressionInstructions.foldl execInstrBr state) 256 answer).setPC (target + 24)
  rw [argsShift,hoist_write_bits_pc]
  simp [BitVec.add_assoc]

theorem unroll_read_pc (state : MachineState) (target : Word) (address bytes : Nat) :
    readBuffer (state.setPC target) address bytes = readBuffer state address bytes := rfl

theorem unroll_step_pc (state : MachineState) (target : Word) (answer : BitVec 256) :
    commitLeafStepState (state.setPC target) answer = commitLeafStepState state answer := by
  unfold commitLeafStepState
  rw [unroll_copy_pc,unroll_compression_pc,commit_leaf_next_pc_irrel]

theorem unroll_loop_pc_positive (state : MachineState) (target : Word) (count : Nat) :
    commitLeafLoop (state.setPC target) (count + 1) = commitLeafLoop state (count + 1) := by
  have inputEq : readBuffer (commitLeafCopyState (state.setPC target)) 256 64 =
      readBuffer (commitLeafCopyState state) 256 64 := by
    rw [unroll_copy_pc,unroll_read_pc]
  have tailEq : (fun answer : BitVec 256 =>
      commitLeafLoop (commitLeafStepState (state.setPC target) answer) count) =
      (fun answer : BitVec 256 => commitLeafLoop (commitLeafStepState state answer) count) := by
    funext answer
    exact congrArg (fun next => commitLeafLoop next count) (unroll_step_pc state target answer)
  exact congrArg₂ (fun (input : BitVec COMPRESSION_INPUT_LENGTH)
      (tail : BitVec 256 → OracleComp World MachineState) =>
        (liftM (World.query (.inr (.inl input))) : OracleComp World (BitVec 256)) >>= tail)
    inputEq tailEq

theorem unroll_loop_pc_bind {α : Type} (state : MachineState) (target finalPC : Word)
    (count : Nat) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop (state.setPC target) count
        continuation (finished.setPC finalPC)) =
      (do let finished ← commitLeafLoop state count
          continuation (finished.setPC finalPC)) := by
  cases count with
  | zero => simp [commitLeafLoop,hoist_pc_pc]
  | succ count => rw [unroll_loop_pc_positive]

theorem counter_write {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (value : Word) :
    writeBits (state.setReg .x28 value) address answer =
      (writeBits state address answer).setReg .x28 value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg .x28 value).setByte a b = (s.setByte a b).setReg .x28 value := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg .x28 value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg .x28 value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons,byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl

theorem counter_copy (state : MachineState) (value : Word) :
    commitLeafCopyState (state.setReg .x28 value) =
      (commitLeafCopyState state).setReg .x28 value := by
  change commitLeafCopyInstructions.foldl execInstrBr (state.setReg .x28 value) =
    (commitLeafCopyInstructions.foldl execInstrBr state).setReg .x28 value
  cases state
  dsimp [commitLeafCopyInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem counter_compression (state : MachineState) (value : Word) (answer : BitVec 256) :
    commitCompressionState (state.setReg .x28 value) answer =
      (commitCompressionState state answer).setReg .x28 value := by
  have argsShift : commitCompressionInstructions.foldl execInstrBr (state.setReg .x28 value) =
      (commitCompressionInstructions.foldl execInstrBr state).setReg .x28 value := by
    cases state
    dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
      MachineState.setReg,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  change writeBits (commitCompressionInstructions.foldl execInstrBr (state.setReg .x28 value)) 256 answer =
    (writeBits (commitCompressionInstructions.foldl execInstrBr state) 256 answer).setReg .x28 value
  rw [argsShift,counter_write]
theorem counter_step (state : MachineState) (value : Word) (answer : BitVec 256) :
    commitLeafStepState (state.setReg .x28 value) answer =
      ((commitLeafStepState state answer).setReg .x28 (value-1)).setPC
        (if value-1=0 then 4504 else 4456) := by
  unfold commitLeafStepState
  rw [counter_copy,counter_compression]
  generalize commitCompressionState (commitLeafCopyState state) answer = base
  cases base
  dsimp [commitLeafNextState,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl
theorem counter_loop_bind {α : Type} (state : MachineState) (value target finalPC : Word)
    (count : Nat) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop ((state.setReg .x28 value).setPC target) count
        continuation ((finished.setReg .x28 0).setPC finalPC)) =
      (do let finished ← commitLeafLoop state count
          continuation ((finished.setReg .x28 0).setPC finalPC)) := by
  induction count generalizing state value target with
  | zero =>
    simp only [commitLeafLoop,pure_bind]
    apply congrArg continuation
    cases state
    dsimp [MachineState.setReg,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  | succ count ih =>
    have inputEq :
        readBuffer (commitLeafCopyState ((state.setReg .x28 value).setPC target)) 256 64 =
          readBuffer (commitLeafCopyState state) 256 64 := by
      rw [unroll_copy_pc,counter_copy]
      rfl
    have tailEq :
        (fun answer : BitVec 256 => do
          let finished ← commitLeafLoop
            (commitLeafStepState ((state.setReg .x28 value).setPC target) answer) count
          continuation ((finished.setReg .x28 0).setPC finalPC)) =
        (fun answer : BitVec 256 => do
          let finished ← commitLeafLoop (commitLeafStepState state answer) count
          continuation ((finished.setReg .x28 0).setPC finalPC)) := by
      funext answer
      rw [unroll_step_pc,counter_step]
      exact ih _ _ _
    exact congrArg₂ (fun (input : BitVec COMPRESSION_INPUT_LENGTH)
        (tail : BitVec 256 → OracleComp World α) =>
          (liftM (World.query (.inr (.inl input))) : OracleComp World (BitVec 256)) >>= tail)
      inputEq tailEq
theorem counter_reg_self (state : MachineState) (value : Word)
    (equal : state.getReg .x28 = value) : state.setReg .x28 value = state := by
  cases state
  dsimp [MachineState.setReg,MachineState.getReg] at equal ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

theorem counter_loop_plain_bind {α : Type} (state : MachineState) (value finalPC : Word)
    (count : Nat) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop (state.setReg .x28 value) count
        continuation ((finished.setReg .x28 0).setPC finalPC)) =
      (do let finished ← commitLeafLoop state count
          continuation ((finished.setReg .x28 0).setPC finalPC)) := by
  have currentPC : (state.setReg .x28 value).pc = state.pc := rfl
  have initialEq : (state.setReg .x28 value).setPC state.pc = state.setReg .x28 value := by
    rw [← currentPC,hoist_pc_self]
  have result := counter_loop_bind state value state.pc finalPC count continuation
  rw [initialEq] at result
  exact result

def pointerFinish (state : MachineState) (base pc : Word) : MachineState :=
  ((state.setReg .x28 0).setPC pc).setReg .x8 base

def pointerInput (state : MachineState) (block : Nat) : MachineState :=
  state.setReg .x8 (state.getReg .x8 + BitVec.ofNat 64 (32*block))

theorem pointer_reg_self (state : MachineState) (value : Word)
    (equal : state.getReg .x8 = value) : state.setReg .x8 value = state := by
  cases state
  dsimp [MachineState.setReg,MachineState.getReg] at equal ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

theorem pointer_input_zero (state : MachineState) : pointerInput state 0 = state := by
  change state.setReg .x8 (state.getReg .x8 + (0 : Word)) = state
  exact (congrArg (fun value : Word => state.setReg .x8 value)
    (BitVec.add_zero (state.getReg .x8))).trans (pointer_reg_self state _ rfl)

theorem pointer_finish_reframe (state : MachineState) (base pc : Word) (block : Nat)
    (progress : state.getReg .x8 = base + BitVec.ofNat 64 (32*(block+1))) :
    pointerInput (pointerFinish state base pc) (block+1) = (state.setReg .x28 0).setPC pc := by
  cases state
  dsimp [pointerInput,pointerFinish,MachineState.getReg,MachineState.setReg,
    MachineState.setPC] at progress ⊢
  congr 1
  funext reg
  cases reg <;> first | exact progress.symm | rfl

theorem pointer_step_erase (state : MachineState) (answer : BitVec 256) (base pc : Word) :
    pointerFinish (commitLeafStepState state answer) base pc =
      pointerFinish (commitCompressionState (commitLeafCopyState state) answer) base pc := by
  unfold commitLeafStepState
  generalize commitCompressionState (commitLeafCopyState state) answer = middle
  cases middle
  dsimp [pointerFinish,commitLeafNextState,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem pointer_copy_preserved (state : MachineState) (block : Nat) (reg : Reg) (scratch : reg ≠ .x6) :
    (pointerCopyState state block).getReg reg = state.getReg reg := by
  have memRegister (s : MachineState) (address value : Word) (r : Reg) :
      (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl
  simp only [pointerCopyState,pointerCopyOps,List.foldl,execInstrBr,
    MachineState.getReg_setPC,memRegister,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem pointer_block_state (state : MachineState) (answer : BitVec 256) (block : Nat)
    (bounded : block < 8) (counter : state.getReg .x28 = 0) (pc : Word) :
    (commitCompressionState (pointerCopyState state block) answer).setPC pc =
      pointerFinish (commitLeafStepState (pointerInput state block) answer) (state.getReg .x8) pc := by
  have actualCounter : (commitCompressionState (pointerCopyState state block) answer).getReg .x28 = 0 := by
    rw [commit_compression_register _ answer .x28 (by decide) (by decide) (by decide) (by decide) (by decide),
      pointer_copy_preserved state block .x28 (by decide)]
    exact counter
  have referenceCounter :
      (commitCompressionState (commitLeafCopyState (pointerInput state block)) answer).getReg .x28 = 0 := by
    simpa only [pointer_copy_reference state block bounded,pointer_compression,
      pointerInput,MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x28)] using actualCounter
  rw [pointer_copy_reference state block bounded,pointer_compression,pointer_step_erase]
  unfold pointerFinish
  rw [counter_reg_self _ 0 referenceCounter]
  rfl
theorem pointer_finish_input (state : MachineState) (block : Nat) (base pc : Word) :
    pointerFinish (pointerInput state block) base pc = pointerFinish state base pc := by
  cases state
  dsimp [pointerFinish,pointerInput,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem pointer_finish_self (state : MachineState) (counter : state.getReg .x28 = 0) :
    pointerFinish state (state.getReg .x8) state.pc = state := by
  unfold pointerFinish
  rw [counter_reg_self state 0 counter,hoist_pc_self]
  exact pointer_reg_self state _ rfl

theorem pointer_step_progress (state : MachineState) (block : Nat) (answer : BitVec 256) :
    (commitLeafStepState (pointerInput state block) answer).getReg .x8 =
      state.getReg .x8 + BitVec.ofNat 64 (32*(block+1)) := by
  rw [(commit_leaf_block_registers (pointerInput state block) answer).1]
  simp only [pointerInput,MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0)]
  rw [Nat.mul_succ,BitVec.ofNat_add,BitVec.add_assoc]
  rfl

/-- Exact block execution expressed through the existing reference transition. -/
theorem pointer_leaf_block (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+36*block))
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (counter : state.getReg .x28 = 0)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (32*block+8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (9+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl
            (readBuffer (commitLeafCopyState (pointerInput state block)) 256 64)))
          let result ← execute (submission.image .commit) fuel
            (pointerFinish (commitLeafStepState (pointerInput state block) answer)
              (state.getReg .x8) (BitVec.ofNat 64 (4456+36*(block+1)))) allowCoins
          return result.charge 16 1) := by
  have inputEq : readBuffer (pointerCopyState state block) 256 64 =
      readBuffer (commitLeafCopyState (pointerInput state block)) 256 64 := by
    rw [pointer_copy_reference state block blockBound]
    rfl
  have tailEq :
      (fun answer : BitVec 256 => do
        let result ← execute (submission.image .commit) fuel
          ((commitCompressionState (pointerCopyState state block) answer).setPC
            (BitVec.ofNat 64 (4456+36*(block+1)))) allowCoins
        return result.charge 16 1) =
      (fun answer : BitVec 256 => do
        let result ← execute (submission.image .commit) fuel
          (pointerFinish (commitLeafStepState (pointerInput state block) answer)
            (state.getReg .x8) (BitVec.ofNat 64 (4456+36*(block+1)))) allowCoins
        return result.charge 16 1) := by
    funext answer
    rw [pointer_block_state state answer block blockBound counter]
  exact (commit_leaf_block_raw state block blockBound pc scratch ready sourceValid fuel allowCoins).trans
    (congrArg₂ (fun (input : BitVec COMPRESSION_INPUT_LENGTH)
      (tail : BitVec 256 → OracleComp World Execution) =>
        (liftM (World.query (.inr (.inl input))) : OracleComp World (BitVec 256)) >>= tail)
      inputEq tailEq)

set_option maxHeartbeats 2000000 in
/-- Fixed-offset blocks preserve the actual source base. The reference pointer is
advanced virtually at the current block; the final actual ADDI restores it once. -/
theorem commit_leaf_loop (state : MachineState) (count first : Nat) (total : first+count=8)
    (pc : state.pc = BitVec.ofNat 64 (4456+36*first))
    (counter : state.getReg .x28 = 0) (scratch : state.getReg .x21 = 256)
    (ready : CommitLeafOracleReady state)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (9*count+fuel) state allowCoins =
      (do let finished ← commitLeafLoop (pointerInput state first) count
          let result ← execute (submission.image .commit) fuel
            (pointerFinish finished (state.getReg .x8) 4744) allowCoins
          return result.charge (16*count) count) := by
  induction count generalizing state first with
  | zero =>
    have firstEq : first=8 := by omega
    have statePC : state.pc=4744 := by simpa [firstEq] using pc
    have normalized : pointerFinish state (state.getReg .x8) 4744 = state := by
      rw [← statePC]
      exact pointer_finish_self state counter
    simp only [Nat.mul_zero,Nat.zero_add,commitLeafLoop,pure_bind,pointer_finish_input]
    rw [normalized]
    simp [Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8+BitVec.ofNat 64 (32*first+8*word.val)) 8 = true := by
      have address : 32*first+8*word.val=8*(4*first+word.val) := by omega
      rw [address]
      exact sourceValid (4*first+word.val) (by omega)
    rw [show 9*(count+1)+fuel=9+(9*count+fuel) by omega,
      pointer_leaf_block state first (by omega) pc scratch ready counter currentValid]
    simp only [commitLeafLoop,bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl
        (readBuffer (commitLeafCopyState (pointerInput state first)) 256 64)))) :
          OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    let referenceNext := commitLeafStepState (pointerInput state first) answer
    let actualNext := pointerFinish referenceNext (state.getReg .x8)
      (BitVec.ofNat 64 (4456+36*(first+1)))
    have nextBase : actualNext.getReg .x8=state.getReg .x8 := rfl
    have actualCounter : actualNext.getReg .x28=0 := rfl
    have framedScratch : (pointerInput state first).getReg .x21=256 := by
      exact (MachineState.getReg_setReg_ne state .x8 .x21
        (state.getReg .x8+BitVec.ofNat 64 (32*first)) (by decide)).trans scratch
    have referenceScratch : referenceNext.getReg .x21=256 :=
      (commit_leaf_block_registers (pointerInput state first) answer).2.2.1.trans framedScratch
    have referenceReady : CommitLeafOracleReady referenceNext :=
      commit_leaf_step_ready (pointerInput state first) answer framedScratch
    have frameRegister (current : MachineState) (base pc : Word) (reg : Reg)
        (not8 : Reg.x8 ≠ reg) (not28 : Reg.x28 ≠ reg) :
        (pointerFinish current base pc).getReg reg=current.getReg reg := by
      simp only [pointerFinish,
        MachineState.getReg_setReg_ne _ _ _ _ not8,MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ not28]
    have actualScratch : actualNext.getReg .x21=256 :=
      (frameRegister referenceNext _ _ .x21 (by decide) (by decide)).trans referenceScratch
    have actualReady : CommitLeafOracleReady actualNext := by
      rcases referenceReady with ⟨r5,r10,r11,r12,r13⟩
      exact ⟨(frameRegister referenceNext _ _ .x5 (by decide) (by decide)).trans r5,
        (frameRegister referenceNext _ _ .x10 (by decide) (by decide)).trans r10,
        (frameRegister referenceNext _ _ .x11 (by decide) (by decide)).trans r11,
        (frameRegister referenceNext _ _ .x12 (by decide) (by decide)).trans r12,
        (frameRegister referenceNext _ _ .x13 (by decide) (by decide)).trans r13⟩
    have actualSource : ∀ word < 32,
        accessValid (actualNext.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true := by
      simpa only [nextBase] using sourceValid
    rw [ih actualNext (first+1) (by omega) rfl actualCounter actualScratch actualReady actualSource]
    have framedNext : pointerInput actualNext (first+1) =
        (referenceNext.setReg .x28 0).setPC (BitVec.ofNat 64 (4456+36*(first+1))) :=
      pointer_finish_reframe referenceNext (state.getReg .x8) _ first
        (pointer_step_progress state first answer)
    rw [framedNext,nextBase]
    have tailEq :
        (do let finished ← commitLeafLoop ((referenceNext.setReg .x28 0).setPC
              (BitVec.ofNat 64 (4456+36*(first+1)))) count
            let result ← execute (submission.image .commit) fuel
              (pointerFinish finished (state.getReg .x8) 4744) allowCoins
            return result.charge (16*count) count) =
        (do let finished ← commitLeafLoop referenceNext count
            let result ← execute (submission.image .commit) fuel
              (pointerFinish finished (state.getReg .x8) 4744) allowCoins
            return result.charge (16*count) count) :=
      counter_loop_bind referenceNext 0 (BitVec.ofNat 64 (4456+36*(first+1))) 4744 count
        (fun finished => do
          let result ← execute (submission.image .commit) fuel
            (finished.setReg .x8 (state.getReg .x8)) allowCoins
          return result.charge (16*count) count)
    rw [tailEq]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,referenceNext]

/-- Every possible run of the bounded loop exhausts its counter and preserves the
return address. A nonempty reference loop records its normalized return address. -/
theorem commit_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4504) := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (commitLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(commit_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have remaining := ih _ (by omega) nextCounter reached
    refine ⟨remaining.1, remaining.2.1.trans (commit_leaf_block_registers state answer).2.2.2, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_leaf_block_pc state answer, counter]
      rfl
    · exact remaining.2.2 (by omega)

theorem counter_ready_prefix (state : MachineState) :
    commitCompressionPrefix ((state.setReg .x28 0).setPC 4436) 5 =
      (commitLeafReadyState state).setReg .x28 0 := by
  change commitCompressionInstructions.foldl execInstrBr ((state.setReg .x28 0).setPC 4436) =
    (commitCompressionInstructions.foldl execInstrBr ((state.setReg .x28 8).setPC 4436)).setReg .x28 0
  cases state
  dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

private theorem commit_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28]) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28⟩
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (commit_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (commit_copy_register state 8 (by decide) reg not6)

/-- The complete hash preserves the position/path metadata, proof pointer, root
pointer, and scratch pointer. It consumes exactly 32 bytes per block from x8. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    constructor
    · rw [rest.1, (commit_leaf_block_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (commit_leaf_block_preserves state answer reg preserved)


/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4748)
    (link : state.getReg .x1 = 4316) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4316) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply commit_fetch _ 163 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4316) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Every reference block preserves the live oracle arguments when scratch is fixed. -/
theorem commit_leaf_loop_ready (state : MachineState) (count : Nat)
    (scratch : state.getReg .x21=256) (ready : CommitLeafOracleReady state)
    (finished : MachineState) (reachable : finished ∈ support (commitLeafLoop state count)) :
    CommitLeafOracleReady finished := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop,support_pure,Set.mem_singleton_iff] at reachable
    subst finished
    exact ready
  | succ count ih =>
    simp only [commitLeafLoop,mem_support_bind_iff] at reachable
    obtain ⟨answer,_,reached⟩ := reachable
    exact ih _ ((commit_leaf_block_registers state answer).2.2.1.trans scratch)
      (commit_leaf_step_ready state answer scratch) reached

theorem global_ready_frame (state : MachineState) (pc : state.pc=4456)
    (scratch : state.getReg .x21=256) (ready : CommitLeafOracleReady state)
    (counter : state.getReg .x28=0) :
    (commitLeafReadyState state).setReg .x28 0=state := by
  change (commitCompressionInstructions.foldl execInstrBr ((state.setReg .x28 8).setPC 4436)).setReg .x28 0=state
  cases state
  dsimp [CommitLeafOracleReady,MachineState.getReg] at scratch ready counter pc
  dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC]
  congr 1
  · funext reg
    cases reg <;> simp_all
  · simp_all

/-- With fixed arguments already live, eight nine-instruction blocks hash one leaf.
The reference block counter is erased by the entry bridge and continuation frame. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc=4456)
    (link : state.getReg .x1=4316) (scratch : state.getReg .x21=256)
    (ready : CommitLeafOracleReady state) (counter : state.getReg .x28=0)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (74+fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafReadyState state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4316) allowCoins
          return result.charge 130 8) := by
  let referenceReady := commitLeafReadyState state
  have framed : referenceReady.setReg .x28 0=state :=
    global_ready_frame state pc scratch ready counter
  have refCounter : referenceReady.getReg .x28=BitVec.ofNat 64 8 := by simp [referenceReady]
  rw [show 74+fuel=9*8+(1+(1+fuel)) by omega,
    commit_leaf_loop state 8 0 (by decide) pc counter scratch ready sourceValid,
    pointer_input_zero]
  have frame :
      (do let finished ← commitLeafLoop state 8
          let result ← execute (submission.image .commit) (1+(1+fuel))
            (pointerFinish finished (state.getReg .x8) 4744) allowCoins
          return result.charge (16*8) 8) =
      (do let finished ← commitLeafLoop referenceReady 8
          let result ← execute (submission.image .commit) (1+(1+fuel))
            (pointerFinish finished (state.getReg .x8) 4744) allowCoins
          return result.charge (16*8) 8) := by
    have equality := counter_loop_plain_bind referenceReady 0 4744 8
      (fun finished => do
        let result ← execute (submission.image .commit) (1+(1+fuel))
          (finished.setReg .x8 (state.getReg .x8)) allowCoins
        return result.charge (16*8) 8)
    rw [framed] at equality
    exact equality
  rw [frame]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := commit_leaf_loop_finished referenceReady 8 (by decide) refCounter finished reachable
  have finalLink : finished.getReg .x1=4316 := by
    rw [done.2.1]
    exact (commit_leaf_ready_register state .x1 (by decide)).trans link
  have progress : finished.getReg .x8=state.getReg .x8+256 := by
    rw [(commit_leaf_loop_registers referenceReady 8 finished reachable).1,
      commit_leaf_ready_register state .x8 (by decide)]
    rfl
  have advanced :
      ((pointerFinish finished (state.getReg .x8) 4744).setReg .x8
        ((pointerFinish finished (state.getReg .x8) 4744).getReg .x8+256)).setPC 4748 =
      finished.setPC 4748 := by
    unfold pointerFinish
    rw [counter_reg_self finished 0 done.1]
    change (((finished.setPC 4744).setReg .x8 (state.getReg .x8)).setReg .x8
      (state.getReg .x8+256)).setPC 4748 = finished.setPC 4748
    cases finished
    dsimp [MachineState.getReg,MachineState.setReg,MachineState.setPC] at progress ⊢
    congr 1
    funext reg
    cases reg <;> first | exact progress.symm | rfl
  rw [pointer_final_advance (pointerFinish finished (state.getReg .x8) 4744) rfl,
    advanced,commit_leaf_return (finished.setPC 4748) rfl finalLink,hoist_pc_pc]
  simp [instructionCycles,Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate
