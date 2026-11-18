import CommitGolfCandidate.NonceCompressedFetch

/-! Query-free runs of the delivered checker, observed through the exit of every continuation,
and the instruction words of the expansion (words 445..545). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- `state` reaches `next` after `steps` ordinary instructions of the delivered check image:
every continuation from `state` with `steps` more fuel has the exit of the one from `next`. -/
def NonceExpandRuns (state : MachineState) (steps : Nat) (next : MachineState) : Prop :=
  ∀ fuel, Execution.exit <$> execute nonceExpandedImage (steps + fuel) state false =
    Execution.exit <$> execute nonceExpandedImage fuel next false

theorem NonceExpandRuns.refl (state : MachineState) : NonceExpandRuns state 0 state := by
  intro fuel
  rw [Nat.zero_add]

theorem NonceExpandRuns.trans {first second third : MachineState} {left right : Nat}
    (head : NonceExpandRuns first left second) (tail : NonceExpandRuns second right third) :
    NonceExpandRuns first (left + right) third := by
  intro fuel
  rw [Nat.add_assoc, head, tail]

theorem NonceExpandRuns.cast {state next : MachineState} {steps other : Nat}
    (run : NonceExpandRuns state steps next) (equal : steps = other) :
    NonceExpandRuns state other next := equal ▸ run

theorem nonce_expand_runs_step (state next : MachineState) (instruction : Instruction)
    (fetched : fetch nonceExpandedImage state = some instruction)
    (stepped : ordinaryStep state instruction = some next) : NonceExpandRuns state 1 next := by
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Execution.charge]

/-- The words of the expansion, check words 445..545. -/
def nonceExpandWords : List (BitVec 32) :=
  [0x58d13, 0x18f313, 0xbc0316e3, 0x21600e93, 0x3d80333, 0xbc68e0e3, 0x40688e33, 0x1e00393,
   0x27e7f33, 0xba0f18e3, 0x27e5e33, 0x24000e93, 0x3d80933, 0x5e1393, 0x790933, 0x1900993,
   0x1d99993, 0xb929e8e3, 0x1178bb3, 0x1278cb3, 0x80c13, 0xe0e93, 0xe8863, 0xb0000ef,
   0xfffe8e93, 0xff5ff06f, 0x40c0a63, 0xd00e93, 0x9c000ef, 0xfffe8e93, 0xfe0e9ce3, 0x4000e13,
   0x70000ef, 0xff8c8c93, 0xcb023, 0xff8c8c93, 0x3c1313, 0xd30333, 0xff833303, 0x831313,
   0x7ff30313, 0x7e930313, 0x6cb023, 0x800e13, 0x40000ef, 0xfffc0c13, 0xfa0c1ae3, 0x90893,
   0x93, 0x313, 0x393, 0x913, 0x993, 0xb93, 0xc13, 0xc93,
   0xe13, 0xe93, 0xf13, 0x825ff06f, 0xffeb8b93, 0xffec8c93, 0xbd303, 0x6c9023,
   0xfffe0e13, 0xfe0e16e3, 0x8067, 0xfe0c8c93, 0xfe2b8b93, 0xc9f23, 0x1cbd303, 0x6c9e23,
   0x1abd303, 0x6c9d23, 0x18bd303, 0x6c9c23, 0x16bd303, 0x6c9b23, 0x14bd303, 0x6c9a23,
   0x12bd303, 0x6c9923, 0x10bd303, 0x6c9823, 0xebd303, 0x6c9723, 0xcbd303, 0x6c9623,
   0xabd303, 0x6c9523, 0x8bd303, 0x6c9423, 0x6bd303, 0x6c9323, 0x4bd303, 0x6c9223,
   0x2bd303, 0x6c9123, 0xbd303, 0x6c9023, 0x8067]

theorem nonce_expand_words : nonceExpandedImage.code.drop 445 = nonceExpandWords := by
  decide

theorem nonce_expand_word (index : Nat) (above : 445 ≤ index) :
    nonceExpandedImage.code[index]? = nonceExpandWords[index - 445]? := by
  rw [← nonce_expand_words, List.getElem?_drop]
  congr 1
  omega

/-- Fetch at word `index` of any image (no bound on the image length). -/
theorem nonce_image_fetch (image : Image) (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 2 ^ 60) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (image.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch image state = some (.base instruction) := by
  have numeric : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, if_pos (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

/-- One expansion instruction at word `index`: its word decodes to `instruction` and its memory
access, if any, is valid. -/
theorem nonce_expand_exec (state : MachineState) (index : Nat) (instruction : Instr)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index)) (above : 445 ≤ index) (inside : index < 546)
    (decoded : (nonceExpandWords[index - 445]?).bind decodeInstruction = some (.base instruction))
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction)) :
    NonceExpandRuns state 1 (execInstrBr state instruction) := by
  apply nonce_expand_runs_step _ _ _ _ stepped
  apply nonce_image_fetch _ _ index _ (by omega) pc
  rw [nonce_expand_word index above]
  exact decoded

end CommitGolfCandidate
