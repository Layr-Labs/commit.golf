import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.Memory
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import RiscvZkvm.Rv64.Logic.ByteOps
import CommitGolfCandidate.ProjectedHalfword
import CommitGolfCandidate.InputMemory

/-! # The four doublewords of a 238-bit node

A node kept at 238 bits (`pad238`, tree levels 8..16) agrees with the compression output on its three low
doublewords; its top doubleword keeps bits `192..237` (46 bits) and clears the rest. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling (pad238)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- The top doubleword of a 238-bit node. -/
def top238 (x : BitVec 256) : BitVec 64 := (pad238 x).extractLsb' 192 64

theorem pad238_bit (x : BitVec 256) (i : Nat) : (pad238 x).getLsbD i = (decide (i < 238) && x.getLsbD i) := by
  unfold pad238
  rw [BitVec.getLsbD_append]
  by_cases low : i < 238
  · simp [low, BitVec.getLsbD_extractLsb']
  · simp [low]

theorem top238_bit (x : BitVec 256) (i : Nat) : (top238 x).getLsbD i = (decide (i < 46) && x.getLsbD (192+i)) := by
  unfold top238
  rw [BitVec.getLsbD_extractLsb', pad238_bit]
  by_cases low : i < 46
  · simp [low, show i < 64 by omega, show 192+i < 238 by omega]
  · simp [low, show ¬ 192+i < 238 by omega]

/-- `top238` is the top doubleword with its 18 high bits shifted out. -/
theorem top238_shift (x : BitVec 256) : top238 x = (x.extractLsb' 192 64 <<< 18) >>> 18 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [top238_bit, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  by_cases low : i < 46
  · simp [low, show 18+i < 64 by omega, show ¬ 18+i < 18 by omega, show 18+i-18 = i by omega,
      show i < 64 by omega]
  · simp [low, show ¬ 18+i < 64 by omega]

theorem pad238_dwords (x : BitVec 256) :
    ((top238 x ++ x.extractLsb' 128 64) ++ x.extractLsb' 64 64) ++ x.extractLsb' 0 64 = pad238 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [pad238_bit]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', top238_bit]
  by_cases a : i < 64
  · simp [a, show i < 238 by omega]
  · by_cases b : i - 64 < 64
    · simp [a, b, show i < 238 by omega, show 64 + (i - 64) = i by omega]
    · by_cases c : i - 64 - 64 < 64
      · simp [a, b, c, show i < 238 by omega, show 128 + (i - 64 - 64) = i by omega]
      · have top : 192 + (i - 64 - 64 - 64) = i := by omega
        have cut : i - 64 - 64 - 64 < 46 ↔ i < 238 := by omega
        simp [a, b, c, top, cut]

/-- `lhu t,4(w); slli t,t,50; srli t,t,50; sw t,4(w)` on one doubleword keeps its low 46 bits. -/
theorem mask_word (d : Word) :
    replaceWord32 d 1 (((((extractHalfword d 2).zeroExtend 64) <<< 50) >>> 50).truncate 32) = (d <<< 18) >>> 18 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceWord32, extractHalfword]

/-- A 32-byte read whose low three doublewords are the answer's and whose top doubleword is `top238`. -/
theorem read_pad238 (s : MachineState) (base : Nat) (aligned : base % 8 = 0) (x : BitVec 256)
    (w0 : s.getMem (BitVec.ofNat 64 base) = x.extractLsb' 0 64)
    (w1 : s.getMem (BitVec.ofNat 64 (base+8)) = x.extractLsb' 64 64)
    (w2 : s.getMem (BitVec.ofNat 64 (base+16)) = x.extractLsb' 128 64)
    (w3 : s.getMem (BitVec.ofNat 64 (base+24)) = top238 x) :
    readBuffer s base 32 = pad238 x := by
  rw [read_digest_words s base aligned, w0, w1, w2, w3]
  exact pad238_dwords x

/-! ### Single instructions of the checker image -/

attribute [local irreducible] execute

/-- One ordinary one-cycle instruction at word `w`. -/
theorem arm_hop (s : MachineState) (w : Nat) (i : Instr) (bound : w < 705)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (decoded : (packedImage.code[w]?).bind decodeInstruction = some (.base i))
    (step : ordinaryStep s (.base i) = some (execInstrBr s i))
    (cost : instructionCycles (.base i) = 1) :
    GroupHop s (execInstrBr s i) 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_at s w i bound pc decoded) step, cost]

theorem pc_next {s t : MachineState} {w : Nat} (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (moved : t.pc = s.pc + 4) : t.pc = BitVec.ofNat 64 (4096+4*(w+1)) := by
  rw [moved, pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

theorem access_ofNat (a n : Nat) (fits : a + n ≤ MEMORY_BYTES) (aligned : a % n = 0) :
    accessValid (BitVec.ofNat 64 a) n = true := by
  have lim : MEMORY_BYTES < 2^64 := by decide
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2^64),
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fits, aligned⟩

theorem lhu_step (s : MachineState) (rd rs : Reg) (o : BitVec 12)
    (valid : accessValid (s.getReg rs + signExtend12 o) 2 = true) :
    ordinaryStep s (.base (.LHU rd rs o)) = some (execInstrBr s (.LHU rd rs o)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

theorem sw_step (s : MachineState) (rs rv : Reg) (o : BitVec 12)
    (valid : accessValid (s.getReg rs + signExtend12 o) 4 = true) :
    ordinaryStep s (.base (.SW rs rv o)) = some (execInstrBr s (.SW rs rv o)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

theorem arm_byte_offset (dword i : Nat) (aligned : dword % 8 = 0) (small : i < 8) :
    byteOffset (BitVec.ofNat 64 (dword+i)) = i := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((dword+i)%2^64) &&& (2^3-1) = i
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem arm_align (dword i : Nat) (aligned : dword % 8 = 0) (small : i < 8) :
    alignToDword (BitVec.ofNat 64 (dword+i)) = BitVec.ofNat 64 dword := by
  have split := alignToDword_add_byteOffset (BitVec.ofNat 64 (dword+i))
  rw [arm_byte_offset dword i aligned small] at split
  have joined : BitVec.ofNat 64 dword + BitVec.ofNat 64 i = BitVec.ofNat 64 (dword+i) := by
    rw [← BitVec.ofNat_add]
  have eq := congrArg (fun v : Word => v - BitVec.ofNat 64 i) (split.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq

@[simp] theorem arm_mem_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
@[simp] theorem arm_getMem_set_reg (s : MachineState) (r : Reg) (v : Word) (a : Word) :
    (s.setReg r v).getMem a = s.getMem a := by cases r <;> rfl
@[simp] theorem arm_pc_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).pc = s.pc := by
  cases r <;> rfl
@[simp] theorem arm_getReg_set_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
@[simp] theorem arm_pc_set_pc (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
@[simp] theorem arm_getMem_set_pc (s : MachineState) (v : Word) (a : Word) : (s.setPC v).getMem a = s.getMem a := rfl

/-! ### The four-word mask `lhu x31,o(r); slli x31,x31,50; srli x31,x31,50; sw x31,o(r)` -/

def maskAfter (s : MachineState) (r : Reg) (o : BitVec 12) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.LHU .x31 r o)) (.SLLI .x31 .x31 50))
    (.SRLI .x31 .x31 50)) (.SW r .x31 o)

/-- What the mask leaves: the doubleword at `dword` keeps its low 46 bits; only `x31` and the pc change. -/
structure MaskPost (s t : MachineState) (dword : Nat) : Prop where
  pc : t.pc = s.pc + 16
  regs : ∀ q, q ≠ .x31 → t.getReg q = s.getReg q
  word : t.getMem (BitVec.ofNat 64 dword) = (s.getMem (BitVec.ofNat 64 dword) <<< 18) >>> 18
  other : ∀ a, a ≠ BitVec.ofNat 64 dword → t.getMem a = s.getMem a

theorem mask_post (s : MachineState) (r : Reg) (o : BitVec 12) (dword : Nat)
    (address : s.getReg r + signExtend12 o = BitVec.ofNat 64 (dword+4))
    (aligned : dword % 8 = 0) (keep : r ≠ .x31) :
    MaskPost s (maskAfter s r o) dword := by
  have al := arm_align dword 4 aligned (by decide)
  have off := arm_byte_offset dword 4 aligned (by decide)
  let s1 := execInstrBr s (.LHU .x31 r o)
  let s2 := execInstrBr s1 (.SLLI .x31 .x31 50)
  let s3 := execInstrBr s2 (.SRLI .x31 .x31 50)
  have m3 : ∀ a, s3.getMem a = s.getMem a := fun a => rfl
  have r3 : ∀ q, q ≠ .x31 → s3.getReg q = s.getReg q := by
    intro q hq
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)]
  have v3 : s3.getReg .x31 =
      (((s.getHalfword (BitVec.ofNat 64 (dword+4))).zeroExtend 64) <<< 50) >>> 50 := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31 ≠ .x0 by decide), address]
    rfl
  have pc3 : s3.pc = s.pc + 4 + 4 + 4 := rfl
  have last : maskAfter s r o =
      (s3.setWord32 (BitVec.ofNat 64 (dword+4)) ((s3.getReg .x31).truncate 32)).setPC (s3.pc + 4) := by
    show (s3.setWord32 (s3.getReg r + signExtend12 o) ((s3.getReg .x31).truncate 32)).setPC (s3.pc + 4) = _
    rw [r3 r keep, address]
  have stored : s3.setWord32 (BitVec.ofNat 64 (dword+4)) ((s3.getReg .x31).truncate 32) =
      s3.setMem (BitVec.ofNat 64 dword)
        (replaceWord32 (s.getMem (BitVec.ofNat 64 dword)) 1 ((s3.getReg .x31).truncate 32)) := by
    simp only [MachineState.setWord32, al, off, m3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [last]
    show s3.pc + 4 = s.pc + 16
    rw [pc3, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
    rfl
  · intro q hq
    rw [last, stored, MachineState.getReg_setPC, arm_getReg_set_mem]
    exact r3 q hq
  · rw [last, stored, arm_getMem_set_pc, MachineState.getMem_setMem_eq, v3, MachineState.getHalfword, al, off]
    exact mask_word _
  · intro a ha
    rw [last, stored, arm_getMem_set_pc, MachineState.getMem_setMem_ne ha]
    exact m3 a

theorem execute_mask (s : MachineState) (w : Nat) (r : Reg) (o : BitVec 12) (dword : Nat)
    (bound : w + 4 ≤ 705) (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (c0 : (packedImage.code[w]?).bind decodeInstruction = some (.base (.LHU .x31 r o)))
    (c1 : (packedImage.code[w+1]?).bind decodeInstruction = some (.base (.SLLI .x31 .x31 50)))
    (c2 : (packedImage.code[w+2]?).bind decodeInstruction = some (.base (.SRLI .x31 .x31 50)))
    (c3 : (packedImage.code[w+3]?).bind decodeInstruction = some (.base (.SW r .x31 o)))
    (address : s.getReg r + signExtend12 o = BitVec.ofNat 64 (dword+4))
    (aligned : dword % 8 = 0) (room : dword + 8 ≤ MEMORY_BYTES) (keep : r ≠ .x31) :
    GroupHop s (maskAfter s r o) 4 := by
  let s1 := execInstrBr s (.LHU .x31 r o)
  let s2 := execInstrBr s1 (.SLLI .x31 .x31 50)
  let s3 := execInstrBr s2 (.SRLI .x31 .x31 50)
  have p1 : s1.pc = BitVec.ofNat 64 (4096+4*(w+1)) := pc_next pc rfl
  have p2 : s2.pc = BitVec.ofNat 64 (4096+4*(w+1+1)) := pc_next p1 rfl
  have p3 : s3.pc = BitVec.ofNat 64 (4096+4*(w+1+1+1)) := pc_next p2 rfl
  have r3 : s3.getReg r = s.getReg r := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm keep)]
  have h0 := arm_hop s w _ (by omega) pc c0
    (lhu_step s .x31 r o (by rw [address]; exact access_ofNat _ 2 (by omega) (by omega))) rfl
  have h1 := arm_hop s1 (w+1) _ (by omega) p1 c1 rfl rfl
  have h2 := arm_hop s2 (w+1+1) _ (by omega) p2 c2 rfl rfl
  have h3 := arm_hop s3 (w+1+1+1) _ (by omega) p3 c3
    (sw_step s3 r .x31 o (by rw [r3, address]; exact access_ofNat _ 4 (by omega) (by omega))) rfl
  exact ((h0.thenDo h1).thenDo h2).thenDo h3

/-! ### The seven-slot gather of the last packed sibling's top bits

With `base = P` at the last slot of a packed block (`P = slot 0 + 210`), slot `j`'s bits `238..239` sit in
bits `14..15` of the halfword at `P - 182 + 30 j`. The gather is `lhu x31,-182(base); srli x31,x31,14` and, for
`j = 1..6`, `lhu tmp,(-182+30j)(base); srli tmp,tmp,14; slli tmp,tmp,2j; or x31,x31,tmp`. -/

def gatherOff (j : Nat) : BitVec 12 := BitVec.ofNat 12 (3914+30*j)

/-- The halfword holding bits `224..239` of slot `j`. -/
def spareHalf (s : MachineState) (P j : Nat) : BitVec 16 := s.getHalfword (BitVec.ofNat 64 (P-182+30*j))

theorem gather_offset (P j : Nat) (small : j ≤ 6) (room : 182 ≤ P) :
    BitVec.ofNat 64 P + signExtend12 (gatherOff j) = BitVec.ofNat 64 (P-182+30*j) := by
  have ext : signExtend12 (gatherOff j) = BitVec.ofNat 64 (18446744073709551434+30*j) := by
    interval_cases j <;> rfl
  rw [ext, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

def gatherStart (s : MachineState) (base : Reg) : MachineState :=
  execInstrBr (execInstrBr s (.LHU .x31 base (gatherOff 0))) (.SRLI .x31 .x31 14)

def chunkAfter (s : MachineState) (base tmp : Reg) (j : Nat) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.LHU tmp base (gatherOff j)))
    (.SRLI tmp tmp 14)) (.SLLI tmp tmp (BitVec.ofNat 6 (2*j)))) (.OR .x31 .x31 tmp)

theorem gather_start_post (s : MachineState) (base : Reg) (P : Nat)
    (baseReg : s.getReg base = BitVec.ofNat 64 P) (room : 182 ≤ P) :
    let t := gatherStart s base
    t.pc = s.pc + 4 + 4 ∧ (∀ a, t.getMem a = s.getMem a) ∧ (∀ q, q ≠ .x31 → t.getReg q = s.getReg q) ∧
      t.getReg .x31 = (spareHalf s P 0).zeroExtend 64 >>> 14 := by
  have addr := gather_offset P 0 (by decide) room
  refine ⟨rfl, fun a => rfl, ?_, ?_⟩
  · intro q hq
    simp only [gatherStart, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)]
  · simp only [gatherStart, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31 ≠ .x0 by decide), baseReg, addr, spareHalf]
    rfl

theorem chunk_post (s : MachineState) (base tmp : Reg) (j P : Nat)
    (baseReg : s.getReg base = BitVec.ofNat 64 P) (small : j ≤ 6) (room : 182 ≤ P)
    (t31 : tmp ≠ .x31) (t0 : tmp ≠ .x0) :
    let t := chunkAfter s base tmp j
    t.pc = s.pc + 4 + 4 + 4 + 4 ∧ (∀ a, t.getMem a = s.getMem a) ∧
      (∀ q, q ≠ .x31 → q ≠ tmp → t.getReg q = s.getReg q) ∧
      t.getReg .x31 = s.getReg .x31 ||| (((spareHalf s P j).zeroExtend 64 >>> 14) <<< (2*j)) := by
  have addr := gather_offset P j small room
  have shift : (BitVec.ofNat 6 (2*j)).toNat = 2*j := by
    rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, fun a => by simp only [chunkAfter, execInstrBr, arm_getMem_set_pc, arm_getMem_set_reg], ?_, ?_⟩
  · intro q a b
    simp only [chunkAfter, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]
  · simp only [chunkAfter, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31 ≠ .x0 by decide), MachineState.getReg_setReg_eq t0,
      MachineState.getReg_setReg_ne _ _ _ _ t31, baseReg, addr, spareHalf, shift]
    rfl

theorem execute_gather_start (s : MachineState) (w : Nat) (base : Reg) (P : Nat)
    (bound : w + 2 ≤ 705) (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (c0 : (packedImage.code[w]?).bind decodeInstruction = some (.base (.LHU .x31 base (gatherOff 0))))
    (c1 : (packedImage.code[w+1]?).bind decodeInstruction = some (.base (.SRLI .x31 .x31 14)))
    (baseReg : s.getReg base = BitVec.ofNat 64 P) (room : 182 ≤ P) (even : P % 2 = 0)
    (fits : P ≤ MEMORY_BYTES) :
    GroupHop s (gatherStart s base) 2 := by
  have addr := gather_offset P 0 (by decide) room
  let s1 := execInstrBr s (.LHU .x31 base (gatherOff 0))
  have p1 : s1.pc = BitVec.ofNat 64 (4096+4*(w+1)) := pc_next pc rfl
  have h0 := arm_hop s w _ (by omega) pc c0
    (lhu_step s .x31 base _ (by rw [baseReg, addr]; exact access_ofNat _ 2 (by omega) (by omega))) rfl
  have h1 := arm_hop s1 (w+1) _ (by omega) p1 c1 rfl rfl
  exact h0.thenDo h1

theorem execute_chunk (s : MachineState) (w : Nat) (base tmp : Reg) (j P : Nat)
    (bound : w + 4 ≤ 705) (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (c0 : (packedImage.code[w]?).bind decodeInstruction = some (.base (.LHU tmp base (gatherOff j))))
    (c1 : (packedImage.code[w+1]?).bind decodeInstruction = some (.base (.SRLI tmp tmp 14)))
    (c2 : (packedImage.code[w+2]?).bind decodeInstruction = some (.base (.SLLI tmp tmp (BitVec.ofNat 6 (2*j)))))
    (c3 : (packedImage.code[w+3]?).bind decodeInstruction = some (.base (.OR .x31 .x31 tmp)))
    (baseReg : s.getReg base = BitVec.ofNat 64 P) (small : j ≤ 6) (room : 182 ≤ P) (even : P % 2 = 0)
    (fits : P ≤ MEMORY_BYTES) :
    GroupHop s (chunkAfter s base tmp j) 4 := by
  have addr := gather_offset P j small room
  let s1 := execInstrBr s (.LHU tmp base (gatherOff j))
  let s2 := execInstrBr s1 (.SRLI tmp tmp 14)
  let s3 := execInstrBr s2 (.SLLI tmp tmp (BitVec.ofNat 6 (2*j)))
  have p1 : s1.pc = BitVec.ofNat 64 (4096+4*(w+1)) := pc_next pc rfl
  have p2 : s2.pc = BitVec.ofNat 64 (4096+4*(w+1+1)) := pc_next p1 rfl
  have p3 : s3.pc = BitVec.ofNat 64 (4096+4*(w+1+1+1)) := pc_next p2 rfl
  have h0 := arm_hop s w _ (by omega) pc c0
    (lhu_step s tmp base _ (by rw [baseReg, addr]; exact access_ofNat _ 2 (by omega) (by omega))) rfl
  have h1 := arm_hop s1 (w+1) _ (by omega) p1 c1 rfl rfl
  have h2 := arm_hop s2 (w+1+1) _ (by omega) p2 c2 rfl rfl
  have h3 := arm_hop s3 (w+1+1+1) _ (by omega) p3 c3 rfl rfl
  exact ((h0.thenDo h1).thenDo h2).thenDo h3

/-- The gathered value: bit pair `j` of the result is bits `14..15` of halfword `j`. -/
theorem gather_bits (h0 h1 h2 h3 h4 h5 h6 : BitVec 16) :
    ((((((h0.zeroExtend 64 >>> 14) ||| ((h1.zeroExtend 64 >>> 14) <<< (2*1))) |||
      ((h2.zeroExtend 64 >>> 14) <<< (2*2))) ||| ((h3.zeroExtend 64 >>> 14) <<< (2*3))) |||
      ((h4.zeroExtend 64 >>> 14) <<< (2*4))) ||| ((h5.zeroExtend 64 >>> 14) <<< (2*5))) |||
      ((h6.zeroExtend 64 >>> 14) <<< (2*6)) =
    (h6.extractLsb' 14 2 ++ h5.extractLsb' 14 2 ++ h4.extractLsb' 14 2 ++ h3.extractLsb' 14 2 ++
      h2.extractLsb' 14 2 ++ h1.extractLsb' 14 2 ++ h0.extractLsb' 14 2).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.zeroExtend, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;> simp

/-- Bits `14..15` of the halfword at byte 28 of a 30-byte slot are the slot's bits `238..239`. -/
theorem half_spare (s : MachineState) (q : Nat) (even : q % 2 = 0) (fits : q + 30 ≤ MEMORY_BYTES) :
    (s.getHalfword (BitVec.ofNat 64 (q+28))).extractLsb' 14 2 = (readBuffer s q 30).extractLsb' 238 2 := by
  have lim : MEMORY_BYTES < 2^64 := by decide
  have byte := read_buffer_byte s q 30 29 (by decide)
  have slice : (readBuffer s q 30).extractLsb' 238 2 = ((readBuffer s q 30).extractLsb' (8*29) 8).extractLsb' 6 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [BitVec.getLsbD_extractLsb']
  rw [slice, byte]
  have small : (q+28)%8 < 7 := by omega
  have eLow : BitVec.ofNat 64 (q+28) = BitVec.ofNat 64 (8*((q+28)/8) + (q+28)%8) := congrArg _ (by omega)
  have eHigh : BitVec.ofNat 64 (q+29) = BitVec.ofNat 64 (8*((q+28)/8) + ((q+28)%8+1)) := congrArg _ (by omega)
  have lowAl : alignToDword (BitVec.ofNat 64 (q+28)) = BitVec.ofNat 64 (8*((q+28)/8)) := by
    rw [eLow]; exact arm_align (8*((q+28)/8)) ((q+28)%8) (by omega) (by omega)
  have highAl : alignToDword (BitVec.ofNat 64 (q+29)) = BitVec.ofNat 64 (8*((q+28)/8)) := by
    rw [eHigh]; exact arm_align (8*((q+28)/8)) ((q+28)%8+1) (by omega) (by omega)
  have lowOff : byteOffset (BitVec.ofNat 64 (q+28)) = (q+28)%8 := by
    rw [eLow]; exact arm_byte_offset (8*((q+28)/8)) ((q+28)%8) (by omega) (by omega)
  have highOff : byteOffset (BitVec.ofNat 64 (q+29)) = (q+28)%8+1 := by
    rw [eHigh]; exact arm_byte_offset (8*((q+28)/8)) ((q+28)%8+1) (by omega) (by omega)
  have loaded := ProjectedHalfword.load_byte s (BitVec.ofNat 64 (q+28)) (BitVec.ofNat 64 (q+29))
    (by rw [lowAl, highAl]) (by rw [lowOff, highOff]; omega)
  rw [highOff, show ((q+28)%8+1)%2 = 1 by omega] at loaded
  rw [← loaded]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

end TwoPermutationPrototype.Packed.Checker
