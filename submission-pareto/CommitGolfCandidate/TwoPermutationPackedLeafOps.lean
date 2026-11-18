import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.TwoPermutationLeafRun
import CommitGolfCandidate.TwoPermutationOpeningCopy

/-! Leaf instruction words of the 4096-leaf commit body. The nonce loads and the heap-slot
address use signed 12-bit displacements measured from base registers that point 2048 bytes
into the current 256-nonce block and 128-slot heap block, so each base register is advanced
half as often as with nonnegative displacements. -/
namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 950000

/-- Signed displacement of the first nonce word: `16*(slot%256) - 2048`. -/
def nonceImm (slot : Nat) : BitVec 12 := BitVec.ofNat 12 (16*(slot%256)+2048)
/-- Signed displacement of the second nonce word: `16*(slot%256) - 2040`. -/
def nonceImm8 (slot : Nat) : BitVec 12 := BitVec.ofNat 12 (16*(slot%256)+2056)
/-- Signed displacement of the heap slot: `32*(slot%128) - 2048`. -/
def heapImm (slot : Nat) : BitVec 12 := BitVec.ofNat 12 (32*(slot%128)+2048)

def firstInstructions (_slot : Fin 4096) : List Instr := [.ADDI .x12 .x10 4064]
def secondInstructions (slot : Fin 4096) : List Instr :=
  [.ADDI .x10 .x10 56,.SD .x10 .x10 0,
   .LD .x31 .x22 (nonceImm slot.val),.SD .x10 .x31 8,
   .LD .x31 .x22 (nonceImm8 slot.val),.SD .x10 .x31 16,
   .ADDI .x12 .x20 (heapImm slot.val)]

def leafInstructions (slot : Fin 4096) : List Instr :=
  firstInstructions slot ++ [.ECALL] ++ secondInstructions slot ++ [.ECALL,.ADDI .x10 .x10 200]

private theorem nonce_disp_table : ∀ k : Fin 256,
    signExtend12 (BitVec.ofNat 12 (16*k.val+2048)) + 2048#64 = BitVec.ofNat 64 (16*k.val) ∧
    signExtend12 (BitVec.ofNat 12 (16*k.val+2056)) + 2048#64 = BitVec.ofNat 64 (16*k.val+8) ∧
    signExtend12 (BitVec.ofNat 12 (16*k.val+2056)) = signExtend12 (BitVec.ofNat 12 (16*k.val+2048)) + 8 := by
  decide

/-- The two nonce displacements, measured from the shifted base. -/
theorem nonce_disp (slot : Nat) :
    signExtend12 (nonceImm slot) + 2048#64 = BitVec.ofNat 64 (16*(slot%256)) ∧
    signExtend12 (nonceImm8 slot) + 2048#64 = BitVec.ofNat 64 (16*(slot%256)+8) ∧
    signExtend12 (nonceImm8 slot) = signExtend12 (nonceImm slot) + 8 :=
  nonce_disp_table ⟨slot%256, Nat.mod_lt _ (by decide)⟩

private theorem heap_disp_table : ∀ k : Fin 128,
    signExtend12 (BitVec.ofNat 12 (32*k.val+2048)) + 2048#64 = BitVec.ofNat 64 (32*k.val) := by decide

/-- The heap displacement, measured from the shifted base. -/
theorem heap_disp (slot : Nat) :
    signExtend12 (heapImm slot) + 2048#64 = BitVec.ofNat 64 (32*(slot%128)) :=
  heap_disp_table ⟨slot%128, Nat.mod_lt _ (by decide)⟩

private theorem shift_words : wordAddress 256 = 2048#64 := rfl

private theorem word_offset (b n m : Nat) (h : 8*n=m) :
    wordAddress (b+n) = wordAddress b + BitVec.ofNat 64 m := by
  rw [wordAddress_add]; unfold wordAddress; rw [h]

/-- A shifted base plus a signed displacement names the word `base + 2*(slot%256)`. -/
theorem shifted_nonce_address (base slot : Nat) :
    wordAddress (base+256) + signExtend12 (nonceImm slot) = wordAddress (base+2*(slot%256)) ∧
    wordAddress (base+256) + signExtend12 (nonceImm8 slot) = wordAddress (base+2*(slot%256)+1) := by
  have d := nonce_disp slot
  constructor
  · rw [wordAddress_add,shift_words,BitVec.add_assoc,BitVec.add_comm 2048#64,d.1,
      word_offset base (2*(slot%256)) (16*(slot%256)) (by omega)]
  · rw [wordAddress_add,shift_words,BitVec.add_assoc,BitVec.add_comm 2048#64,d.2.1,Nat.add_assoc,
      word_offset base (2*(slot%256)+1) (16*(slot%256)+8) (by omega)]

/-- A shifted heap base plus a signed displacement names the slot `base + 4*(slot%128)`. -/
theorem shifted_heap_address (base slot : Nat) :
    wordAddress (base+256) + signExtend12 (heapImm slot) = wordAddress (base+4*(slot%128)) := by
  rw [wordAddress_add,shift_words,BitVec.add_assoc,BitVec.add_comm 2048#64,heap_disp,
    word_offset base (4*(slot%128)) (32*(slot%128)) (by omega)]

def nonceWords (state : MachineState) (slot : Fin 4096) : Words 2 := fun i =>
  if i.val=0 then state.getMem (state.getReg .x22+signExtend12 (nonceImm slot.val))
  else state.getMem (state.getReg .x22+signExtend12 (nonceImm8 slot.val))

def secondMemory (s : MachineState) (slot : Fin 4096) : MachineState :=
  let tag := s.getReg .x10+56
  ((s.setMem tag tag).setMem (tag+8) (nonceWords s slot 0)).setMem (tag+16) (nonceWords s slot 1)

def preparedA (s : MachineState) (slot : Fin 4096) := (firstInstructions slot).foldl execInstrBr s
def repliedA (s : MachineState) (slot : Fin 4096) (start : Nat) (answer : BitVec 1600) :=
  writeBits (preparedA s slot) (wordAddress (start+1)) answer
def preparedB (s : MachineState) (slot : Fin 4096) (start : Nat) (a : BitVec 1600) :=
  (secondInstructions slot).foldl execInstrBr (repliedA s slot start a)
def repliedB (s : MachineState) (slot : Fin 4096) (start dst : Nat) (a b : BitVec 1600) :=
  writeBits (preparedB s slot start a) (wordAddress dst) b
def finishedLeaf (s : MachineState) (slot : Fin 4096) (start dst : Nat) (a b : BitVec 1600) :=
  execInstrBr (repliedB s slot start dst a b) (.ADDI .x10 .x10 200)

theorem first_execution (s : MachineState) (slot : Fin 4096) :
    let before := preparedA s slot
    before.mem=s.mem ∧ before.getReg .x10=s.getReg .x10 ∧ before.getReg .x12=s.getReg .x10+signExtend12 4064 ∧
    before.pc=s.pc+4 := ⟨rfl,rfl,rfl,rfl⟩

theorem first_keeps (s : MachineState) (slot : Fin 4096) (r : Reg) (p : r≠.x10) (q : r≠.x12) :
    (preparedA s slot).getReg r=s.getReg r := by
  simp only [preparedA,firstInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm q)]

private theorem store_regs (s : MachineState) (addr val : Word) (r : Reg) : (s.setMem addr val).getReg r=s.getReg r := by cases r <;> rfl

def StampSeparate (s : MachineState) (slot : Fin 4096) : Prop :=
  let base := s.getReg .x10+56
  let salt := s.getReg .x22+signExtend12 (nonceImm slot.val)
  salt≠base ∧ salt+8≠base ∧ salt+8≠base+8

theorem second_execution (s : MachineState) (slot : Fin 4096) (apart : StampSeparate s slot) :
    let before := (secondInstructions slot).foldl execInstrBr s
    before.mem=(secondMemory s slot).mem ∧ before.getReg .x10=s.getReg .x10+56 ∧
    before.getReg .x12=s.getReg .x20+signExtend12 (heapImm slot.val) ∧ before.pc=s.pc+28 := by
  have ⟨d0,e0,e1⟩ := apart
  have add8 : s.getReg .x22+signExtend12 (nonceImm8 slot.val)=
      (s.getReg .x22+signExtend12 (nonceImm slot.val))+8 := by
    rw [(nonce_disp slot.val).2.2,BitVec.add_assoc]
  simp only [secondInstructions,secondMemory,List.foldl_cons,List.foldl_nil,execInstrBr,
    show signExtend12 56=56#64 by decide, show signExtend12 0=0#64 by decide,
    show signExtend12 8=8#64 by decide, show signExtend12 16=16#64 by decide,
    MachineState.getReg_setPC,store_regs,Opening.getReg_setReg,
    MachineState.getMem_setPC,MachineState.getMem_setReg]
  simp [MachineState.setReg,MachineState.setMem,MachineState.setPC,MachineState.getMem,nonceWords,add8,
    BitVec.add_assoc] at *
  simp only [ite_eq_right d0,ite_eq_right e0,ite_eq_right e1]

theorem second_keeps (s : MachineState) (slot : Fin 4096) (r : Reg) (a : r≠.x10) (b : r≠.x12) (c : r≠.x31) :
    ((secondInstructions slot).foldl execInstrBr s).getReg r=s.getReg r := by
  simp only [secondInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,store_regs,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]

end TwoPermutationPrototype.RV64.PackedLeaves
