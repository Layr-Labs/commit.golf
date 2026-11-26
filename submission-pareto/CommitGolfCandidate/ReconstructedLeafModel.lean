import CommitGolfCandidate.ReconstructedLeafSteps
import CommitGolfCandidate.ReconstructedLeafMemory
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace CommitGolfCandidate.Reconstruction.LeafModel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 LeafSteps
open TwoPermutationPrototype (window Memory writeWindow writeWord)
open TwoPermutationPrototype.Opening (getReg_setReg getReg_setMem)

structure Model where
  reg : Reg → Word
  mem : Memory

def Model.set (m : Model) (rd : Reg) (v : Word) : Model :=
  {m with reg := fun r => if rd = r ∧ rd ≠ .x0 then v else m.reg r}
def Model.store (m : Model) (w : Nat) (v : Word) := {m with mem := writeWord m.mem w v}
def Model.permute (o : Oracle) (m : Model) (src dst : Nat) :=
  {m with mem := writeWindow m.mem dst (replyWords (o.permutation (packBuffer (window m.mem src))))}

structure Fits (s : MachineState) (m : Model) : Prop where
  registers : ∀ r, s.getReg r = m.reg r
  memory : LeafMemory.Agrees (memoryView s) m.mem

def Contract (o : Oracle) (ops : List Instr) (m n : Model) :=
  ∀ s : MachineState, Fits s m → ∃ t, Run o ops s t ∧ Fits t n

theorem empty (o : Oracle) (m : Model) : Contract o [] m m :=
  fun s fits => ⟨s,.nil _,fits⟩

theorem combine {o a b m n p} (left : Contract o a m n) (right : Contract o b n p) :
    Contract o (a++b) m p := by
  intro s h
  obtain ⟨t,l,ht⟩ := left s h
  obtain ⟨u,r,hu⟩ := right t ht
  exact ⟨u,l.append r,hu⟩

theorem Fits.pc {s : MachineState} {m : Model} (h : Fits s m) (pc : Word) : Fits (s.setPC pc) m :=
  ⟨fun r => (MachineState.getReg_setPC ..).trans (h.registers r),h.memory⟩

theorem Fits.reg {s : MachineState} {m : Model} (h : Fits s m) (rd : Reg) (v : Word) :
    Fits (s.setReg rd v) (m.set rd v) := by
  constructor
  · intro r
    rw [getReg_setReg,h.registers]
    rfl
  · intro w hw
    exact (show memoryView (s.setReg rd v) w = memoryView s w by cases rd <;> rfl).trans (h.memory w hw)

theorem Fits.store {s : MachineState} {m : Model} (h : Fits s m) (w : Nat) (v : Word) (room : w < 2^33) :
    Fits (s.setMem (wordAddress w) v) (m.store w v) :=
  ⟨fun r => (getReg_setMem ..).trans (h.registers r),fun j hj =>
    (memory_at_store (by omega) (by omega)).trans (LeafMemory.write_word h.memory w v j hj)⟩

private theorem word_ok (w : Nat) (room : w < 2^33) : accessValid (wordAddress w) 8 = true := by
  simp [accessValid,rangeValid,MEMORY_BYTES,word_address_value (by omega : w < 2^61)]
  omega

theorem addi (o : Oracle) (m : Model) (rd rs : Reg) (imm : BitVec 12) (v : Word)
    (value : m.reg rs + signExtend12 imm = v) : Contract o [.ADDI rd rs imm] m (m.set rd v) := by
  intro s fits
  let t := (s.setReg rd v).setPC (s.pc+4)
  have step : ordinaryStep s (.base (.ADDI rd rs imm)) = some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,fits.registers,value,t]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.reg rd v).pc _⟩

theorem load (o : Oracle) (m : Model) (rd rs : Reg) (imm : BitVec 12) (w : Nat) (room : w < 2^33)
    (value : m.reg rs + signExtend12 imm = wordAddress w) : Contract o [.LD rd rs imm] m (m.set rd (m.mem w)) := by
  intro s fits
  let t := (s.setReg rd (m.mem w)).setPC (s.pc+4)
  have phys : s.getMem (wordAddress w) = m.mem w := fits.memory w room
  have step : ordinaryStep s (.base (.LD rd rs imm)) = some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fits.registers,value,
      word_ok w room,ite_true,phys,t]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.reg rd (m.mem w)).pc _⟩

theorem store (o : Oracle) (m : Model) (rs rv : Reg) (imm : BitVec 12) (w : Nat) (room : w < 2^33)
    (value : m.reg rs + signExtend12 imm = wordAddress w) : Contract o [.SD rs rv imm] m (m.store w (m.reg rv)) := by
  intro s fits
  let t := (s.setMem (wordAddress w) (m.reg rv)).setPC (s.pc+4)
  have step : ordinaryStep s (.base (.SD rs rv imm)) = some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fits.registers,value,word_ok w room,ite_true,t]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.store w (m.reg rv) room).pc _⟩

private theorem byte_ok (w : Nat) (room : w < 2^33) : accessValid (BitVec.ofNat 64 (8*w+7)) 1 = true := by
  simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 8*w+7 < 2^64 by omega)]
  omega

private theorem half_ok (w : Nat) (room : w < 2^33) : accessValid (BitVec.ofNat 64 (8*w+6)) 2 = true := by
  simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 8*w+6 < 2^64 by omega)]
  omega

theorem clearByte (o : Oracle) (m : Model) (rs : Reg) (imm : BitVec 12) (w : Nat) (room : w < 2^33)
    (addr : m.reg rs + signExtend12 imm = BitVec.ofNat 64 (8*w+7)) :
    Contract o [.SB rs .x0 imm] m (m.store w ((m.mem w) &&& 0x00ffffffffffffff)) := by
  intro s fits
  let t := s.setByte (BitVec.ofNat 64 (8*w+7)) 0
  have step : ordinaryStep s (.base (.SB rs .x0 imm)) = some (t.setPC (s.pc+4)) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,show s.getReg .x0 = 0 from rfl,
      fits.registers,addr,byte_ok w room,ite_true,t]
    rfl
  refine ⟨_,Run.one (.ordinary _ _ _ step rfl),Fits.pc ?_ _⟩
  constructor
  · intro r
    exact (show t.getReg r = s.getReg r by cases r <;> rfl).trans (fits.registers r)
  · intro j hj
    rw [show memoryView t j = _ from CommitWrite.clear_salt_byte s w j (by omega) (by omega),fits.memory w room]
    exact LeafMemory.write_word fits.memory _ _ j hj

theorem markHalf (o : Oracle) (m : Model) (rs rv : Reg) (imm : BitVec 12) (w : Nat) (room : w < 2^33)
    (addr : m.reg rs + signExtend12 imm = BitVec.ofNat 64 (8*w+6)) (ones : m.reg rv = -1) :
    Contract o [.SH rs rv imm] m (m.store w ((m.mem w) ||| 0xffff000000000000)) := by
  intro s fits
  let t := s.setHalfword (BitVec.ofNat 64 (8*w+6)) 65535
  have step : ordinaryStep s (.base (.SH rs rv imm)) = some (t.setPC (s.pc+4)) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fits.registers,addr,ones,
      half_ok w room,ite_true,t]
    rfl
  refine ⟨_,Run.one (.ordinary _ _ _ step rfl),Fits.pc ?_ _⟩
  constructor
  · intro r
    exact (show t.getReg r = s.getReg r by cases r <;> rfl).trans (fits.registers r)
  · intro j hj
    rw [show memoryView t j = _ from CommitWrite.mark_leaf s w j (by omega) (by omega),fits.memory w room]
    exact LeafMemory.write_word fits.memory _ _ j hj

theorem permutation (o : Oracle) (m : Model) (src dst : Nat) (srcRoom : src+25 ≤ 2^33)
    (dstRoom : dst+25 ≤ 2^33) (source : m.reg .x10 = wordAddress src) (out : m.reg .x12 = wordAddress dst)
    (mode : m.reg .x5 = 0) (len : m.reg .x11 = 200) (kind : m.reg .x13 = 1) :
    Contract o [.ECALL] m (m.permute o src dst) := by
  intro s fits
  have call := Step.permute (o := o) s src dst srcRoom dstRoom ((fits.registers _).trans source)
    ((fits.registers _).trans out) ((fits.registers _).trans mode) ((fits.registers _).trans len)
    ((fits.registers _).trans kind)
  refine ⟨_,Run.one call,⟨fun r => (writeBits_register ..).trans (fits.registers r),?_⟩⟩
  intro w hw
  let answer : BitVec 1600 := o.permutation (packBuffer (window (memoryView s) src))
  refine (permutation_write_memory s dst w answer dstRoom hw).trans ?_
  have inputs : (window (memoryView s) src : TwoPermutationPrototype.Words 25) = window m.mem src :=
    LeafMemory.window_congr fits.memory srcRoom
  have physical := LeafMemory.write_window fits.memory dst (replyWords answer) w hw
  refine physical.trans ?_
  unfold Model.permute
  exact congrArg (fun ws : TwoPermutationPrototype.Words 25 =>
    writeWindow m.mem dst (replyWords (o.permutation (packBuffer ws))) w) inputs

end CommitGolfCandidate.Reconstruction.LeafModel
