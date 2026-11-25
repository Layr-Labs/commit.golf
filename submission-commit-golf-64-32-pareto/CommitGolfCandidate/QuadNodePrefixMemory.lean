import CommitGolfCandidate.QuadNodeBlock
import CommitGolfCandidate.TwoPermutationQuadSpec

/-! Exact memory contents of the quad prefix: nine zero words and the opened
four-word digest, before the three rotated sibling copies. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
@[local simp] private theorem prefix_getMem_setPC (s : MachineState) (pc q : Word) : (s.setPC pc).getMem q=s.getMem q := rfl
@[local simp] private theorem prefix_getMem_setReg (s : MachineState) (r : Reg) (v q : Word) : (s.setReg r v).getMem q=s.getMem q := by cases r <;> rfl
@[local simp] private theorem prefix_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

theorem quad_prefix_workspace_word (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) (i : Fin 25) :
    memoryView (quadPrefix s 22) (1600+i.val) =
      if i.val<9 then 0 else
      if (i.val-9)/4=slot.val then memoryView s (1536+(i.val-9)%4)
      else memoryView s (1600+i.val) := by
  fin_cases slot <;> fin_cases i <;>
    simp [quadPrefix,quadPrefixCode,execInstrBr,signExtend12,pair,digest,opened,
      memoryView,wordAddress]

/-- Workspace preparation preserves every word outside its 200-byte window. -/
theorem quad_prefix_word_frame (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) (q : Word)
    (outside : ∀ j : Fin 25, q≠wordAddress (1600+j.val)) :
    (quadPrefix s 22).getMem q=s.getMem q := by
  simp only [Fin.forall_fin_succ,Fin.val_zero,Fin.val_succ,Nat.zero_add] at outside
  fin_cases slot <;>
    simp_all [quadPrefix,quadPrefixCode,execInstrBr,signExtend12,wordAddress]

/-- The opened digest occupies its original slot after the zero-prefix setup. -/
theorem quad_prefix_opened (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) :
    readBuffer (quadPrefix s 22) (12872+32*slot.val) 32=readBuffer s 12288 32 := by
  apply (read_digest_eq_iff _ _ _ _ (by omega) (by decide)).mpr
  intro i inside
  have v := quad_prefix_workspace_word s slot pair digest opened ⟨9+4*slot.val+i,by have := slot.isLt; omega⟩
  dsimp only [Fin.val_mk] at v
  change memoryView (quadPrefix s 22) (1600+(9+4*slot.val+i)) = _ at v
  have div : (9+4*slot.val+i-9)/4=slot.val := by omega
  have rem : (9+4*slot.val+i-9)%4=i := by omega
  rw [ite_eq_right (by omega),div,ite_eq_left rfl,rem] at v
  simpa only [memoryView,wordAddress,show 8*(1600+(9+4*slot.val+i))=12872+32*slot.val+8*i by omega,
    show 8*(1536+i)=12288+8*i by omega] using v

/-- Exactly the first 72 workspace bytes are cleared. -/
theorem quad_prefix_zero_byte (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) (i : Nat) (inside : i<72) :
    (quadPrefix s 22).getByte (BitVec.ofNat 64 (12800+i))=0 := by
  have w := quad_prefix_workspace_word s slot pair digest opened ⟨i/8,by omega⟩
  dsimp only [Fin.val_mk] at w
  rw [ite_eq_left (by omega)] at w
  have split : 12800+i=8*(1600+i/8)+i%8 := by omega
  rw [split,aligned_byte _ _ _ (by omega)]
  simp only [Nat.div_eq_of_lt (show i%8<8 by omega),Nat.mul_zero,Nat.add_zero]
  change extractByte (memoryView (quadPrefix s 22) (1600+i/8)) (i%8%8)=0
  rw [w]
  simp [extractByte]

/-- Every word above the workspace is preserved, including all proof records. -/
theorem quad_prefix_above (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) (word : Nat)
    (above : 1625≤word) (bounded : word<2^33) :
    memoryView (quadPrefix s 22) word=memoryView s word := by
  apply quad_prefix_word_frame s slot pair digest opened
  intro j eq
  have same := wordAddress_injective_of_bound (by omega : word<2^61)
    (by have := j.isLt; omega : 1600+j.val<2^61) eq
  have := j.isLt
  omega

/-- The nonce and all three sibling source digests survive preparation. -/
theorem quad_prefix_read_above (s : MachineState) (slot : Fin 4)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) (address count : Nat)
    (above : 13000≤address) (room : address+count≤MEMORY_BYTES) :
    readBuffer (quadPrefix s 22) address count=readBuffer s address count := by
  apply TwoPermutationPrototype.Packed.Checker.read_buffer_above s (quadPrefix s 22) address count 1625
    above (by
      have limit : MEMORY_BYTES<2^64 := by decide
      omega)
  intro word lo hi
  by_cases fits : word<2^33
  · exact quad_prefix_above s slot pair digest opened word lo fits
  · apply quad_prefix_word_frame s slot pair digest opened
    intro j eq
    have same := wordAddress_injective_of_bound hi (by have := j.isLt; omega : 1600+j.val<2^61) eq
    have := j.isLt
    omega

end TwoPermutationPrototype.Quad.Checker
