import CommitGolfCandidate.TwoPermutationWideLeafOps

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def nonceWords (s : MachineState) (slot : Fin 256) : Words 2 := fun i =>
  if i.val = 0 then s.getMem (s.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128)))
  else s.getMem (s.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128)+8))

theorem at_salt (s : MachineState) (slot : Fin 256) (salts : Nat)
    (source : s.getReg .x22=wordAddress salts) :
    nonceWords s slot = window (memoryView s) (salts + 2*(slot.val%128)) := by
  funext i
  fin_cases i <;> simp only [nonceWords,window,memoryView,source] <;> dsimp <;>
    congr 1 <;> simp only [wordAddress,←BitVec.ofNat_add] <;> congr 1 <;> omega

theorem first_memory_word (s : MachineState) (slot : Fin 256) (r w : Nat)
    (source : s.getReg .x10=wordAddress (r+12)) (rb : r+12<2^61) (wb : w<2^61) :
    memoryView ((firstInstructions slot).foldl execInstrBr s) w =
      writeWord (memoryView s) (r+12) 0 w := by
  change ((firstInstructions slot).foldl execInstrBr s).mem _ = _
  rw [(first_execution s slot).1]
  change memoryView (s.setMem (s.getReg .x10) 0) w = _
  rw [source]
  exact memory_at_store rb wb

theorem first_call_input (s : MachineState) (slot : Fin 256) (r : Nat)
    (source : s.getReg .x10=wordAddress (r+12)) (rb : r+37<2^61) :
    window (memoryView ((firstInstructions slot).foldl execInstrBr s)) (r+12) =
      Overlap.firstInput (window (memoryView s) (r+13)) := by
  rw [←Overlap.first_window]
  funext i
  exact first_memory_word s slot r _ source (by omega) (by have := i.isLt; omega)

theorem address_plus (a k b : Nat) (same : a+k=b) :
    wordAddress a + BitVec.ofNat 64 (8*k) = wordAddress b := by
  subst b
  exact (wordAddress_add a k).symm

theorem first_dest (start : Nat) (low : 8 ≤ start) :
    wordAddress (start+4) + (-96 : Word) = wordAddress (start-8) := by
  rw [show start+4=start-8+12 by omega,wordAddress_add,BitVec.add_assoc]
  change wordAddress (start-8)+0=_
  exact BitVec.add_zero _

/-- The salt tape is above all three workspace stores. Each load sees the original tape. -/
theorem second_memory_word (s : MachineState) (slot : Fin 256) (r salts w : Nat)
    (source : s.getReg .x10=wordAddress (r+12)) (tape : s.getReg .x22=wordAddress salts)
    (sep : r+27 ≤ salts) (bound : salts+256≤2^33) (wb : w<2^61) :
    memoryView (secondMemory s slot) w =
      writeWord (writeWord (writeWord (memoryView s) (r+20) (wordAddress (r+20)))
        (r+25) ((nonceWords s slot) 0)) (r+26) ((nonceWords s slot) 1) w := by
  let a := salts + 2*(slot.val%128)
  have sb : a+1<2^61 := by dsimp [a];omega
  have wa : s.getReg .x10+64=wordAddress (r+20) := by rw [source];exact address_plus _ 8 _ (by omega)
  have a₀ : s.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128))=wordAddress a := by
    rw [tape];unfold wordAddress a;rw [←BitVec.ofNat_add];congr 1;omega
  have a₁ : s.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128)+8)=wordAddress (a+1) := by
    rw [tape];unfold wordAddress a;rw [←BitVec.ofNat_add];congr 1;omega
  have d₀ : wordAddress a ≠ wordAddress (r+20) := fun h => by
    have e := wordAddress_injective_of_bound (by omega) (by omega) h; dsimp [a] at e;omega
  have d₁ : wordAddress (a+1) ≠ wordAddress (r+20) := fun h => by
    have e := wordAddress_injective_of_bound (by omega) (by omega) h; dsimp [a] at e;omega
  have d₂ : wordAddress (a+1) ≠ wordAddress (r+25) := fun h => by
    have e := wordAddress_injective_of_bound (by omega) (by omega) h; dsimp [a] at e;omega
  have sd₀ : (nonceWords s slot) 0 = s.getMem (wordAddress a) := by change s.getMem _=_;rw [a₀]
  have sd₁ : (nonceWords s slot) 1 = s.getMem (wordAddress (a+1)) := by change s.getMem _=_;rw [a₁]
  have p40 : wordAddress (r+20)+40=wordAddress (r+25) := address_plus _ 5 _ (by omega)
  have p48 : wordAddress (r+20)+48=wordAddress (r+26) := address_plus _ 6 _ (by omega)
  simp only [secondMemory,wa,a₀,a₁,p40,p48,MachineState.getMem_setMem_ne d₀,
    MachineState.getMem_setMem_ne d₁,MachineState.getMem_setMem_ne d₂,sd₀,sd₁]
  rw [memory_at_store (by omega) wb]
  by_cases h26 : w=r+26
  · simp [writeWord,h26]
  · simp only [writeWord,if_neg h26]
    rw [memory_at_store (by omega) wb]
    by_cases h25 : w=r+25
    · simp [writeWord,h25]
    · simp only [writeWord,if_neg h25]
      exact memory_at_store (by omega) wb

end TwoPermutationPrototype.RV64.WideLeaves
