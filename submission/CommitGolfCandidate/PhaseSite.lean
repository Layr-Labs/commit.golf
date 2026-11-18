import CommitGolfCandidate.PhaseField
import CommitGolfCandidate.GroupOpenCopy

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open GroupedOpening (CopySite FieldInputs)
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000

def oldSite (f : Fin 18) : CopySite :=
  if z : f.val=0 then .nonce
  else if h : f.val<4 then .quartet ⟨f.val-1,by omega⟩
  else if k : f.val=4 then .firstSibling else .sibling ⟨f.val-5,by omega⟩

theorem old_matches : ∀ f : Fin 18, (oldSite f).source=srcReg f ∧
    (oldSite f).destOffset=storeOffset f ∧ 2*(oldSite f).halfwords=fieldSize f := by decide

structure Audited (p : Fin 4) (f : Fin 18) : Prop where
  cover : (widths p f).sum=fieldSize f
  chunk : ∀ j (inside : j<(widths p f).length),
    let w := (widths p f)[j]
    let off := chunkOffset p f j
    (w=2 ∨ w=4 ∨ w=8) ∧ off%w=0 ∧ (6*p.val+fieldOffset f+off)%w=0 ∧
    off+w≤fieldSize f ∧
    decodeAt (fieldPC p f+2*j)=some (loadWidth w f off) ∧
    decodeAt (fieldPC p f+2*j+1)=some (saveWidth w (storeOffset f+off))

theorem audited (p : Fin 4) (f : Fin 18) : Audited p f := by
  have a := every_field_decodes p f
  simp only [auditField,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at a
  refine ⟨a.1,?_⟩
  intro j inside
  have b:=a.2 j (List.mem_range.mpr inside)
  simp only [List.getElem?_eq_getElem inside,Option.getD_some,Bool.or_eq_true,beq_iff_eq,
    decide_eq_true_eq] at b
  simpa only [and_assoc,or_assoc,or_left_comm,or_comm] using b

private theorem valid_of (ws : List Nat) (sa da : Nat)
    (all : ∀ j (inside : j<ws.length),
      let w:=ws[j]
      (w=2 ∨ w=4 ∨ w=8) ∧ (sa+(ws.take j).sum)%w=0 ∧ (da+(ws.take j).sum)%w=0) :
    ValidMoves ws sa da := by
  induction ws generalizing sa da with
  | nil => trivial
  | cons w ws ih =>
    have first:=all 0 (by simp)
    simp only [List.getElem_cons_zero,List.take_zero,List.sum_nil,Nat.add_zero] at first
    refine ⟨first.1,first.2.1,first.2.2,ih _ _ ?_⟩
    intro j inside
    have h:=all (j+1) (by simpa using inside)
    simpa only [List.getElem_cons_succ,List.take_succ_cons,List.sum_cons,Nat.add_assoc] using h

def fieldAddress (p : Fin 4) (f : Fin 18) := addr (4096+4*fieldPC p f)

structure FieldState (im : Image) (p : Fin 4) (f : Fin 18) (s : MachineState) (src dst : Nat) : Prop where
  pc : s.pc=fieldAddress p f
  source : s.getReg (srcReg f)=addr src
  target : s.getReg .x21+addr (storeOffset f)=addr dst
  sourceAligned : src%8=0
  targetAligned : dst%8=(6*p.val+fieldOffset f)%8
  apart : src+fieldSize f≤dst
  fits : dst+fieldSize f≤MEMORY_BYTES
  fetched : ∀ (pc : Nat) (op : Instr), fieldPC p f≤pc → pc<fieldPC p f+2*(widths p f).length →
    decodeAt pc=some op → ∀ v : MachineState, v.pc=addr (4096+4*pc) → fetch im v=some (.base op)

theorem field_valid {im : Image} {p f} {s : MachineState} {src dst : Nat}
    (input : FieldState im p f s src dst) : ValidMoves (widths p f) src dst := by
  apply valid_of
  intro j inside
  obtain ⟨w,a,b,_,_,_⟩ := (audited p f).chunk j inside
  have sa:=input.sourceAligned
  have da:=input.targetAligned
  change _ ∧ (src+chunkOffset p f j)%_=0 ∧ (dst+chunkOffset p f j)%_=0
  refine ⟨w,?_⟩
  rcases w with eq|eq|eq <;> rw [eq] at a b ⊢ <;> omega

theorem field_run {im : Image} {p f} {s : MachineState} {src dst : Nat} (input : FieldState im p f s src dst) :
    PairRun im s (moveList (widths p f) s src dst) (2*(widths p f).length) := by
  let ws:=widths p f
  have facts:=audited p f
  have total:=facts.cover
  have fit:=input.fits
  have apart:=input.apart
  have small : ∀ x : Fin 18, storeOffset x+fieldSize x≤128 := by decide
  apply moveList_run im f s ws src dst 0 (storeOffset f) (field_valid input)
  · exact ⟨by dsimp [ws];omega,by simpa only [ws,total] using fit⟩
  · have :=small f;dsimp [ws];omega
  · simpa [addr] using input.source
  · exact input.target
  · intro j inside u
    obtain ⟨_,_,_,_,load,save⟩:=facts.chunk j inside
    have add_addr (a b : Nat) : addr (a+b)=addr a+addr b := BitVec.ofNat_add ..
    constructor
    · intro h
      apply input.fetched (fieldPC p f+2*j) _ (by omega) (by dsimp [ws] at inside;omega)
      · simpa [chunkOffset,ws] using load
      · rw [h,input.pc,fieldAddress,←add_addr]
        congr 1 <;> omega
    · intro h
      apply input.fetched (fieldPC p f+2*j+1) _ (by omega) (by dsimp [ws] at inside;omega)
      · exact save
      · rw [h,input.pc,fieldAddress,←add_addr]
        congr 1 <;> omega

theorem field_memory {im : Image} {p f} {s : MachineState} {src dst : Nat}
    (input : FieldState im p f s src dst) :
    (moveList (widths p f) s src dst).mem =
       (ProjectedHalfword.copyLoopMemory false (oldSite f).halfwords s (addr src) (addr dst)).mem := by
  have size:=(old_matches f).2.2
  have total:=(audited p f).cover
  have fits:=input.fits
  have apart:=input.apart
  have limit : MEMORY_BYTES≤2^64 := by decide
  have count : (widths p f).sum/2=(oldSite f).halfwords := by omega
  simpa only [count] using moveList_memory (widths p f) s src dst (field_valid input) (by omega) (by omega)

#print axioms field_run
#print axioms field_memory
end TwoPermutationPrototype.PhaseOpening
