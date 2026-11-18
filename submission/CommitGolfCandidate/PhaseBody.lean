import CommitGolfCandidate.PhaseCursor
namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate GroupedOpening
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000

def physicalField (p : Fin 4) (f : Fin 18) (i : Index) (o : Nat) (s : MachineState) : MachineState :=
  moveList (widths p f) (straight s (beforeOps f)) (sourceAt i f) (destAt o f)

def fieldCycles (p : Fin 4) (f : Fin 18) : Nat := (beforeOps f).length+2*(widths p f).length

def endPC (p : Fin 4) (f : Fin 18) : Nat := fieldPC p f+2*(widths p f).length

theorem physical_field (pi : Image) (p : Fin 4) (f : Fin 18) (i : Index) (o : Nat)
    (old actual : MachineState) (fit : o<LENGTH) (phase : p.val=o%4) (start : PrefixStart old i o)
    (entry : actual.pc=addr (4096+4*beforePC p f)) (rel : Rel (beforeCopy old f) actual) :
    PricedRun (stitched pi) actual (physicalField p f i o actual) (fieldCycles p f) (extraOps (beforeOps f)) ∧
    Rel (afterCopy old f) (physicalField p f i o actual) ∧
    (physicalField p f i o actual).pc=addr (4096+4*endPC p f) := by
  obtain ⟨low,base,high⟩:=source_rows_range p f
  have ⟨setup,same,pc⟩:=lifted_run pi p (beforeOps f) (beforePC p f) (before_decoded p f) (by omega) (by omega)
    (beforeCopy old f) actual entry rel (pre_ready old i o start f) (before_member f)
  rw [before_relation] at same
  rw [base] at pc
  have ref:=atCopy_witness old i o fit start f
  have aligns:=field_prepared ref same pc (sources_aligned i f) (by rw [phase];exact dst_residue o f)
    (every_site_fetches pi p f)
  have ⟨copy,next⟩:=field_refinement aligns ref same
  refine ⟨by simpa only [Nat.add_zero,physicalField,fieldCycles] using setup.next copy.priced,next,?_⟩
  rw [physicalField,moveList_pc,pc]
  unfold addr endPC
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

def physicalFields (p : Fin 4) (i : Index) (o : Nat) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => if h : n<18 then physicalField p ⟨n,h⟩ i o (physicalFields p i o s n) else physicalFields p i o s n

def fieldsCycles (p : Fin 4) : Nat → Nat
  | 0 => 0
  | n+1 => fieldsCycles p n + if h : n<18 then fieldCycles p ⟨n,h⟩ else 0

def virtualAt (s : MachineState) (n : Nat) : MachineState :=
  if z : n=0 then s else if h : n-1<18 then afterCopy s ⟨n-1,h⟩ else s

def wirePC (p : Fin 4) (n : Nat) : Nat :=
  if h : n<18 then beforePC p ⟨n,h⟩ else lastPC p

theorem next_wire (p : Fin 4) (f : Fin 18) : endPC p f=wirePC p (f.val+1) := by
  exact (show ∀ t : Fin 4, ∀ j : Fin 18, endPC t j=wirePC t (j.val+1) by decide) p f

theorem base_wire (p : Fin 4) : wirePC p 0=phasePC p := by
  exact (show ∀ t : Fin 4, wirePC t 0=phasePC t by decide) p

theorem complete_cost (p : Fin 4) : fieldsCycles p 18+lastOps.length+2=phaseCost p := by
  exact (show ∀ t : Fin 4, fieldsCycles t 18+lastOps.length+2=phaseCost t by decide) p

theorem virtual_before (old : MachineState) (f : Fin 18) : virtualAt old f.val=beforeCopy old f := by
  have small : f.val-1<18 := by omega
  simp [virtualAt,beforeCopy,small]

theorem virtual_after (old : MachineState) (f : Fin 18) : virtualAt old (f.val+1)=afterCopy old f := by
  simp [virtualAt,f.isLt]

def fieldExtra (n : Nat) : Nat := if 1<n then 3 else 0
theorem fieldExtra_step (f : Fin 18) : fieldExtra (f.val+1)=fieldExtra f.val+extraOps (beforeOps f) :=
  (show ∀ j : Fin 18, fieldExtra (j.val+1)=fieldExtra j.val+extraOps (beforeOps j) by decide) f

theorem fields_run (pi : Image) (p : Fin 4) (i : Index) (o : Nat) (old actual : MachineState)
    (fit : o<LENGTH) (phase : p.val=o%4) (start : PrefixStart old i o)
    (entry : actual.pc=addr (4096+4*phasePC p)) (rel : Rel old actual) (n : Nat) (lim : n≤18) :
    PricedRun (stitched pi) actual (physicalFields p i o actual n) (fieldsCycles p n) (fieldExtra n) ∧
    Rel (virtualAt old n) (physicalFields p i o actual n) ∧
    (physicalFields p i o actual n).pc=addr (4096+4*wirePC p n) := by
  induction n with
  | zero =>
    refine ⟨?_,by simpa [virtualAt,physicalFields] using rel,?_⟩
    · intro fuel coins;simp [physicalFields,fieldsCycles,fieldExtra,Execution.charge]
    · simpa only [physicalFields,base_wire] using entry
  | succ n ih =>
    have inside : n<18 := by omega
    let f : Fin 18 := ⟨n,inside⟩
    obtain ⟨initial,same,pc⟩:=ih (by omega)
    have before : Rel (beforeCopy old f) (physicalFields p i o actual n) := by
      rw [←virtual_before]; exact same
    have localPC : (physicalFields p i o actual n).pc=addr (4096+4*beforePC p f) := by
      simpa only [wirePC,dif_pos inside] using pc
    obtain ⟨step,after,exitPC⟩:=physical_field pi p f i o old _ fit phase start localPC before
    simp only [physicalFields,fieldsCycles,dif_pos inside]
    refine ⟨by rw [show n+1=f.val+1 by rfl,fieldExtra_step];exact initial.next step,?_,?_⟩
    · rw [show n+1=f.val+1 by rfl,virtual_after]
      exact after
    · exact exitPC.trans (congrArg (fun k=>addr (4096+4*k)) (next_wire p f))
#print axioms fields_run
end TwoPermutationPrototype.PhaseOpening
