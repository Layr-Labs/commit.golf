import CommitGolfCandidate.Stage3cChainSites
import CommitGolfCandidate.Stage3cChainMem
import CommitGolfCandidate.Stage3cPassEntry
import CommitGolfCandidate.Stage3cHash
import CommitGolfCandidate.Stage3cRuns
import CommitGolfCandidate.Execution
set_option maxHeartbeats 4000000
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000

def scratchWord (j : Nat) := scratchBase+32+8*j

def clearScratch (s : MachineState) : Nat→MachineState
  | 0=>s
  | j+1=>let t:=clearScratch s j
         (t.setMem (BitVec.ofNat 64 (scratchWord j)) 0).setPC (t.pc+4)

theorem clear_register (s : MachineState) (n : Nat) (r : Reg) :
    (clearScratch s n).getReg r=s.getReg r := by induction n with
  | zero=>rfl
  | succ j ih=>exact ih

theorem clear_pc (s : MachineState) (n : Nat) : (clearScratch s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero=>simp [clearScratch]
  | succ n ih=>
    change (clearScratch s n).pc+4=_
    rw [ih,BitVec.add_assoc,show 4*(n+1)=4*n+4 by omega,BitVec.ofNat_add];rfl

theorem clear_word (s : MachineState) (n j : Nat) (inside : j<n) (bound : n≤8) :
    (clearScratch s n).getMem (BitVec.ofNat 64 (scratchWord j))=0 := by
  induction n with
  | zero=>omega
  | succ n ih=>
    change ((clearScratch s n).setMem (BitVec.ofNat 64 (scratchWord n)) 0).getMem _=_
    by_cases same : j=n
    · subst j;exact MachineState.getMem_setMem_eq
    · rw [MachineState.getMem_setMem_ne]
      · exact ih (by omega) (by omega)
      · intro e;have v:=congrArg BitVec.toNat e
        simp only [scratchWord,scratchBase,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 7516200960+32+8*j<2^64),Nat.mod_eq_of_lt (by omega : 7516200960+32+8*n<2^64)] at v
        omega

private theorem zero_region (s : MachineState) (a n : Nat) (al : a%8=0)
    (zero : ∀ i<n, s.getMem (BitVec.ofNat 64 (a+8*i))=0) : readBuffer s a (8*n)=0 := by
  have byte (j : Nat) (small : j<8*n) : s.getByte (BitVec.ofNat 64 (a+j))=0 := by
    rw [MachineState.getByte,word_address a j al,zero (j/8) (by omega)]
    simp [extractByte]
  unfold readBuffer
  rw [Finset.sum_eq_zero fun j hj=> by rw [byte j (Finset.mem_range.mp hj)];simp];rfl

theorem clear_pads (s : MachineState) : ScratchPad (clearScratch s 8) := by
  constructor
  · exact zero_region _ (scratchBase+32) 4 (by decide) (fun j hj=>clear_word s 8 j (by omega) le_rfl)
  · apply zero_region _ (scratchBase+72) 3 (by decide)
    intro j hj
    rw [show scratchBase+72+8*j=scratchWord (j+5) by unfold scratchWord;omega]
    exact clear_word s 8 _ (by omega) le_rfl

theorem clear_frame (s : MachineState) (n : Nat) (cap : n≤8) : unchanged s (clearScratch s n) scratchBase 96 := by
  intro b k bound apart
  induction n with
  | zero=>rfl
  | succ n ih=>
    refine (read_after_store_outside (clearScratch s n) (scratchWord n) 0 b k (by unfold scratchWord scratchBase;omega)
      (by unfold scratchWord scratchBase;omega) (by change _≤2^36 at bound;omega) ?_).trans (ih (by omega))
    unfold scratchWord;rcases apart with left|right <;> omega

private theorem clear_sites : ∀ d : Height,chained d → ∀ j : Fin 8,
    passHeader d+j.val<11543 ∧ decoded (passHeader d+j.val)=some (.base (.SD .x24 .x0 (BitVec.ofNat 12 (32+8*j.val)))) := by decide +kernel

theorem clear_run (o : Oracle) (d : Height) (cut : chained d) (s : MachineState) (common : Common s) (pc : s.pc=pcAt (passHeader d)) :
    Runs .commit true o s (clearScratch s 8) 8 8 0 := by
  apply runs_pure;intro f
  rw [Nat.add_comm]
  apply execute_unit_steps (states:=clearScratch s)
  intro j hj
  let t:=clearScratch s j
  have slot:=clear_sites d cut ⟨j,hj⟩
  have ip : t.pc=pcAt (passHeader d+j) := by
    rw [show t.pc=s.pc+BitVec.ofNat 64 (4*j) from clear_pc ..,pc,pcAt,pcAt,←BitVec.ofNat_add];congr 1 <;> omega
  have ad : t.getReg .x24+signExtend12 (BitVec.ofNat 12 (32+8*j))=BitVec.ofNat 64 (scratchWord j) := by
    have v : signExtend12 (BitVec.ofNat 12 (32+8*j))=BitVec.ofNat 64 (32+8*j):=small_signed ⟨32+8*j,by omega⟩
    rw [show t.getReg .x24=s.getReg .x24 from clear_register ..,common.scratch,v];change BitVec.ofNat 64 7516200960+BitVec.ofNat 64 _=_
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold scratchWord scratchBase;omega
  have ok : accessValid (BitVec.ofNat 64 (scratchWord j)) 8=true := by
    apply access_ok <;> unfold scratchWord scratchBase <;> change _ at * <;> first | (change _≤2^36;omega) | omega
  refine ⟨_,(decoded_site slot.1 slot.2) t ip,?_,rfl⟩
  change ordinaryStep t (.base (.SD .x24 .x0 (BitVec.ofNat 12 (32+8*j))))=some _
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,ad,ok,ite_true,decide_true]
  rfl
end CommitGolfCandidate.Chained.BinaryMachine
