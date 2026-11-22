import CommitGolfCandidate.GroupOpenWholeRaw
import CommitGolfCandidate.GroupOpenLeafFields
import CommitGolfCandidate.GroupOpenCapEmitPrefix

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

def PureRow : Instr → Bool
  | .ADDI .. | .SRLI .. | .SLLI .. | .ANDI .. | .XORI .. | .ADD .. | .LUI .. | .OR .. => true
  | _ => false

theorem pure_run (s : MachineState) (w : Nat) (xs : List Instr) (slice : Slice w xs)
    (bounded : w+xs.length≤7872) (pc : s.pc=pcAt w) (pure : ∀ i∈xs, PureRow i=true) :
    RunsOpeningBlock s (execCode s xs) xs.length := by
  have ready (t : MachineState) (ops : List Instr) (h : ∀ i∈ops, PureRow i=true) : Ready t ops := by
    induction ops generalizing t with
    | nil => trivial
    | cons i is ih =>
      refine ⟨?_,ih _ (fun j m => h j (List.mem_cons_of_mem _ m))⟩
      have hi := h i (List.mem_cons_self ..)
      cases i <;> first | rfl | cases hi
  exact code_run xs w s bounded (codeOfSlice slice) (ready s xs pure) pc
    (fun i m => by have hi:=pure i m; cases i <;> first | rfl | cases hi)
    (fun t i m => by have hi:=pure i m; cases i <;> first | rfl | cases hi)

/-- Only the first record arrives from the salt pass at word 15. Subsequent
records enter the nonce setup immediately before their class's writer. -/
def dispatch (n : MachineState) := if n.pc=pcAt 18 then n.setPC (pcAt (row 0 0)) else n

private theorem entry_table (c : Fin 4) : Slice (row c 0-3) nonceSetupCode ∧
    3≤row c 0 ∧ row c 0<7872 ∧ row c 0≠18 := by revert c;decide +kernel

theorem enter_run (s : MachineState) (o : Nat) (pc : s.pc=setupPC o)
    (valid : accessValid (s.getReg .x8) 8=true) :
    let n:=nonceSetup s
    RunsOpeningBlock s (dispatch n) (3+firstCost o) ∧ (dispatch n).pc=pcAt (row (pageClass o) 0) ∧
    (dispatch n).mem=n.mem ∧ ∀ r, r≠.x31 → r≠.x29 → (dispatch n).getReg r=n.getReg r := by
  let c : Fin 4:=⟨pageClass o,class_lt o⟩
  let n:=nonceSetup s
  have post:=nonce_setup_post s
  by_cases first : o=0
  · have at15 : s.pc=pcAt 15 := by simpa only [setupPC,if_pos first] using pc
    have at18 : n.pc=pcAt 18 := by rw [show n.pc=_ from post.1,at15];rfl
    have run : RunsOpeningBlock s n 3 := fun fuel coins => execute_nonce_setup s at15 valid fuel coins
    have hop:=run_step n 18 (.JAL .x0 24516) (by decide) at18 (by decide +kernel) rfl rfl
    have eq : execInstrBr n (.JAL .x0 24516)=n.setPC (pcAt (row 0 0)) := by
      change n.setPC (n.pc+signExtend21 24516)=_;rw [at18];rfl
    rw [eq] at hop
    change RunsOpeningBlock s (dispatch n) _ ∧ _
    simp only [dispatch,show (nonceSetup s).pc=pcAt 18 from at18,at18,if_pos rfl,firstCost,first,zero_class]
    exact ⟨run.next hop,rfl,rfl,fun _ _ _ => MachineState.getReg_setPC ..⟩
  · have entry : s.pc=pcAt (row c 0-3) := by simpa only [setupPC,if_neg first] using pc
    obtain ⟨code,low,high,ne⟩:=entry_table c
    have ra : Ready s nonceSetupCode := by
      refine ⟨?_,rfl,rfl,trivial⟩
      simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
    have run : RunsOpeningBlock s n 3 := code_run nonceSetupCode _ s (by change _+3≤_;omega)
      (codeOfSlice code) ra entry (by decide)
      (by intro u i m;simp only [nonceSetupCode,List.mem_cons,List.not_mem_nil,or_false] at m
          rcases m with rfl|rfl|rfl <;> rfl)
    have endPC : n.pc=pcAt (row c 0) := by
      rw [show n.pc=_ from post.1,entry];exact (ofNat_step _ 3).trans (congrArg pcAt (by omega))
    have nePC : n.pc≠pcAt 18 := by
      rw [endPC];intro eq;have q:=congrArg BitVec.toNat eq
      change (4096+4*row c 0)%2^64=4168 at q;omega
    change RunsOpeningBlock s (dispatch n) _ ∧ _
    simp only [dispatch,show (nonceSetup s).pc≠pcAt 18 from nePC,nePC,if_false,firstCost,if_neg first,Nat.add_zero]
    exact ⟨run,endPC,trivial,fun _ _ _ => trivial⟩

def topRows : List Instr :=
  [.SRLI .x29 .x6 13,.XORI .x29 .x29 1,.SLLI .x29 .x29 5,.ADD .x29 .x9 .x29,.LHU .x10 .x29 28]
def preload (s : MachineState) := execCode s topRows

@[local simp] private theorem fixed_pc (s : MachineState) (v : Word) : (s.setPC v).pc=v := rfl
@[local simp] private theorem fixed_mem (s : MachineState) (v : Word) : (s.setPC v).mem=s.mem := rfl
@[local simp] private theorem fixed_reg_mem (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl

def fixedSlotCode : List Instr :=
  [.SLLI .x7 .x6 8, .ANDI .x7 .x7 3072, .ADD .x7 .x7 .x24, .ANDI .x10 .x6 3,
   .ADDI .x7 .x7 584]

def fixedExitCode : List Instr := [.SRLI .x6 .x6 2,.ADD .x6 .x6 .x19]
def fixedSlot (s : MachineState) := execCode s fixedSlotCode
def fixedExit (s : MachineState) := execCode s fixedExitCode
theorem fixedSlot_post (s : MachineState) :
    let u := fixedSlot s
    u.pc=s.pc+20 ∧ u.mem=s.mem ∧ u.getReg .x21=s.getReg .x21 ∧
    u.getReg .x7 = (((s.getReg .x6 <<< 8) &&& (3072#12).signExtend 64) + s.getReg .x24) + 584 ∧
    u.getReg .x10 = s.getReg .x6 &&& 3 ∧
    ∀ r, r ≠ .x21 → r ≠ .x7 → r ≠ .x10 → u.getReg r = s.getReg r := by
  simp [fixedSlot,execCode,fixedSlotCode,execInstrBr,signExtend12,BitVec.add_assoc]
  intro r a b c
  simp [Ne.symm a,Ne.symm b,Ne.symm c]

theorem fixedExit_post (s : MachineState) :
    let u := fixedExit s
    u.pc=s.pc+8 ∧ u.mem=s.mem ∧ u.getReg .x21=s.getReg .x21 ∧
    u.getReg .x6=(s.getReg .x6 >>> 2)+s.getReg .x19 ∧
    ∀ r, r ≠ .x21 → r ≠ .x6 → u.getReg r = s.getReg r := by
  simp [fixedExit,execCode,fixedExitCode,execInstrBr,signExtend12,BitVec.add_assoc]
  intro r a b
  simp [Ne.symm a, Ne.symm b]

theorem prefix_code (c : Fin 4) : Slice (row c 1) fixedSlotCode ∧ Slice (row c 5) fixedExitCode ∧
    Slice (row c 6) topRows ∧ ∀ j : Fin 3, Slice (row c (2+j.val)) (quartetHeadCode j) := by
  revert c; decide +kernel

theorem prefix_layout (c : Fin 4) :
    rawStart c 0+(shape c 0).cycles=row c 1 ∧ row c 1+5=row c 2 ∧
    row c 5+2=row c 6 ∧ row c 6+5=row c 7 ∧ row c 7<7872 ∧
    ∀ j : Fin 3, rawStart c (1+j.val)=row c (2+j.val)+3 ∧
      rawStart c (1+j.val)+(shape c (1+j.val)).cycles=row c (3+j.val) ∧
      row c (2+j.val)≤row c (3+j.val) ∧ row c (3+j.val)≤row c 5 := by
  revert c; decide

theorem slot_run (c : Fin 4) (s : MachineState) (pc : s.pc=pcAt (row c 1)) :
    RunsOpeningBlock s (fixedSlot s) 5 :=
  pure_run s _ fixedSlotCode (prefix_code c).1 ((show ∀ a : Fin 4, row a 1+5≤7872 from by decide) c) pc (by decide)

theorem mate_run (c : Fin 4) (j : Fin 3) (s : MachineState) (pc : s.pc=pcAt (row c (2+j.val))) :
    RunsOpeningBlock s (quartetHead j s) 3 := by
  exact pure_run s _ (quartetHeadCode j) ((prefix_code c).2.2.2 j)
    ((show ∀ a : Fin 4, ∀ k : Fin 3, row a (2+k.val)+3≤7872 from by decide) c j) pc
    (by intro i hi; simp only [quartetHeadCode,List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl|rfl|rfl <;> rfl)

theorem exit_run (c : Fin 4) (s : MachineState) (pc : s.pc=pcAt (row c 5)) :
    RunsOpeningBlock s (fixedExit s) 2 :=
  pure_run s _ fixedExitCode (prefix_code c).2.1 (by have := prefix_layout c;change _+2≤_;omega) pc (by decide)

private theorem shift13 (i : Index) :
    BitVec.ofNat 64 (upperNode i 0) >>> 13 = BitVec.ofNat 64 (upperNode i 13) := by
  apply BitVec.eq_of_toNat_eq
  have a:=upper_node_bound i 0; have b:=upper_node_bound i 13
  have small : 2*LENGTH<2^64 := by decide
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show upperNode i 0<2^64 by omega),Nat.mod_eq_of_lt (show upperNode i 13<2^64 by omega),
    Nat.shiftRight_eq_div_pow]
  rw [upper_node_zero,upper_node_heap_index]

theorem preload_run (c : Fin 4) (s : MachineState) (i : Index) (pc : s.pc=pcAt (row c 6))
    (heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase) (node : s.getReg .x6=BitVec.ofNat 64 (upperNode i 0)) :
    RunsOpeningBlock s (preload s) 5 ∧ (preload s).pc=pcAt (row c 7) ∧ (preload s).mem=s.mem ∧
    (preload s).getReg .x10=(s.getHalfword (BitVec.ofNat 64 (siblingAddress i 13+28))).zeroExtend 64 ∧
    ∀ r, r≠.x10 → r≠.x29 → (preload s).getReg r=s.getReg r := by
  have addr : s.getReg .x9+(((s.getReg .x6 >>> 13) ^^^ (signExtend12 1)) <<< (5:Nat)) =
      BitVec.ofNat 64 (siblingAddress i 13) := by
    rw [heap,node,shift13, sibling_address_upper i 13 (by decide)]
    change BitVec.ofNat 64 trapdoorBase+((BitVec.ofNat 64 (upperNode i 13) ^^^ BitVec.ofNat 64 1) <<< (5:Nat))=_
    rw [← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow]
    change _ + BitVec.ofNat 64 _ * BitVec.ofNat 64 32=_
    rw [← BitVec.ofNat_mul,← BitVec.ofNat_add,Nat.mul_comm _ 32]
  have addr' : s.getReg .x9+(((s.getReg .x6 >>> 13) ^^^ (signExtend12 1)) <<< (5:Nat))+signExtend12 28 =
      BitVec.ofNat 64 (siblingAddress i 13+28) := by rw [addr,show signExtend12 28=BitVec.ofNat 64 28 from rfl,←BitVec.ofNat_add]
  have ready : Ready s topRows := by
    refine ⟨rfl,rfl,rfl,rfl,?_,trivial⟩
    change accessValid _ 2=true
    rw [show (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.SRLI .x29 .x6 13)) (.XORI .x29 .x29 1)) (.SLLI .x29 .x29 5)) (.ADD .x29 .x9 .x29)).getReg .x29 + signExtend12 28=BitVec.ofNat 64 (siblingAddress i 13+28) from addr']
    have h:=sibling_address_inside i 13
    have fit : nonceBase≤MEMORY_BYTES := by decide
    exact half_access _ (by omega) (by omega)
  have pos:=prefix_layout c
  have ran := code_run topRows _ s (by change _+5≤_;omega) (codeOfSlice (prefix_code c).2.2.1)
    ready pc (by decide) (by intro u op hi; simp only [topRows,List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl)
  refine ⟨ran,?_,rfl,?_,?_⟩
  · change s.pc+4+4+4+4+4=_
    rw [pc,←pos.2.2.2.1]; simp only [BitVec.add_assoc]; exact ofNat_step _ 5
  · change (s.getHalfword _).zeroExtend 64=_
    rw [←addr']; rfl
  · intro r a b; simp [preload,execCode,topRows,execInstrBr,Ne.symm a,Ne.symm b]

end TwoPermutationPrototype.GroupedOpening.Whole
