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
    (bounded : w+xs.length≤6144) (pc : s.pc=pcAt w) (pure : ∀ i∈xs, PureRow i=true) :
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

private def selectorRows : List Instr := [.ANDI .x31 .x21 7, .SLLI .x31 .x31 10, .LUI .x29 5, .ADD .x31 .x31 .x29]

def dispatch (s : MachineState) :=
  execInstrBr (execCode (execInstrBr s (.JAL .x0 12216)) selectorRows) (.JALR .x0 .x31 0)

theorem dispatch_run (s : MachineState) (c : Fin 4) (pc : s.pc=pcAt 18)
    (sel : s.getReg .x21 &&& signExtend12 7 = BitVec.ofNat 64 (2*c.val)) :
    RunsOpeningBlock s (dispatch s) 6 ∧ (dispatch s).pc=pcAt (row c 0) ∧
    (dispatch s).mem=s.mem ∧ ∀ r, r≠.x31 → r≠.x29 → (dispatch s).getReg r=s.getReg r := by
  let entry := execInstrBr s (.JAL .x0 12216)
  let mid := execCode entry selectorRows
  have hop := run_step s 18 (.JAL .x0 12216) (by decide) pc (by decide +kernel) rfl rfl
  have pc1 : entry.pc=pcAt 3072 := by change s.pc+signExtend21 12216=_; rw [pc]; rfl
  have setup : RunsOpeningBlock entry mid 4 := pure_run entry 3072 selectorRows
    (by decide +kernel) (by decide) pc1 (by decide)
  have pc2 : mid.pc=pcAt 3076 := by change entry.pc+4+4+4+4=_; rw [pc1]; rfl
  have finish := run_step mid 3076 (.JALR .x0 .x31 0) (by decide) pc2 (by decide +kernel) rfl rfl
  refine ⟨(hop.next setup).next finish, ?_, rfl, ?_⟩
  · change ((((s.getReg .x21 &&& signExtend12 7) <<< (10 : Nat)) + (20480#64) + 0) &&& ~~~1#64) = _
    rw [sel]; fin_cases c <;> decide
  · intro r h31 h29
    simp [dispatch,selectorRows,execCode,execInstrBr,Ne.symm h31,Ne.symm h29]

def topRows : List Instr :=
  [.SRLI .x29 .x6 13,.XORI .x29 .x29 1,.SLLI .x29 .x29 5,.ADD .x29 .x9 .x29,.LHU .x10 .x29 28]
def preload (s : MachineState) := execCode s topRows

theorem prefix_code (c : Fin 4) : Slice (row c 1) slotCode ∧ Slice (row c 5) quartetExitCode ∧
    Slice (row c 6) topRows ∧ ∀ j : Fin 3, Slice (row c (2+j.val)) (quartetHeadCode j) := by
  revert c; decide +kernel

theorem prefix_layout (c : Fin 4) :
    rawStart c 0+(shape c 0).cycles=row c 1 ∧ row c 1+6=row c 2 ∧
    row c 5+3=row c 6 ∧ row c 6+5=row c 7 ∧ row c 7<6144 ∧
    ∀ j : Fin 3, rawStart c (1+j.val)=row c (2+j.val)+3 ∧
      rawStart c (1+j.val)+(shape c (1+j.val)).cycles=row c (3+j.val) ∧
      row c (2+j.val)≤row c (3+j.val) ∧ row c (3+j.val)≤row c 5 := by
  revert c; decide

theorem slot_run (c : Fin 4) (s : MachineState) (pc : s.pc=pcAt (row c 1)) :
    RunsOpeningBlock s (slotStart s) 6 :=
  pure_run s _ slotCode (prefix_code c).1 ((show ∀ a : Fin 4, row a 1+6≤6144 from by decide) c) pc (by decide)

theorem mate_run (c : Fin 4) (j : Fin 3) (s : MachineState) (pc : s.pc=pcAt (row c (2+j.val))) :
    RunsOpeningBlock s (quartetHead j s) 3 := by
  exact pure_run s _ (quartetHeadCode j) ((prefix_code c).2.2.2 j)
    ((show ∀ a : Fin 4, ∀ k : Fin 3, row a (2+k.val)+3≤6144 from by decide) c j) pc
    (by intro i hi; simp only [quartetHeadCode,List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl|rfl|rfl <;> rfl)

theorem exit_run (c : Fin 4) (s : MachineState) (pc : s.pc=pcAt (row c 5)) :
    RunsOpeningBlock s (quartetExit s) 3 :=
  pure_run s _ quartetExitCode (prefix_code c).2.1 (by have := prefix_layout c;change _+3≤_;omega) pc (by decide)

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
