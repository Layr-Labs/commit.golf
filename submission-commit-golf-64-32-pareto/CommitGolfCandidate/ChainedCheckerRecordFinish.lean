import CommitGolfCandidate.ChainedCheckerCapMarks
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationCheckerLeafRun
import CommitGolfCandidate.TwoPermutationGroupGeometry

/-! Actual record-root insertion, duplicate comparison and outer-record latch. -/
namespace CommitGolfCandidate.Chained.Native.RecordTail
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
attribute [local irreducible] execute chainedCheckerImage
private theorem fetch_at (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (opcode : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch chainedCheckerImage state=some (.base instruction) := by
  have location : state.pc=4096+BitVec.ofNat 64 (4*index) := by
    change state.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index)
    rwa [←BitVec.ofNat_add]
  simpa only [opcode] using chained_checker_ops_at index
    (by rw [chained_checker_ops_length]; exact bounded) state location


def Hop (s t : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel, execute chainedCheckerImage (steps+fuel) s false = do
    let result ← execute chainedCheckerImage fuel t false
    return result.charge cycles 0

abbrev GroupHop (s t : MachineState) (cost : Nat) : Prop := Hop s t cost cost


theorem Hop.thenDo {s t u : MachineState} {a b c d : Nat}
    (first : Hop s t a c) (last : Hop t u b d) : Hop s u (a+b) (c+d) := by
  intro fuel
  rw [Nat.add_assoc,first,last]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,← Nat.add_assoc]

theorem GroupHop.thenDo {s t u : MachineState} {a b : Nat}
    (first : GroupHop s t a) (last : GroupHop t u b) : GroupHop s u (a+b) :=
  Hop.thenDo first last


open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

inductive GroupBlock where
  | setup | compare (i : Fin 4) | duplicate | mark | latch

def GroupBlock.words : GroupBlock → List Instr
  | .setup => [.SLLI .x7 .x6 3,.ADD .x7 .x26 .x7,.SLLI .x28 .x6 5,.ADD .x28 .x25 .x28,
      .LD .x29 .x7 0,.BEQ .x29 .x0 56]
  | .compare i => [.LD .x29 .x28 (BitVec.ofNat 12 (8*i.val)),
      .LD .x30 .x23 (BitVec.ofNat 12 (8*i.val)),.BNE .x29 .x30 (BitVec.ofNat 13 (464-12*i.val))]
  | .duplicate => [.JAL .x0 44]
  | .mark => [.ADDI .x29 .x0 1,.SD .x7 .x29 0]
  | .latch => [.ADDI .x8 .x8 8,.ADDI .x19 .x19 256,.ADDI .x18 .x18 4095,.BNE .x18 .x0 7192]

def GroupBlock.start : GroupBlock → Nat
  | .setup => 2614 | .compare i => 2620+3*i.val | .duplicate => 2632 | .mark => 2641 | .latch => 2643

def GroupBlock.partialState (block : GroupBlock) (state : MachineState) (count : Nat) :=
  (block.words.take count).foldl execInstrBr state

def GroupBlock.done (block : GroupBlock) (state : MachineState) :=
  block.words.foldl execInstrBr state

def groupMarkAddress (s : MachineState) := s.getReg .x26+(s.getReg .x6 <<< 3)
def groupRootAddress (s : MachineState) := s.getReg .x25+(s.getReg .x6 <<< 5)

def GroupBlock.Valid (block : GroupBlock) (s : MachineState) : Prop :=
  match block with
  | .setup => accessValid (groupMarkAddress s) 8=true
  | .compare i => accessValid (s.getReg .x28+BitVec.ofNat 64 (8*i.val)) 8=true ∧
      accessValid (s.getReg .x23+BitVec.ofNat 64 (8*i.val)) 8=true
  | .duplicate | .latch => True
  | .mark => accessValid (s.getReg .x7) 8=true

private theorem groupCode_group_prefix_succ (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) :
    block.partialState s (i+1)=execInstrBr (block.partialState s i) (block.words[i]?.getD .EBREAK) := by
  simp only [GroupBlock.partialState,List.take_succ_eq_append_getElem inside,List.foldl_append,
    List.getElem?_eq_getElem inside,Option.getD_some,List.foldl_cons,List.foldl_nil]

private theorem groupCode_prefix_pc (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) :
    (block.partialState s i).pc=s.pc+BitVec.ofNat 64 (4*i) := by
  have short : i<6 := by cases block <;> simp [GroupBlock.words] at inside <;> omega
  cases block <;> simp [GroupBlock.words] at inside <;> interval_cases i <;> first | omega |
    simp [GroupBlock.partialState,GroupBlock.words,execInstrBr,MachineState.setPC,BitVec.add_assoc]

private theorem groupCode_group_ordinary (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) (valid : block.Valid s) :
    ordinaryStep (block.partialState s i) (.base (block.words[i]?.getD .EBREAK)) =
      some (block.partialState s (i+1)) := by
  rw [groupCode_group_prefix_succ _ _ _ inside]
  cases block with
  | compare n =>
    have l:=valid.1
    have r:=valid.2
    fin_cases n <;> change i<3 at inside <;> interval_cases i <;>
      simp_all [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
        memAccess,execInstrBr,signExtend12]
  | setup =>
    change accessValid (s.getReg .x26+(s.getReg .x6 <<< 3)) 8=true at valid
    change i<6 at inside
    interval_cases i <;> simp [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
      memAccess,execInstrBr,signExtend12,valid]
  | mark =>
    change accessValid (s.getReg .x7) 8=true at valid
    change i<2 at inside
    interval_cases i <;> simp [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
      memAccess,execInstrBr,signExtend12,valid]
  | duplicate => change i<1 at inside; interval_cases i <;> rfl
  | latch => change i<4 at inside; interval_cases i <;> rfl

theorem group_block_execute (block : GroupBlock) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*block.start)) (valid : block.Valid s) (fuel : Nat) :
    execute chainedCheckerImage (block.words.length+fuel) s false = do
      let result ← execute chainedCheckerImage fuel (block.done s) false
      return result.charge block.words.length 0 := by
  have enough : block.start+block.words.length≤3012 := by
    cases block <;> simp [GroupBlock.start,GroupBlock.words] <;> omega
  have final : block.done s=block.partialState s block.words.length := by simp [GroupBlock.done,GroupBlock.partialState]
  rw [final]
  apply execute_unit_steps (states := block.partialState s)
  intro i inside
  refine ⟨.base (block.words[i]?.getD .EBREAK),fetch_at _ (block.start+i) _ (by omega) ?_
    (?decoded),groupCode_group_ordinary block s i inside valid,?_⟩
  · rw [groupCode_prefix_pc _ _ _ inside,here,← BitVec.ofNat_add]
    congr 1
    omega
  case decoded =>
    cases block with
    | compare n => fin_cases n <;> change i<3 at inside <;> interval_cases i <;> rfl
    | setup => change i<6 at inside; interval_cases i <;> rfl
    | duplicate => change i<1 at inside; interval_cases i <;> rfl
    | mark => change i<2 at inside; interval_cases i <;> rfl
    | latch => change i<4 at inside; interval_cases i <;> rfl
  · cases block with
    | setup => change i<6 at inside; interval_cases i <;> rfl
    | compare n => change i<3 at inside; interval_cases i <;> rfl
    | duplicate => change i<1 at inside; interval_cases i <;> rfl
    | mark => change i<2 at inside; interval_cases i <;> rfl
    | latch => change i<4 at inside; interval_cases i <;> rfl

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 32000
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem groupView_setpc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem groupView_setpc_mem (s : MachineState) (pc : Word) : (s.setPC pc).mem=s.mem := rfl
@[local simp] private theorem groupView_setreg_mem (s : MachineState) (r : Reg) (x : Word) : (s.setReg r x).mem=s.mem := by cases r <;> rfl
@[local simp] private theorem groupView_zero_register (s : MachineState) : s.getReg .x0=0#64 := rfl

def GroupSaved (reg : Reg) : Prop :=
  reg ∉ ([.x7,.x8,.x18,.x19,.x28,.x29,.x30,.x31] : List Reg)

def sameGroupWord (s : MachineState) (i : Fin 4) : Prop :=
  s.getMem (s.getReg .x28+BitVec.ofNat 64 (8*i.val)) =
    s.getMem (s.getReg .x23+BitVec.ofNat 64 (8*i.val))
instance (s : MachineState) (i : Fin 4) : Decidable (sameGroupWord s i) := inferInstanceAs (Decidable (_=_))

private theorem groupView_group_beq_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).pc = if s.getReg a=s.getReg b then s.pc+signExtend13 d else s.pc+4 := by
  simp only [execInstrBr,beq_iff_eq]
  split <;> rfl

theorem group_bne_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).pc = if s.getReg a=s.getReg b then s.pc+4 else s.pc+signExtend13 d := by
  simp only [execInstrBr,bne_iff_ne]
  by_cases eq : s.getReg a=s.getReg b <;> simp [eq]

private theorem groupView_group_beq_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

theorem group_bne_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

private theorem groupView_group_beq_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

theorem group_bne_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

private theorem groupView_getMem_pc (s : MachineState) (p a : Word) : (s.setPC p).getMem a=s.getMem a := rfl
private theorem groupView_getMem_reg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getMem a=s.getMem a := by cases r <;> rfl
attribute [local simp] groupView_getMem_pc groupView_getMem_reg

theorem group_setup_view (s : MachineState) (pc : s.pc=(4096+4*2614)) :
    let t := GroupBlock.setup.done s
    t.pc=(if s.getMem (groupMarkAddress s)=0 then (4096+4*2633) else (4096+4*2620)) ∧
    t.getReg .x7=groupMarkAddress s ∧ t.getReg .x28=groupRootAddress s ∧ t.mem=s.mem ∧
    ∀ r : Reg, r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [GroupBlock.done,GroupBlock.words,List.foldl_cons,List.foldl_nil,
    groupView_group_beq_pc,groupView_group_beq_reg,groupView_group_beq_mem]
  simp [execInstrBr,signExtend12,signExtend13,groupMarkAddress,groupRootAddress,pc]
  constructor
  · rfl
  intro r m p t
  simp [Ne.symm m,Ne.symm p,Ne.symm t]

theorem group_compare_view (s : MachineState) (i : Fin 4)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(2620+3*i.val))) :
    let t := (GroupBlock.compare i).done s
    t.pc=(if sameGroupWord s i then BitVec.ofNat 64 (4096+4*(2623+3*i.val)) else (4096+4*2738)) ∧
      t.mem=s.mem ∧ ∀ r : Reg, r≠.x29 → r≠.x30 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [GroupBlock.done,GroupBlock.words,List.foldl_cons,List.foldl_nil,
    group_bne_pc,group_bne_reg,group_bne_mem]
  fin_cases i <;> simp [sameGroupWord,execInstrBr,signExtend12,signExtend13,pc]
  all_goals first | exact ⟨rfl, by intro r m p; simp [Ne.symm m,Ne.symm p]⟩ | (intro r m p; simp [Ne.symm m,Ne.symm p])

theorem group_duplicate_view (s : MachineState) (pc : s.pc=(4096+4*2632)) :
    let t := GroupBlock.duplicate.done s
    t.pc=(4096+4*2643) ∧ t.mem=s.mem ∧ ∀ r, t.getReg r=s.getReg r := by
  simp [GroupBlock.done,GroupBlock.words,execInstrBr,pc,signExtend21]

theorem group_mark_view (s : MachineState) (pc : s.pc=(4096+4*2641)) :
    let t := GroupBlock.mark.done s
    t.pc=(4096+4*2643) ∧ t.mem=(s.setMem (s.getReg .x7) 1).mem ∧
      ∀ r : Reg, r≠.x29 → t.getReg r=s.getReg r := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simp [GroupBlock.done,GroupBlock.words,execInstrBr,pc]
  · simp [GroupBlock.done,GroupBlock.words,execInstrBr,signExtend12,MachineState.setMem]
  · intro r kept
    simp [GroupBlock.done,GroupBlock.words,execInstrBr,Ne.symm kept]

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
private theorem groupLatchView_latch_word (s : MachineState) (reg : Reg) (imm : BitVec 12) (nz : reg≠.x0) :
    (execInstrBr s (.ADDI reg reg imm)).getReg reg=s.getReg reg+signExtend12 imm := by
  simp [execInstrBr,nz]
private theorem groupLatchView_latch_keep (s : MachineState) (reg other : Reg) (imm : BitVec 12) (ne : other≠reg) :
    (execInstrBr s (.ADDI reg reg imm)).getReg other=s.getReg other := by
  simp [execInstrBr,Ne.symm ne]
private theorem groupLatchView_latch_mem (s : MachineState) (reg : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI reg reg imm)).mem=s.mem := by cases reg <;> rfl
private theorem groupLatchView_latch_pc (s : MachineState) (reg : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI reg reg imm)).pc=s.pc+4 := rfl

section
attribute [local irreducible] execInstrBr

private def groupLatchView_lA (s : MachineState) := execInstrBr s (.ADDI .x8 .x8 8)
private def groupLatchView_lB (s : MachineState) := execInstrBr (groupLatchView_lA s) (.ADDI .x19 .x19 256)
private def groupLatchView_lC (s : MachineState) := execInstrBr (groupLatchView_lB s) (.ADDI .x18 .x18 4095)
private def groupLatchView_lD (s : MachineState) := execInstrBr (groupLatchView_lC s) (.BNE .x18 .x0 7192)

private theorem groupLatchView_ldec (s : MachineState) (remaining : Nat) (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) : (groupLatchView_lC s).getReg .x18=BitVec.ofNat 64 remaining := by
  let a := groupLatchView_lA s
  let b := groupLatchView_lB s
  let c := groupLatchView_lC s
  let d := groupLatchView_lD s
  have dec : c.getReg .x18=BitVec.ofNat 64 remaining := by
    rw [show c.getReg .x18 = b.getReg .x18 + signExtend12 4095 from groupLatchView_latch_word _ _ _ (by decide),
      show b.getReg .x18=a.getReg .x18 from groupLatchView_latch_keep _ _ _ _ (by decide),
      show a.getReg .x18=s.getReg .x18 from groupLatchView_latch_keep _ _ _ _ (by decide),
      counter,BitVec.ofNat_add]
    change BitVec.ofNat 64 remaining+1+(-1:Word)=BitVec.ofNat 64 remaining
    simp [BitVec.add_assoc]
  exact dec

private theorem groupLatchView_latch_branch_control (middle : MachineState) (n : Nat)
    (pc : middle.pc=(4096+4*2646)) (count : middle.getReg .x18=BitVec.ofNat 64 n) (small : n<2^64) :
    (execInstrBr middle (.BNE .x18 .x0 7192)).pc=(if n=0 then (4096+4*2647) else (4096+4*2396)) := by
  have fall : ((4096+4*2646) : Word)+4=(4096+4*2647) := by decide
  have back : ((4096+4*2646) : Word)+signExtend13 7192=(4096+4*2396) := by decide
  rw [group_bne_pc,pc,fall,back,count,show middle.getReg .x0=0#64 by rfl]
  by_cases zero : n=0
  · subst n
    rfl
  · have nonzero : BitVec.ofNat 64 n≠0#64 := by
      intro eq
      apply zero
      have numeric := congrArg BitVec.toNat eq
      change n%2^64=0 at numeric
      rwa [Nat.mod_eq_of_lt small] at numeric
    simp only [ite_eq_right nonzero,ite_eq_right zero]

private theorem groupLatchView_lpc (s : MachineState) (pc : s.pc=(4096+4*2643)) (remaining : Nat) (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    (groupLatchView_lD s).pc=(if remaining=0 then (4096+4*2647) else (4096+4*2396)) := by
  apply groupLatchView_latch_branch_control (groupLatchView_lC s) remaining _ (groupLatchView_ldec s remaining counter) small
  rw [groupLatchView_lC,groupLatchView_latch_pc,groupLatchView_lB,groupLatchView_latch_pc,groupLatchView_lA,groupLatchView_latch_pc,pc]
  decide

private theorem groupLatchView_l8 (s : MachineState) : (groupLatchView_lD s).getReg .x8=s.getReg .x8+8 := by
  let a := groupLatchView_lA s
  let b := groupLatchView_lB s
  let c := groupLatchView_lC s
  let d := groupLatchView_lD s
  change d.getReg _=_
  rw [show d.getReg .x8=c.getReg .x8 from group_bne_reg _ _ _ _ _,
    show c.getReg .x8=b.getReg .x8 from groupLatchView_latch_keep _ _ _ _ (by decide),
    show b.getReg .x8=a.getReg .x8 from groupLatchView_latch_keep _ _ _ _ (by decide),
    show a.getReg .x8=s.getReg .x8+signExtend12 8 from groupLatchView_latch_word _ _ _ (by decide)]
  rfl

private theorem groupLatchView_l19 (s : MachineState) : (groupLatchView_lD s).getReg .x19=s.getReg .x19+256 := by
  let a := groupLatchView_lA s
  let b := groupLatchView_lB s
  let c := groupLatchView_lC s
  let d := groupLatchView_lD s
  change d.getReg _=_
  rw [show d.getReg .x19=c.getReg .x19 from group_bne_reg _ _ _ _ _,
    show c.getReg .x19=b.getReg .x19 from groupLatchView_latch_keep _ _ _ _ (by decide),
    show b.getReg .x19=a.getReg .x19+signExtend12 256 from groupLatchView_latch_word _ _ _ (by decide),
    show a.getReg .x19=s.getReg .x19 from groupLatchView_latch_keep _ _ _ _ (by decide)]
  rfl


private theorem groupLatchView_latch_abstract_fold {α : Type} (step : α → Instr → α) (s : α) :
    GroupBlock.latch.words.foldl step s =
      step (step (step (step s (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095))
        (.BNE .x18 .x0 7192) := rfl

private theorem groupLatchView_latch_done_eq (s : MachineState) : GroupBlock.latch.done s = groupLatchView_lD s :=
  groupLatchView_latch_abstract_fold execInstrBr s

private theorem groupLatchView_latch_done_pc (s : MachineState) (pc : s.pc=(4096+4*2643)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    (GroupBlock.latch.done s).pc=(if remaining=0 then (4096+4*2647) else (4096+4*2396)) :=
  (congrArg MachineState.pc (groupLatchView_latch_done_eq s)).trans (groupLatchView_lpc s pc remaining counter small)

private theorem groupLatchView_latch_done_8 (s : MachineState) :
    (GroupBlock.latch.done s).getReg .x8 = s.getReg .x8+8 :=
  (congrArg (fun (t : MachineState) => t.getReg .x8) (groupLatchView_latch_done_eq s)).trans (groupLatchView_l8 s)

private theorem groupLatchView_latch_done_19 (s : MachineState) :
    (GroupBlock.latch.done s).getReg .x19 = s.getReg .x19+256 :=
  (congrArg (fun (t : MachineState) => t.getReg .x19) (groupLatchView_latch_done_eq s)).trans (groupLatchView_l19 s)

private theorem groupLatchView_latch_done_18 (s : MachineState) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) :
    (GroupBlock.latch.done s).getReg .x18 = BitVec.ofNat 64 remaining :=
  (congrArg (fun (t : MachineState) => t.getReg .x18) (groupLatchView_latch_done_eq s)).trans
    ((group_bne_reg (groupLatchView_lC s) .x18 .x0 .x18 7192).trans (groupLatchView_ldec s remaining counter))

private theorem groupLatchView_latch_done_mem (s : MachineState) : (GroupBlock.latch.done s).mem = s.mem :=
  (congrArg MachineState.mem (groupLatchView_latch_done_eq s)).trans
    ((group_bne_mem (groupLatchView_lC s) .x18 .x0 7192).trans
      ((groupLatchView_latch_mem (groupLatchView_lB s) .x18 4095).trans ((groupLatchView_latch_mem (groupLatchView_lA s) .x19 256).trans (groupLatchView_latch_mem s .x8 8))))

private theorem groupLatchView_latch_done_reg (s : MachineState) (r : Reg)
    (r8 : r≠.x8) (r19 : r≠.x19) (r18 : r≠.x18) :
    (GroupBlock.latch.done s).getReg r = s.getReg r :=
  (congrArg (fun (t : MachineState) => t.getReg r) (groupLatchView_latch_done_eq s)).trans
    ((group_bne_reg (groupLatchView_lC s) .x18 .x0 r 7192).trans
      ((groupLatchView_latch_keep (groupLatchView_lB s) .x18 r 4095 r18).trans
        ((groupLatchView_latch_keep (groupLatchView_lA s) .x19 r 256 r19).trans (groupLatchView_latch_keep s .x8 r 8 r8))))

theorem group_latch_view (s : MachineState) (pc : s.pc=(4096+4*2643)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    let t := GroupBlock.latch.done s
    t.pc=(if remaining=0 then (4096+4*2647) else (4096+4*2396)) ∧
      t.getReg .x8=s.getReg .x8+8 ∧ t.getReg .x19=s.getReg .x19+256 ∧
      t.getReg .x18=BitVec.ofNat 64 remaining ∧ t.mem=s.mem ∧
      ∀ r : Reg, r≠.x8 → r≠.x19 → r≠.x18 → t.getReg r=s.getReg r :=
  ⟨groupLatchView_latch_done_pc s pc remaining counter small, groupLatchView_latch_done_8 s, groupLatchView_latch_done_19 s, groupLatchView_latch_done_18 s remaining counter,
    groupLatchView_latch_done_mem s, groupLatchView_latch_done_reg s⟩

end

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure GroupReady (node remaining : Nat) (s : MachineState) : Prop where
  pc : s.pc=(4096+4*2614)
  nodeReg : s.getReg .x6=BitVec.ofNat 64 node
  low : 256≤node
  high : node<512
  scratch : s.getReg .x23=12288
  rootBase : s.getReg .x25=16384
  markBase : s.getReg .x26=4096
  counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)
  small : remaining<2^64

private theorem groupGeometry_shift3 (n : Nat) : (BitVec.ofNat 64 n <<< 3)=BitVec.ofNat 64 (8*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 8=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]
private theorem groupGeometry_shift5 (n : Nat) : (BitVec.ofNat 64 n <<< 5)=BitVec.ofNat 64 (32*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 32=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem GroupReady.mark {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupMarkAddress s=wordAddress (512+n) := by
  rw [groupMarkAddress,h.markBase,h.nodeReg,groupGeometry_shift3]
  change BitVec.ofNat 64 4096+BitVec.ofNat 64 (8*n)=BitVec.ofNat 64 (8*(512+n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem GroupReady.root {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupRootAddress s=wordAddress (2048+4*n) := by
  rw [groupRootAddress,h.rootBase,h.nodeReg,groupGeometry_shift5]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 (32*n)=BitVec.ofNat 64 (8*(2048+4*n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

set_option maxRecDepth 8192

private def groupCopy_copyWords : List Instr :=
  [.LD .x31 .x23 0, .SD .x28 .x31 0, .LD .x31 .x23 8, .SD .x28 .x31 8,
   .LD .x31 .x23 16, .SD .x28 .x31 16, .LD .x31 .x23 24, .SD .x28 .x31 24]

private def groupCopy_copyPrefix (s : MachineState) (count : Nat) :=
  (groupCopy_copyWords.take count).foldl execInstrBr s

def copiedGroup (s : MachineState) := groupCopy_copyPrefix s 8

private theorem groupCopy_store_register (s : MachineState) (address value : Word) (r : Reg) :
    (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl

private theorem groupCopy_copy_keeps (s : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (notScratch : reg ≠ .x31) :
    (groupCopy_copyPrefix s count).getReg reg = s.getReg reg := by
  interval_cases count <;>
    simp only [groupCopy_copyPrefix,groupCopy_copyWords,List.take,List.foldl,execInstrBr,MachineState.getReg_setPC,
      groupCopy_store_register,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem copied_group_register (s : MachineState) (r : Reg) (other : r ≠ .x31) :
    (copiedGroup s).getReg r = s.getReg r :=
  groupCopy_copy_keeps s 8 (by decide) r other

theorem copied_group_pc (s : MachineState) : (copiedGroup s).pc = s.pc+32 := by
  simp [copiedGroup,groupCopy_copyPrefix,groupCopy_copyWords,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem execute_group_copy (s : MachineState) (pc : s.pc = (4096+4*2633))
    (readable : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (8*j.val)) 8 = true)
    (writable : ∀ j : Fin 4, accessValid (s.getReg .x28+BitVec.ofNat 64 (8*j.val)) 8 = true) :
    GroupHop s (copiedGroup s) 8 := by
  intro fuel
  apply execute_unit_steps (states := groupCopy_copyPrefix s)
  intro i bounded
  have src := groupCopy_copy_keeps s i (by omega) .x23 (by decide)
  have dst := groupCopy_copy_keeps s i (by omega) .x28 (by decide)
  have r0 := readable ⟨0,by decide⟩
  have r1 := readable ⟨1,by decide⟩
  have r2 := readable ⟨2,by decide⟩
  have r3 := readable ⟨3,by decide⟩
  have w0 := writable ⟨0,by decide⟩
  have w1 := writable ⟨1,by decide⟩
  have w2 := writable ⟨2,by decide⟩
  have w3 := writable ⟨3,by decide⟩
  have valid : memoryArgumentsValid (groupCopy_copyPrefix s i) (groupCopy_copyWords[i]?.getD .EBREAK) = true := by
    interval_cases i <;>
      simp only [groupCopy_copyWords,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        memoryArgumentsValid,memAccess,src,dst] <;>
      first | exact r0 | exact r1 | exact r2 | exact r3 | exact w0 | exact w1 | exact w2 | exact w3
  refine ⟨.base (groupCopy_copyWords[i]?.getD .EBREAK),fetch_at _ (2633+i) _ (by omega) ?_ ?_,?_,?_⟩
  · interval_cases i <;> simp [groupCopy_copyPrefix,groupCopy_copyWords,execInstrBr,pc,MachineState.setPC]
  · interval_cases i <;> rfl
  · simp only [ordinaryStep]
    interval_cases i <;> simp only [groupCopy_copyWords,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at valid ⊢ <;> rw [ite_eq_left valid] <;> rfl
  · interval_cases i <;> rfl

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem groupCopy_copy_mem_set_reg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem = s.mem := by cases reg <;> rfl

@[local simp] private theorem groupCopy_copy_mem_set_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).mem = s.mem := rfl

private theorem groupCopy_mem_store (s : MachineState) (address value : Word) :
    (s.setMem address value).mem = fun word => if word = address then value else s.mem word := by
  funext word
  simp [MachineState.setMem]

theorem copied_group_memory (s : MachineState)
    (separate : ∀ i j : Fin 4, s.getReg .x23+BitVec.ofNat 64 (8*i.val) ≠
      s.getReg .x28+BitVec.ofNat 64 (8*j.val)) :
    (copiedGroup s).mem = (Opening.fourWordStore s (s.getReg .x23) (s.getReg .x28)).mem := by
  have h10 := separate 1 0
  have h20 := separate 2 0
  have h21 := separate 2 1
  have h30 := separate 3 0
  have h31 := separate 3 1
  have h32 := separate 3 2
  simp [copiedGroup,groupCopy_copyPrefix,groupCopy_copyWords,Opening.fourWordStore,execInstrBr,
    signExtend12,groupCopy_mem_store,MachineState.getMem,BitVec.add_assoc] at h10 h20 h21 h30 h31 h32 ⊢
  all_goals simp [h10,h20,h21,h30,h31,h32]

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

theorem GroupBlock.hop (block : GroupBlock) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*block.start)) (valid : block.Valid s) :
    GroupHop s (block.done s) block.words.length :=
  group_block_execute block s here valid

private def groupCompare_nextWord (left : Nat) : Fin 4 := ⟨(3-left)%4,Nat.mod_lt _ (by decide)⟩

def compareGroup : Nat → MachineState → MachineState × Nat
  | 0,s => (GroupBlock.duplicate.done s,1)
  | left+1,s =>
    let i := groupCompare_nextWord left
    let t := (GroupBlock.compare i).done s
    if sameGroupWord s i then
      let result := compareGroup left t
      (result.1,3+result.2)
    else (t,3)

def GroupReadable (s : MachineState) :=
  ∀ i : Fin 4, (GroupBlock.compare i).Valid s

/-- The comparison has no writes. A mismatch exits on the first unequal
stored word; reaching the record latch authenticates all four words. -/
theorem compare_group_run (s : MachineState) (left : Nat) (bounded : left≤4)
    (here : s.pc=BitVec.ofNat 64 (4096+4*(2632-3*left)))
    (readable : GroupReadable s) :
    let result := compareGroup left s
    GroupHop s result.1 result.2 ∧ result.2≤3*left+1 ∧ result.1.mem=s.mem ∧
      (∀ r : Reg, r≠.x29 → r≠.x30 → result.1.getReg r=s.getReg r) ∧
      result.1.pc=if ∀ i : Fin 4, 4-left≤ i.val → sameGroupWord s i then (4096+4*2643) else (4096+4*2738) := by
  classical
  induction left generalizing s with
  | zero =>
    have pc : s.pc=(4096+4*2632) := here
    have good : ∀ i : Fin 4, 4-0≤ i.val → sameGroupWord s i := by intro i hi;omega
    obtain ⟨after,mem,regs⟩ := group_duplicate_view s pc
    simp only [compareGroup]
    exact ⟨GroupBlock.hop .duplicate s pc trivial,by decide,mem,fun r _ _ => regs r,
      by simpa only [ite_eq_left good] using after⟩
  | succ left ih =>
    let i := groupCompare_nextWord left
    let t := (GroupBlock.compare i).done s
    have val : i.val=3-left := by
      change (3-left)%4=3-left
      apply Nat.mod_eq_of_lt
      omega
    have site : s.pc=BitVec.ofNat 64 (4096+4*(2620+3*i.val)) := by rw [val,here];congr 1;omega
    have hop : GroupHop s t 3 := (GroupBlock.compare i).hop s site (readable i)
    obtain ⟨pc,memory,regs⟩ := group_compare_view s i site
    have equival (j : Fin 4) : sameGroupWord t j ↔ sameGroupWord s j := by
      simp only [sameGroupWord,regs _ (by decide : Reg.x28≠.x29) (by decide : Reg.x28≠.x30),
        regs _ (by decide : Reg.x23≠.x29) (by decide : Reg.x23≠.x30),MachineState.getMem,memory,t]
    have validT : GroupReadable t := by
      intro j
      change accessValid (t.getReg .x28+_) 8=true ∧ accessValid (t.getReg .x23+_) 8=true
      rw [regs _ (by decide) (by decide),regs _ (by decide) (by decide)]
      exact readable j
    by_cases matchWord : sameGroupWord s i
    · have pc' : t.pc=BitVec.ofNat 64 (4096+4*(2632-3*left)) := by
        rw [show t.pc=_ from pc,ite_eq_left matchWord,val]
        congr 1
        omega
      obtain ⟨run,cost,mem,kept,exit⟩ := ih t (by omega) pc' validT
      have allWords : (∀ j : Fin 4, 4-left≤ j.val → sameGroupWord t j) ↔
          (∀ j : Fin 4, 4-(left+1)≤ j.val → sameGroupWord s j) := by
        constructor
        · intro later j hj
          by_cases eq : j=i
          · simpa only [eq] using matchWord
          · have apart : j.val ≠ i.val := fun h => eq (Fin.ext h)
            exact (equival j).mp (later j (by omega))
        · intro all j hj
          exact (equival j).mpr (all j (by omega))
      simp only [compareGroup,show sameGroupWord s (groupCompare_nextWord left) from matchWord,↓reduceIte]
      exact ⟨hop.thenDo run,by change 3+(compareGroup left t).2≤_; omega,mem.trans memory,
        fun r a b => (kept r a b).trans (regs r a b),by simpa only [allWords] using exit⟩
    · have bad : ¬∀ j : Fin 4, 4-(left+1)≤ j.val → sameGroupWord s j :=
        fun h => matchWord (h i (by omega))
      simp only [compareGroup,show ¬sameGroupWord s (groupCompare_nextWord left) from matchWord,↓reduceIte]
      exact ⟨hop,by omega,memory,regs,by simpa only [ite_eq_right matchWord,ite_eq_right bad] using pc⟩

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (GroupAccepted groupMemory group_memory_set group_memory_four aligned_access distinct_word_offset word_offset)
set_option maxRecDepth 8192
attribute [local irreducible] GroupBlock.done compareGroup copiedGroup

private def groupRun_groupPrepared (s : MachineState) (node : Nat) : MachineState × Nat :=
  let t := GroupBlock.setup.done s
  if s.getMem (wordAddress (512+node))=0 then
    (GroupBlock.mark.done (copiedGroup t),16)
  else
    let result := compareGroup 4 t
    (result.1,6+result.2)

def groupRun (s : MachineState) (node : Nat) : MachineState × Nat :=
  let result := groupRun_groupPrepared s node
  if GroupAccepted s node then (GroupBlock.latch.done result.1,result.2+4) else result

structure GroupFrame (s t : MachineState) (node remaining : Nat) : Prop where
  pc : t.pc=if GroupAccepted s node then (if remaining=0 then (4096+4*2647) else (4096+4*2396)) else (4096+4*2738)
  memory : t.mem=(groupMemory s node).mem
  saved : ∀ r, GroupSaved r → t.getReg r=s.getReg r
  advanced : GroupAccepted s node → t.getReg .x8=s.getReg .x8+8 ∧ t.getReg .x19=s.getReg .x19+256 ∧
    t.getReg .x18=BitVec.ofNat 64 remaining

private def groupRun_BeforeSaved (reg : Reg) : Prop := reg ∉ ([.x7,.x28,.x29,.x30,.x31] : List Reg)

private theorem groupRun_prepared_run (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    let result := groupRun_groupPrepared s node
    GroupHop s result.1 result.2 ∧ result.2≤19 ∧
      result.1.pc=(if GroupAccepted s node then (4096+4*2643) else (4096+4*2738)) ∧
      result.1.mem=(groupMemory s node).mem ∧
      ∀ r : Reg, groupRun_BeforeSaved r → result.1.getReg r=s.getReg r := by
  let t := GroupBlock.setup.done s
  obtain ⟨pc,mark,root,mem,regs⟩ := group_setup_view s ready.pc
  rw [ready.mark] at pc mark
  rw [ready.root] at root
  have setup : GroupHop s t 6 := GroupBlock.hop .setup s ready.pc (by
    change accessValid (groupMarkAddress s) 8=true
    rw [ready.mark]
    exact aligned_access _ (by have := ready.high;omega))
  have src : t.getReg .x23=wordAddress 1536 := (regs _ (by decide) (by decide) (by decide)).trans ready.scratch
  have rd (j : Fin 4) : accessValid (t.getReg .x28+BitVec.ofNat 64 (8*j.val)) 8=true := by
    rw [root,word_offset]
    apply aligned_access
    have := ready.high
    omega
  have sd (j : Fin 4) : accessValid (t.getReg .x23+BitVec.ofNat 64 (8*j.val)) 8=true := by
    rw [src,word_offset]
    exact aligned_access _ (by omega)
  have fields (r : Reg) (saved : groupRun_BeforeSaved r) : r≠.x7 ∧ r≠.x28 ∧ r≠.x29 ∧ r≠.x30 ∧ r≠.x31 := by
    simpa [groupRun_BeforeSaved,not_or] using saved
  by_cases fresh : s.getMem (wordAddress (512+node))=0
  · have ok : GroupAccepted s node := Or.inl fresh
    have copyPC : t.pc=(4096+4*2633) := by simpa only [ite_eq_left fresh] using pc
    let c := copiedGroup t
    have copy : GroupHop t c 8 := execute_group_copy t copyPC sd rd
    have markPC : c.pc=(4096+4*2641) := by rw [show c.pc=t.pc+32 from copied_group_pc t,copyPC];rfl
    have markReg : c.getReg .x7=wordAddress (512+node) := (copied_group_register _ _ (by decide)).trans mark
    have writeMark : GroupHop c (GroupBlock.mark.done c) 2 := GroupBlock.hop .mark c markPC (by
      change accessValid (c.getReg .x7) 8=true
      rw [markReg]
      exact aligned_access _ (by have := ready.high;omega))
    have separate (i j : Fin 4) :
        t.getReg .x23+BitVec.ofNat 64 (8*i.val)≠t.getReg .x28+BitVec.ofNat 64 (8*j.val) := by
      rw [src,root]
      exact distinct_word_offset _ _ _ _ (by omega) (by have := ready.high;omega) (by omega)
    have copiedMem := copied_group_memory t separate
    rw [src,root] at copiedMem
    obtain ⟨dest,store,kept⟩ := group_mark_view c markPC
    rw [groupRun_groupPrepared,ite_eq_left fresh,groupMemory,ite_eq_left fresh,ite_eq_left ok]
    refine ⟨(setup.thenDo copy).thenDo writeMark,by change 16≤19;decide,dest,?_,?_⟩
    · rw [store,markReg]
      exact group_memory_set (copiedMem.trans (group_memory_four mem _ _)) _ _
    · intro r h
      obtain ⟨a,b,d,_,e⟩ := fields _ h
      exact (kept r d).trans ((copied_group_register _ _ e).trans (regs r a b d))
  · have duplicatePC : t.pc=(4096+4*2620) := by simpa only [ite_eq_right fresh] using pc
    have readable : GroupReadable t := fun j => ⟨rd j,sd j⟩
    obtain ⟨run,cost,unchanged,kept,exit⟩ := compare_group_run t 4 (by decide) duplicatePC readable
    have same : (∀ i : Fin 4, 4-4≤ i.val → sameGroupWord t i) ↔ GroupAccepted s node := by
      rw [GroupAccepted,or_iff_right fresh,read_digest_eq_iff _ _ _ _ (by omega) (by decide)]
      have word (j : Fin 4) : sameGroupWord t j ↔
          s.getMem (BitVec.ofNat 64 (8*(2048+4*node)+8*j.val))=s.getMem (BitVec.ofNat 64 (12288+8*j.val)) := by
        simp only [sameGroupWord,src,root,wordAddress,←BitVec.ofNat_add,MachineState.getMem,mem,t]
      constructor
      · intro all j hi
        exact (word ⟨j,hi⟩).mp (all ⟨j,hi⟩ (by omega))
      · intro all j _
        exact (word j).mpr (all j.val j.isLt)
    rw [groupRun_groupPrepared,ite_eq_right fresh,groupMemory,ite_eq_right fresh]
    refine ⟨setup.thenDo run,by change 6+(compareGroup 4 t).2≤19;omega,?_,unchanged.trans mem,?_⟩
    · simpa only [same] using exit
    · intro r h
      obtain ⟨a,b,d,e,_⟩ := fields _ h
      exact (kept r d e).trans (regs r a b d)

private theorem groupRun_run_frame (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    let result := groupRun s node
    GroupHop s result.1 result.2 ∧ result.2≤23 ∧ GroupFrame s result.1 node remaining := by
  obtain ⟨run,cost,exit,mem,regs⟩ := groupRun_prepared_run s node remaining ready
  let p := (groupRun_groupPrepared s node).1
  have old (r : Reg) (h : GroupSaved r) : groupRun_BeforeSaved r := by
    simp [GroupSaved,groupRun_BeforeSaved,not_or] at *
    tauto
  by_cases ok : GroupAccepted s node
  · have entry : p.pc=(4096+4*2643) := by simpa only [ite_eq_left ok] using exit
    have latch : GroupHop p (GroupBlock.latch.done p) 4 := GroupBlock.hop .latch p entry trivial
    have counter : p.getReg .x18=BitVec.ofNat 64 (remaining+1) := (regs .x18 (by unfold groupRun_BeforeSaved;decide)).trans ready.counter
    obtain ⟨pc,a,b,c,m,r⟩ := group_latch_view p entry remaining counter ready.small
    rw [groupRun,ite_eq_left ok]
    refine ⟨run.thenDo latch,by omega,⟨by simpa only [ite_eq_left ok] using pc,m.trans mem,?_,?_⟩⟩
    · intro reg h
      have kept : reg≠.x8 ∧ reg≠.x19 ∧ reg≠.x18 := by simp [GroupSaved,not_or] at h;tauto
      exact (r _ kept.1 kept.2.1 kept.2.2).trans (regs _ (old _ h))
    · intro _
      rw [show p.getReg .x8=s.getReg .x8 from regs _ (by unfold groupRun_BeforeSaved;decide)] at a
      rw [show p.getReg .x19=s.getReg .x19 from regs _ (by unfold groupRun_BeforeSaved;decide)] at b
      exact ⟨a,b,c⟩
  · rw [groupRun,ite_eq_right ok]
    exact ⟨run,by omega,⟨by simpa only [ite_eq_right ok] using exit,mem,fun r h => regs r (old r h),fun h => (ok h).elim⟩⟩

theorem group_run_execute (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    GroupHop s (groupRun s node).1 (groupRun s node).2 := (groupRun_run_frame s node remaining ready).1

theorem group_run_state (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    GroupFrame s (groupRun s node).1 node remaining := (groupRun_run_frame s node remaining ready).2.2

theorem group_run_cost (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    (groupRun s node).2≤23 := (groupRun_run_frame s node remaining ready).2.1

open CommitGolfCandidate.Chained.Native.RecordLeaf

theorem checker_record_group_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) :
    GroupReady (checkerRecordGroup input record) remaining out := by
  have bounds := checker_record_group_bounds input record
  refine ⟨checker_record_lower_pc ready reached,?_,bounds.1,bounds.2,
    (checker_record_lower_ready ready reached).digest,?_,?_,?_,small⟩
  · rw [checker_record_lower_node ready reached,checker_record_group_shift]
  · exact (checker_record_lower_fixed ready reached ⟨8,by decide⟩ (by decide) (by decide)).trans roots
  · exact (checker_record_lower_fixed ready reached ⟨9,by decide⟩ (by decide) (by decide)).trans marks
  · exact (checker_record_lower_fixed ready reached ⟨5,by decide⟩ (by decide) (by decide)).trans counter

theorem checker_record_group_frame {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) :
    GroupFrame out (groupRun out (checkerRecordGroup input record)).1 (checkerRecordGroup input record) remaining :=
  group_run_state out _ remaining (checker_record_group_ready ready reached remaining counter small roots marks)

theorem checker_record_group_execution {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) :
    GroupHop out (groupRun out (checkerRecordGroup input record)).1 (groupRun out (checkerRecordGroup input record)).2 :=
  group_run_execute out _ remaining (checker_record_group_ready ready reached remaining counter small roots marks)

theorem checker_record_group_memory {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) (word : Nat)
    (lower : 4096≤word) (room : word<2^33) (outside : word<src ∨ src+26≤word) :
    memoryView (groupRun out (checkerRecordGroup input record)).1 word=memoryView s word := by
  have frame := checker_record_group_frame ready reached remaining counter small roots marks
  have bound := (checker_record_group_bounds input record).2
  calc
    memoryView (groupRun out (checkerRecordGroup input record)).1 word=memoryView out word := by
      change (groupRun out (checkerRecordGroup input record)).1.mem (wordAddress word)=out.mem (wordAddress word)
      rw [frame.memory]
      exact TwoPermutationPrototype.Checker.group_memory_other out _ word bound (by omega) (by omega)
        (Or.inr (by omega))
    _=memoryView s word := checker_record_lower_memory ready reached word (by omega) room outside

theorem checker_record_next_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096)
    (accepted : GroupAccepted out (checkerRecordGroup input record)) (continued : remaining≠0)
    (nextBase : CheckerRecordBase) (baseNext : nextBase.value=base.value+498)
    (nextWord : Nat) (nextPointer : s.getReg .x8+8=wordAddress nextWord)
    (indexLower : 4096≤nextWord) (indexRoom : nextWord<2^33)
    (indexOutside : nextWord<src ∨ src+26≤nextWord)
    (nextLoaded : s.getMem (wordAddress nextWord)=BitVec.ofNat 64 (checkerRecordInputIndex input (record+1)).val)
    (messageRoom : src+32+37≤2^33) :
    CheckerRecordCoreReady input (record+1) nextBase (src+32) (groupRun out (checkerRecordGroup input record)).1 := by
  have frame := checker_record_group_frame ready reached remaining counter small roots marks
  have advanced := frame.advanced accepted
  have kept (slot : Fin 14) (saved : GroupSaved (checkerLowerFixedReg slot))
      (notSize : checkerLowerFixedReg slot≠.x11) (notPrimitive : checkerLowerFixedReg slot≠.x13) :
      (groupRun out (checkerRecordGroup input record)).1.getReg (checkerLowerFixedReg slot)=
        s.getReg (checkerLowerFixedReg slot) :=
    (frame.saved _ saved).trans (checker_record_lower_fixed ready reached slot notSize notPrimitive)
  have pointer : (groupRun out (checkerRecordGroup input record)).1.getReg .x8=s.getReg .x8+8 :=
    advanced.1.trans (congrArg (fun value : Word => value+8)
      (checker_record_lower_fixed ready reached ⟨1,by decide⟩ (by decide) (by decide)))
  have source : (groupRun out (checkerRecordGroup input record)).1.getReg .x19=wordAddress (src+32) := by
    have oldSource : out.getReg .x19=s.getReg .x19 :=
      checker_record_lower_fixed ready reached ⟨6,by decide⟩ (by decide) (by decide)
    rw [advanced.2.1,oldSource,ready.source]
    have delta : (256 : Word)=BitVec.ofNat 64 256 := by decide +kernel
    rw [delta]
    change BitVec.ofNat 64 (8*src)+BitVec.ofNat 64 256=BitVec.ofNat 64 (8*(src+32))
    rw [←BitVec.ofNat_add]
    congr 1
  refine ⟨?_,?_,?_,?_,source,?_,?_,?_,?_,?_,?_,?_,messageRoom⟩
  · simpa only [ite_eq_left accepted,ite_eq_right continued] using frame.pc
  · rw [pointer,nextPointer]
    exact CommitGolfCandidate.Chained.Native.RecordLeaf.aligned_access nextWord indexRoom
  · rw [pointer,nextPointer]
    exact (checker_record_group_memory ready reached remaining counter small roots marks nextWord
      indexLower indexRoom indexOutside).trans nextLoaded
  · rw [frame.saved .x21 (by unfold GroupSaved;decide),checker_record_lower_source ready reached,baseNext]
  · exact (kept ⟨12,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans ready.nonce
  · exact (frame.saved .x23 (by unfold GroupSaved;decide)).trans (checker_record_lower_ready ready reached).digest
  · exact (frame.saved .x24 (by unfold GroupSaved;decide)).trans (checker_record_lower_ready ready reached).pair
  · exact (kept ⟨11,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans ready.tagBase
  · exact (kept ⟨13,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans ready.length
  · exact (kept ⟨0,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans ready.selector
  · have := ready.separated
    omega

def CheckerUnreadMemory (reference : MachineState) (first source : Nat) (s : MachineState) : Prop :=
  ∀ word, 4096≤word → word<2^33 → (word<first ∨ source≤word) →
    memoryView s word=memoryView reference word

def CheckerIndexWords (input : CheckInput) (s : MachineState) : Prop :=
  ∀ record, record < input.positions.card → memoryView s (738198020+record)=
    BitVec.ofNat 64 (checkerRecordInputIndex input record).val

theorem checker_loader_index_words (input : CheckInput) :
    CheckerIndexWords input (Artifact.submission.initialState .check input) := by
  intro record present
  have small : record<(input.positions.sort (·≤·)).length := by simpa using present
  have loaded := checker_input_position input record present
  change (Artifact.submission.initialState .check input).getMem
    (BitVec.ofNat 64 (8*(738198020+record)))=_
  rw [show 8*(738198020+record)=5905584160+8*record by omega]
  simpa only [checkerRecordInputIndex,List.getElem?_eq_getElem small,Option.getD_some] using loaded

theorem checker_crypto_index_words {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) : CheckerIndexWords input (checkerCryptoRecordState s) := by
  intro record present
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have bound : input.positions.card≤16777216 := cardinal
  have raw : 6039802000<checkingRawBase := by decide +kernel
  have same := TwoPermutationPrototype.Packed.Checker.word_eq_of_byte_frame
    (Artifact.submission.initialState .check input) (checkerCryptoRecordState s) (738198020+record)
    (fun i small => checker_crypto_record_public input footer s ready _ (by omega) (by omega))
  exact same.trans (checker_loader_index_words input record present)

@[irreducible] def checkerRecordEntryState (s : MachineState) : MachineState :=
  checkerLeafHeadPrefix 1 (checkerCryptoRecordState s)

theorem checker_record_entry_register (s : MachineState) (reg : Reg) (other : reg≠.x5) :
    (checkerRecordEntryState s).getReg reg=(checkerCryptoRecordState s).getReg reg := by
  have step (state : MachineState) : (checkerLeafHeadPrefix 1 state).getReg reg=state.getReg reg := by
    rw [checker_leaf_head_succ,checker_leaf_head_zero]
    cases reg <;> simp at other <;> rfl
  rw [checkerRecordEntryState]
  exact step _

theorem checker_record_entry_memory (s : MachineState) (query : Word) :
    (checkerRecordEntryState s).getMem query=(checkerCryptoRecordState s).getMem query := by
  rw [checkerRecordEntryState]
  exact checker_leaf_head_memory 1 _ (by decide) query

theorem checker_record_entry_unread (s : MachineState) :
    CheckerUnreadMemory (checkerCryptoRecordState s) 754975239 754975239 (checkerRecordEntryState s) := by
  intro word _ _ _
  exact checker_record_entry_memory s (wordAddress word)

theorem checker_unread_index {input : CheckInput} {reference s : MachineState} {source : Nat}
    (indices : CheckerIndexWords input reference) (unread : CheckerUnreadMemory reference 754975239 source s)
    (record : Nat) (present : record < input.positions.card) :
    memoryView s (738198020+record)=BitVec.ofNat 64 (checkerRecordInputIndex input record).val := by
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have bound : input.positions.card≤16777216 := cardinal
  exact (unread _ (by omega) (by omega) (Or.inl (by omega))).trans (indices record present)

theorem checker_record_group_unread {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src first : Nat} {s out reference : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) (ordered : first ≤ src)
    (unread : CheckerUnreadMemory reference first src s) :
    CheckerUnreadMemory reference first (src+32) (groupRun out (checkerRecordGroup input record)).1 := by
  intro word low high domain
  have outside : word<src ∨ src+26≤word := by rcases domain with before | after <;> omega
  have previous : word<first ∨ src≤word := by rcases domain with before | after <;> omega
  exact (checker_record_group_memory ready reached remaining counter small roots marks word low high outside).trans
    (unread word low high previous)

theorem checker_record_entry_assigned (s : MachineState) (reg : Reg)
    (written : reg∈CheckerCryptoPart.records.writes) :
    (checkerRecordEntryState s).getReg reg=checkerCryptoRecordValue s reg :=
  (checker_record_entry_register s reg
    (by cases reg <;> simp [CheckerCryptoPart.writes] at written <;> decide)).trans
    (checker_crypto_record_assigned s reg written)

theorem checker_record_entry_ready {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) :
    CheckerRecordCoreReady input 0 checkerDefaultRecordBase 754975239 (checkerRecordEntryState s) := by
  have pointer : (checkerRecordEntryState s).getReg .x8=wordAddress 738198020 := by
    rw [checker_record_entry_register s .x8 (by decide),checker_record_first_indices input footer s ready]
    decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by decide,by decide⟩
  · rw [checkerRecordEntryState,checker_leaf_head_pc 1 _ (by decide),checker_crypto_record_pc]
    rfl
  · rw [pointer]
    exact CommitGolfCandidate.Chained.Native.RecordLeaf.aligned_access _ (by decide)
  · rw [pointer,checker_record_entry_memory]
    exact checker_crypto_index_words ready 0 (by omega)
  · rw [checker_record_entry_assigned s .x21 (by decide)]
    exact ready.source
  · rw [checker_record_entry_assigned s .x19 (by decide)]
    change s.getReg .x14+signExtend12 4056=wordAddress 754975239
    have abi : s.getReg .x14=(Artifact.submission.initialState .check input).getReg .x14 := ready.abi ⟨2,by decide⟩
    rw [abi,(checker_input_registers input).2.2.2.1]
    rfl
  · rw [checker_record_entry_assigned s .x4 (by decide)]
    simp only [checkerCryptoRecordValue]
  · rw [checker_record_entry_assigned s .x23 (by decide)]
    simp only [checkerCryptoRecordValue]
  · rw [checker_record_entry_assigned s .x24 (by decide)]
    simp only [checkerCryptoRecordValue]
  · rw [checker_record_entry_assigned s .x3 (by decide)]
    simp only [checkerCryptoRecordValue]
  · rw [checker_record_entry_assigned s .x20 (by decide)]
    simp only [checkerCryptoRecordValue] <;> decide +kernel
  · have step (state : MachineState) : (checkerLeafHeadPrefix 1 state).getReg .x5=0 := by
      rw [checker_leaf_head_succ,checker_leaf_head_zero]
      rfl
    rw [checkerRecordEntryState]
    exact step _

theorem checker_record_entry_counter {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) :
    (checkerRecordEntryState s).getReg .x18=BitVec.ofNat 64 input.positions.card := by
  rw [checker_record_entry_assigned s .x18 (by decide)]
  exact (ready.abi ⟨3,by decide⟩).trans (checker_input_registers input).2.2.2.2.2.1

theorem checker_record_selector_execution (s : MachineState) (pc : s.pc=4096+4*2395)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (1+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLeafHeadPrefix 1 s) coins
          return result.charge 1 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_leaf_head_zero s]
  apply execute_unit_steps (states := fun n => checkerLeafHeadPrefix n s)
  intro i small
  have zero : i=0 := by omega
  subst i
  refine ⟨.base (checkerLeafHeadOps.getD 0 .EBREAK),?_,?_,?_⟩
  · apply checker_leaf_head_at 0 (by decide)
    rwa [checker_leaf_head_zero]
  · rw [checker_leaf_head_succ,checker_leaf_head_zero]
    rfl
  · rfl

theorem checker_record_entry_execution {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2073+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordEntryState s) coins
          return result.charge 2073 0) := by
  rw [show 2073+fuel=2072+(1+fuel) by omega,checker_decoded_record_execution input nonempty footer s ready,
    checker_record_selector_execution _ (checker_crypto_record_pc s),checkerRecordEntryState]
  simp [Execution.charge,←Nat.add_assoc]

def checkerProcessedGroups (input : CheckInput) (record : Nat) : List Nat :=
  ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup).take record

private theorem checker_take_succ {α : Type*} (values : List α) (n : Nat) (present : n<values.length) :
    values.take (n+1)=values.take n++[values[n]'present] := by
  induction values generalizing n with
  | nil => simp at present
  | cons value values ih =>
    cases n with
    | zero => rfl
    | succ n => simpa using congrArg (List.cons value) (ih n (by simpa using present))

theorem checker_record_group_cap (input : CheckInput) (record : Nat) :
    checkerRecordGroup input record=TwoPermutationPrototype.Sampling.capGroup (checkerRecordInputIndex input record) := by
  change 256+(checkerRecordInputIndex input record).val/65536=
    (16777216+(checkerRecordInputIndex input record).val)/65536
  omega

theorem checker_processed_groups_next (input : CheckInput) (record : Nat) (present : record < input.positions.card) :
    checkerProcessedGroups input (record+1)=checkerProcessedGroups input record++[checkerRecordGroup input record] := by
  have bound : record<(input.positions.sort (·≤·)).length := by simpa using present
  have mapped : record<((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup).length := by simpa using bound
  rw [checkerProcessedGroups,checkerProcessedGroups,checker_take_succ _ _ mapped]
  congr 1
  simp only [List.getElem_map,checker_record_group_cap,checkerRecordInputIndex,
    List.getElem?_eq_getElem bound,Option.getD_some]

theorem checker_processed_groups_all (input : CheckInput) :
    checkerProcessedGroups input input.positions.card=(input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup := by
  have all : ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup).take
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup).length=
      (input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup := List.take_length
  simpa only [checkerProcessedGroups,List.length_map,Finset.length_sort] using all

theorem checker_record_group_marked {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64)
    (roots : s.getReg .x25=16384) (marks : s.getReg .x26=4096) (present : record < input.positions.card)
    (marked : ∀ node, 256≤node → node<512 → memoryView s (512+node)=
      if node∈checkerProcessedGroups input record then 1 else 0) :
    ∀ node, 256≤node → node<512 → memoryView (groupRun out (checkerRecordGroup input record)).1 (512+node)=
      if node∈checkerProcessedGroups input (record+1) then 1 else 0 := by
  intro node low high
  have frame := checker_record_group_frame ready reached remaining counter small roots marks
  have prior : out.getMem (wordAddress (512+node))=s.getMem (wordAddress (512+node)) :=
    checker_record_lower_mark_memory ready reached _ (by omega) (by omega)
  have original : s.getMem (wordAddress (512+node))=
      if node∈checkerProcessedGroups input record then 1 else 0 := marked node low high
  change (groupRun out (checkerRecordGroup input record)).1.mem (wordAddress (512+node))=_
  rw [frame.memory]
  change (TwoPermutationPrototype.Checker.groupMemory out (checkerRecordGroup input record)).getMem
    (wordAddress (512+node))=_
  rw [checker_processed_groups_next input record present]
  by_cases same : node=checkerRecordGroup input record
  · subst node
    rw [TwoPermutationPrototype.Checker.group_memory_mark,prior,original]
    by_cases member : checkerRecordGroup input record∈checkerProcessedGroups input record
    · simp [member]
    · simp [member]
  · rw [TwoPermutationPrototype.Checker.group_memory_other out _ _
      (checker_record_group_bounds input record).2 (by omega) (by omega) (Or.inl (by omega)),prior,original]
    simp [same]

structure CheckerRecordBoundary (input : CheckInput) (reference : MachineState)
    (record remaining : Nat) (s : MachineState) : Prop where
  limit : input.positions.card≤LENGTH
  balance : record+remaining=input.positions.card
  pc : s.pc=if remaining=0 then (4096+4*2647) else (4096+4*2396)
  pointer : s.getReg .x8=wordAddress (738198020+record)
  cursor : s.getReg .x21=BitVec.ofNat 64 (checkingRawBase+498*record)
  source : s.getReg .x19=wordAddress (754975239+32*record)
  counter : s.getReg .x18=BitVec.ofNat 64 remaining
  nonce : s.getReg .x4=12272
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  tagBase : s.getReg .x3=4056
  length : s.getReg .x20=BitVec.ofNat 64 LENGTH
  selector : s.getReg .x5=0
  roots : s.getReg .x25=16384
  marks : s.getReg .x26=4096
  cap : s.getReg .x27=256
  claim : s.getReg .x9=reference.getReg .x9
  finish : s.getReg .x22=reference.getReg .x22
  unread : CheckerUnreadMemory reference 754975239 (754975239+32*record) s
  indices : CheckerIndexWords input reference
  marked : ∀ node, 256≤node → node<512 → memoryView s (512+node)=
    if node∈checkerProcessedGroups input record then 1 else 0

theorem checker_record_boundary_initial {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) :
    CheckerRecordBoundary input (checkerCryptoRecordState s) 0 input.positions.card (checkerRecordEntryState s) := by
  have core := checker_record_entry_ready nonempty ready
  refine {
    limit:=by simpa [Index] using Finset.card_le_univ input.positions
    balance:=by omega
    pc:=?_
    pointer:=?_
    cursor:=core.cursor
    source:=core.source
    counter:=checker_record_entry_counter ready
    nonce:=core.nonce
    digest:=core.digest
    pair:=core.pair
    tagBase:=core.tagBase
    length:=core.length
    selector:=core.selector
    roots:=?_
    marks:=?_
    cap:=?_
    claim:=checker_record_entry_register s .x9 (by decide)
    finish:=checker_record_entry_register s .x22 (by decide)
    unread:=checker_record_entry_unread s
    indices:=checker_crypto_index_words ready
    marked:=?_}
  · simpa only [ite_eq_right nonempty] using core.pc
  · rw [checker_record_entry_register s .x8 (by decide),checker_record_first_indices input footer s ready]
    decide +kernel
  · rw [checker_record_entry_assigned s .x25 (by decide)]
    rfl
  · rw [checker_record_entry_assigned s .x26 (by decide)]
    rfl
  · rw [checker_record_entry_assigned s .x27 (by decide)]
    rfl
  · intro node low high
    change (checkerRecordEntryState s).getMem (wordAddress (512+node))=_
    rw [checker_record_entry_memory]
    change (checkerCryptoRecordState s).getMem (BitVec.ofNat 64 (8*(512+node)))=_
    rw [show 8*(512+node)=4096+8*node by omega,checker_crypto_record_marks s node high]
    simp [checkerProcessedGroups]

theorem checker_record_boundary_core {input : CheckInput} {reference s : MachineState} {record remaining : Nat}
    (boundary : CheckerRecordBoundary input reference record remaining s) (active : remaining≠0) :
    ∃ fit : record<LENGTH, CheckerRecordCoreReady input record (checkerRecordBaseAt ⟨record,fit⟩)
      (754975239+32*record) s := by
  have present : record < input.positions.card := by have := boundary.balance;omega
  have fit : record<LENGTH := by have := boundary.limit;omega
  have numerical : record<16777216 := fit
  refine ⟨fit,{
    pc:=?_
    access:=?_
    loaded:=?_
    cursor:=boundary.cursor
    source:=boundary.source
    nonce:=boundary.nonce
    digest:=boundary.digest
    pair:=boundary.pair
    tagBase:=boundary.tagBase
    length:=boundary.length
    selector:=boundary.selector
    separated:=by omega
    endBound:=by omega}⟩
  · simpa only [ite_eq_right active] using boundary.pc
  · rw [boundary.pointer]
    exact CommitGolfCandidate.Chained.Native.RecordLeaf.aligned_access _ (by omega)
  · rw [boundary.pointer]
    exact checker_unread_index boundary.indices boundary.unread record present

theorem checker_record_entry_input_cases (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (∃ cycles, cycles≤49725+2387*input.positions.card ∧
      CheckerRejectedBlock (Artifact.submission.initialState .check input) cycles) ∨
    (∃ footer before cycles, cycles≤49725+2387*input.positions.card ∧
      RunsCheckerFooterBlock (Artifact.submission.initialState .check input) (checkerRecordEntryState before) cycles ∧
      CheckerDecodedInput input footer before) := by
  rcases checker_decoded_input_cases input nonempty lower upper with rejected | decoded
  · obtain ⟨cycles,bound,rejects⟩ := rejected
    exact Or.inl ⟨cycles,by omega,rejects⟩
  · obtain ⟨footer,before,cycles,bound,ran,ready⟩ := decoded
    exact Or.inr ⟨footer,before,cycles+2073,by omega,
      RunsCheckerFooterBlock.next ran (checker_record_entry_execution nonempty ready),ready⟩

theorem checker_record_word_add (address count : Nat) :
    wordAddress address+BitVec.ofNat 64 (8*count)=wordAddress (address+count) := by
  change BitVec.ofNat 64 (8*address)+BitVec.ofNat 64 (8*count)=BitVec.ofNat 64 (8*(address+count))
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

theorem checker_record_boundary_next {input : CheckInput} {reference s out : MachineState} {record remaining : Nat}
    (boundary : CheckerRecordBoundary input reference record (remaining+1) s)
    (reached : out∈support (checkerRecordLowerTrace input record (754975239+32*record) s))
    (accepted : GroupAccepted out (checkerRecordGroup input record)) :
    CheckerRecordBoundary input reference (record+1) remaining (groupRun out (checkerRecordGroup input record)).1 := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
  have cardinal : input.positions.card≤16777216 := boundary.limit
  have small : remaining<2^64 := by have := boundary.balance;omega
  have frame := checker_record_group_frame core reached remaining boundary.counter small boundary.roots boundary.marks
  have advanced := frame.advanced accepted
  have lowerReady := checker_record_lower_ready core reached
  have kept (slot : Fin 14) (saved : GroupSaved (checkerLowerFixedReg slot))
      (notSize : checkerLowerFixedReg slot≠.x11) (notPrimitive : checkerLowerFixedReg slot≠.x13) :
      (groupRun out (checkerRecordGroup input record)).1.getReg (checkerLowerFixedReg slot)=
        s.getReg (checkerLowerFixedReg slot) :=
    (frame.saved _ saved).trans (checker_record_lower_fixed core reached slot notSize notPrimitive)
  have oldPointer : out.getReg .x8=s.getReg .x8 :=
    checker_record_lower_fixed core reached ⟨1,by decide⟩ (by decide) (by decide)
  have oldSource : out.getReg .x19=s.getReg .x19 :=
    checker_record_lower_fixed core reached ⟨6,by decide⟩ (by decide) (by decide)
  refine {
    limit:=boundary.limit
    balance:=by have := boundary.balance;omega
    pc:=?_
    pointer:=?_
    cursor:=?_
    source:=?_
    counter:=advanced.2.2
    nonce:=(kept ⟨12,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.nonce
    digest:=(frame.saved .x23 (by unfold GroupSaved;decide)).trans lowerReady.digest
    pair:=(frame.saved .x24 (by unfold GroupSaved;decide)).trans lowerReady.pair
    tagBase:=(kept ⟨11,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.tagBase
    length:=(kept ⟨13,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.length
    selector:=(kept ⟨0,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.selector
    roots:=(kept ⟨8,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.roots
    marks:=(kept ⟨9,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.marks
    cap:=(kept ⟨10,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.cap
    claim:=(kept ⟨2,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.claim
    finish:=(kept ⟨7,by decide⟩ (by unfold GroupSaved;decide) (by decide) (by decide)).trans boundary.finish
    unread:=?_
    indices:=boundary.indices
    marked:=checker_record_group_marked core reached remaining boundary.counter small boundary.roots boundary.marks
      (by have := boundary.balance;omega) boundary.marked}
  · simpa only [ite_eq_left accepted] using frame.pc
  · rw [advanced.1,oldPointer,boundary.pointer,
      show (8:Word)=BitVec.ofNat 64 (8*1) by decide +kernel,checker_record_word_add]
    congr 1 <;> omega
  · rw [frame.saved .x21 (by unfold GroupSaved;decide),checker_record_lower_source core reached]
    change BitVec.ofNat 64 (checkingRawBase+498*record+498)=BitVec.ofNat 64 (checkingRawBase+498*(record+1))
    congr 1 <;> omega
  · rw [advanced.2.1,oldSource,boundary.source,
      show (256:Word)=BitVec.ofNat 64 (8*32) by decide +kernel,checker_record_word_add]
    congr 1 <;> omega
  · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      checker_record_group_unread core reached remaining boundary.counter small boundary.roots boundary.marks
        (by omega) boundary.unread

theorem checker_record_boundary_rejected {input : CheckInput} {reference s out : MachineState} {record remaining : Nat}
    (boundary : CheckerRecordBoundary input reference record (remaining+1) s)
    (reached : out∈support (checkerRecordLowerTrace input record (754975239+32*record) s))
    (rejected : ¬GroupAccepted out (checkerRecordGroup input record)) :
    (groupRun out (checkerRecordGroup input record)).1.pc=4096+4*2738 := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
  have cardinal : input.positions.card≤16777216 := boundary.limit
  have small : remaining<2^64 := by have := boundary.balance;omega
  have frame := checker_record_group_frame core reached remaining boundary.counter small boundary.roots boundary.marks
  simpa only [ite_eq_right rejected] using frame.pc

structure CheckerRecordPrefixResult where
  state : MachineState
  instructions : Nat
  cycles : Nat
  calls : Nat
  processed : Nat
  rejected : Bool

def CheckerRecordPrefixResult.stopped (s : MachineState) (rejected : Bool) : CheckerRecordPrefixResult :=
  ⟨s,0,0,0,0,rejected⟩

def CheckerRecordPrefixResult.addRecord (result : CheckerRecordPrefixResult) (instructions cycles : Nat) :
    CheckerRecordPrefixResult :=
  {result with
    instructions:=instructions+result.instructions
    cycles:=cycles+result.cycles
    calls:=92+result.calls
    processed:=1+result.processed}

def checkerRecordPrefix (input : CheckInput) : (count record : Nat) → MachineState → OracleComp World CheckerRecordPrefixResult
  | 0,_,s => pure (.stopped s false)
  | count+1,record,s => do
    let out ← checkerRecordLowerTrace input record (754975239+32*record) s
    let tail := groupRun out (checkerRecordGroup input record)
    let instructions := checkerFirstOrderingInput input record+3656+tail.2
    let cycles := checkerFirstOrderingInput input record+4344+tail.2
    if GroupAccepted out (checkerRecordGroup input record) then
      let result ← checkerRecordPrefix input count (record+1) tail.1
      return result.addRecord instructions cycles
    else
      return (CheckerRecordPrefixResult.stopped tail.1 true).addRecord instructions cycles

structure CheckerRecordPrefixGood (input : CheckInput) (reference : MachineState)
    (record remaining count : Nat) (result : CheckerRecordPrefixResult) : Prop where
  work : result.processed≤count
  instructions : result.instructions≤3725*result.processed
  cycles : result.cycles≤4413*result.processed
  calls : result.calls=92*result.processed
  accounting : result.cycles=result.instructions+7*result.calls+44*result.processed
  badpc : result.rejected=true → result.state.pc=4096+4*2738
  continuation : result.rejected=false → result.processed=count ∧
    CheckerRecordBoundary input reference (record+count) (remaining-count) result.state

theorem checker_record_prefix_good {input : CheckInput} {reference s : MachineState} {record remaining count : Nat}
    (boundary : CheckerRecordBoundary input reference record remaining s) (enough : count≤remaining)
    {result : CheckerRecordPrefixResult} (reached : result∈support (checkerRecordPrefix input count record s)) :
    CheckerRecordPrefixGood input reference record remaining count result := by
  induction count generalizing record remaining s result with
  | zero =>
    simp only [checkerRecordPrefix,support_pure,Set.mem_singleton_iff] at reached
    subst result
    refine {
      work:=by simp [CheckerRecordPrefixResult.stopped]
      instructions:=by simp [CheckerRecordPrefixResult.stopped]
      cycles:=by simp [CheckerRecordPrefixResult.stopped]
      calls:=by simp [CheckerRecordPrefixResult.stopped]
      accounting:=by simp [CheckerRecordPrefixResult.stopped]
      badpc:=by simp [CheckerRecordPrefixResult.stopped]
      continuation:=?_}
    intro _
    exact ⟨rfl,by simpa only [CheckerRecordPrefixResult.stopped,Nat.add_zero,Nat.sub_zero] using boundary⟩
  | succ count ih =>
    cases remaining with
    | zero => omega
    | succ remaining =>
      simp only [checkerRecordPrefix,mem_support_bind_iff] at reached
      obtain ⟨out,first,reached⟩ := reached
      obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
      have cardinal : input.positions.card≤16777216 := boundary.limit
      have small : remaining<2^64 := by have := boundary.balance;omega
      have groupReady := checker_record_group_ready core first remaining boundary.counter small boundary.roots boundary.marks
      have cost := group_run_cost out (checkerRecordGroup input record) remaining groupReady
      have lower := checker_record_lower_costs input record
      by_cases accepted : GroupAccepted out (checkerRecordGroup input record)
      · simp only [ite_eq_left accepted,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
        obtain ⟨rest,later,rfl⟩ := reached
        have good := ih (checker_record_boundary_next boundary first accepted) (by omega) later
        refine {
          work:=?_
          instructions:=?_
          cycles:=?_
          calls:=?_
          accounting:=?_
          badpc:=?_
          continuation:=?_}
        · dsimp [CheckerRecordPrefixResult.addRecord]
          have := good.work
          omega
        · dsimp [CheckerRecordPrefixResult.addRecord]
          have := good.instructions
          omega
        · dsimp [CheckerRecordPrefixResult.addRecord]
          have := good.cycles
          omega
        · dsimp [CheckerRecordPrefixResult.addRecord]
          have := good.calls
          omega
        · dsimp [CheckerRecordPrefixResult.addRecord]
          have := good.accounting
          omega
        · intro rejected
          exact good.badpc rejected
        · intro continued
          obtain ⟨processed,final⟩ := good.continuation continued
          refine ⟨by dsimp [CheckerRecordPrefixResult.addRecord];omega,?_⟩
          change CheckerRecordBoundary input reference (record+(count+1)) ((remaining+1)-(count+1)) rest.state
          rw [show record+(count+1)=record+1+count by omega,
            show (remaining+1)-(count+1)=remaining-count by omega]
          exact final
      · simp only [ite_eq_right accepted,support_pure,Set.mem_singleton_iff] at reached
        subst result
        refine {
          work:=by dsimp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped];omega
          instructions:=by dsimp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped];omega
          cycles:=by dsimp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped];omega
          calls:=by simp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped]
          accounting:=by dsimp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped];omega
          badpc:=?_
          continuation:=by simp [CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped]}
        intro _
        exact checker_record_boundary_rejected boundary first accepted

theorem checker_record_prefix_execution {input : CheckInput} {reference s : MachineState} {record remaining count : Nat}
    (boundary : CheckerRecordBoundary input reference record remaining s) (enough : count≤remaining) (fuel : Nat) :
    execute (Artifact.submission.image .check) (3725*count+fuel) s false=
      (do let result ← checkerRecordPrefix input count record s
          let final ← execute (Artifact.submission.image .check) (3725*count-result.instructions+fuel) result.state false
          return final.charge result.cycles result.calls) := by
  induction count generalizing record remaining s fuel with
  | zero =>
    have zero (result : Execution) : result.charge 0 0=result := by cases result;simp [Execution.charge]
    simp only [checkerRecordPrefix,pure_bind,CheckerRecordPrefixResult.stopped,Nat.mul_zero,Nat.sub_zero,Nat.zero_add,
      zero,bind_pure]
  | succ count ih =>
    cases remaining with
    | zero => omega
    | succ remaining =>
      obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
      let instructions := checkerFirstOrderingInput input record+3656
      have lowerBound : instructions≤3702 := (checker_record_lower_costs input record).1
      rw [show 3725*(count+1)+fuel=instructions+(3725*count+(3725-instructions)+fuel) by omega,
        checker_record_lower_execution core]
      simp only [checkerRecordPrefix,bind_assoc]
      apply bind_congr_of_forall_mem_support
      intro out first
      have cardinal : input.positions.card≤16777216 := boundary.limit
      have small : remaining<2^64 := by have := boundary.balance;omega
      have groupReady := checker_record_group_ready core first remaining boundary.counter small boundary.roots boundary.marks
      let tail := groupRun out (checkerRecordGroup input record)
      have cost : tail.2≤23 := group_run_cost out (checkerRecordGroup input record) remaining groupReady
      let gap := 3725-instructions-tail.2
      have hop (extra : Nat) : execute (Artifact.submission.image .check) (tail.2+extra) out false=
          (do let result ← execute (Artifact.submission.image .check) extra tail.1 false
              return result.charge tail.2 0) := by
        simpa only [checking_manifest_image] using
          checker_record_group_execution core first remaining boundary.counter small boundary.roots boundary.marks extra
      have room : instructions+tail.2≤3725 := by omega
      rw [show 3725*count+(3725-instructions)+fuel=tail.2+(3725*count+(gap+fuel)) by dsimp only [gap];omega,hop]
      simp only [bind_assoc,pure_bind]
      by_cases accepted : GroupAccepted out (checkerRecordGroup input record)
      · simp only [ite_eq_left accepted]
        have next := checker_record_boundary_next boundary first accepted
        rw [ih next (by omega) (gap+fuel)]
        simp only [bind_assoc,pure_bind]
        apply bind_congr_of_forall_mem_support
        intro rest later
        have good := checker_record_prefix_good next (by omega) later
        have within : rest.instructions≤3725*count := by have := good.instructions;have := good.work;omega
        simp only [CheckerRecordPrefixResult.addRecord]
        rw [show 3725*count-rest.instructions+(gap+fuel)=
          3725*(count+1)-(instructions+tail.2+rest.instructions)+fuel by dsimp only [gap];omega]
        apply bind_congr
        intro result
        congr 1
        cases result
        simp [Execution.charge,tail,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      · simp only [ite_eq_right accepted,pure_bind,CheckerRecordPrefixResult.stopped,CheckerRecordPrefixResult.addRecord,
          Nat.add_zero]
        rw [show 3725*count+(gap+fuel)=3725*(count+1)-(instructions+tail.2)+fuel by dsimp only [gap];omega]
        apply bind_congr
        intro result
        congr 1
        cases result
        simp [Execution.charge,tail,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem checker_decoded_records_execution {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) (count : Nat) (enough : count ≤ input.positions.card) (fuel : Nat) :
    execute (Artifact.submission.image .check) (2073+3725*count+fuel) s false=
      (do let result ← checkerRecordPrefix input count 0 (checkerRecordEntryState s)
          let final ← execute (Artifact.submission.image .check) (3725*count-result.instructions+fuel) result.state false
          return final.charge (2073+result.cycles) result.calls) := by
  rw [Nat.add_assoc,checker_record_entry_execution nonempty ready,
    checker_record_prefix_execution (checker_record_boundary_initial nonempty ready) enough]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro result
  apply bind_congr
  intro final
  congr 1
  cases final
  simp [Execution.charge,Nat.add_assoc]

theorem checker_decoded_records_limits {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) (count : Nat) (enough : count ≤ input.positions.card)
    {result : CheckerRecordPrefixResult}
    (reached : result∈support (checkerRecordPrefix input count 0 (checkerRecordEntryState s))) :
    result.instructions≤3725*count ∧ 2073+result.cycles≤2073+4413*count ∧ result.calls≤92*count ∧
      (result.state.pc=4096+4*2738 ∨
        CheckerRecordBoundary input (checkerCryptoRecordState s) count (input.positions.card-count) result.state) := by
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty ready) enough reached
  refine ⟨by have := good.instructions;have := good.work;omega,
    by have := good.cycles;have := good.work;omega,
    by have := good.calls;have := good.work;omega,?_⟩
  cases flag : result.rejected with
  | false =>
    right
    simpa only [Nat.zero_add] using (good.continuation flag).2
  | true => exact Or.inl (good.badpc flag)

theorem checker_decoded_records_complete {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {s : MachineState}
    (ready : CheckerDecodedInput input footer s) {result : CheckerRecordPrefixResult}
    (reached : result∈support (checkerRecordPrefix input input.positions.card 0 (checkerRecordEntryState s))) :
    result.state.pc=4096+4*2738 ∨ result.state.pc=4096+4*2647 := by
  rcases (checker_decoded_records_limits nonempty ready _ (by omega) reached).2.2.2 with rejected | finished
  · exact Or.inl rejected
  · right
    simpa using finished.pc

open TwoPermutationPrototype.Sampling in
theorem checker_decoded_cap_ready {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))}
    {before state : MachineState} (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) :
    CheckerCap.Visit.CapMarkReady ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) state
      (checkingRawBase+498*input.positions.card)
      (checkingRawBase+498*input.positions.card+30*(checkerInputFooterNodes input).length) := by
  have frontier : (checkerInputFooterNodes input).length≤128 := by
    rw [checkerInputFooterNodes,cap_frontier_length]
    exact production_boundary_bound _
  have endReg : (checkerCryptoRecordState before).getReg .x22=
      BitVec.ofNat 64 (checkingRawBase+498*input.positions.card+30*(checkerInputFooterNodes input).length) := by
    rw [checker_crypto_record_assigned before .x22 (by decide)]
    change before.getReg .x15+before.getReg .x17=_
    rw [decoded.source,decoded.length,checker_input_raw_records_length,←BitVec.ofNat_add]
    congr 1 <;> omega
  refine {
    pc:=by simpa using boundary.pc
    selector:=boundary.selector
    roots:=boundary.roots
    markBase:=boundary.marks
    capLeaves:=boundary.cap
    marked:=?_
    cursor:=boundary.cursor
    endReg:=boundary.finish.trans endReg
    above:=by have := checkerDefaultRecordBase.above;change 32768≤checkingRawBase at this;omega
    even:=by
      have even : checkingRawBase%2=0 := checkerDefaultRecordBase.even
      simp [Nat.add_mod,Nat.mul_mod,even]
    endBound:=by
      have cardinal : input.positions.card≤16777216 := boundary.limit
      have room : checkingRawBase+498*16777216+3840≤MEMORY_BYTES := by decide +kernel
      omega
    room:=by change checkingRawBase+498*input.positions.card+30*(checkerInputFooterNodes input).length≤_;omega}
  intro node low high
  rw [TwoPermutationPrototype.Opening.mark_word_leaf _ ⟨node,high⟩ low]
  simpa only [checker_processed_groups_all] using boundary.marked node low high

theorem checker_decoded_cap_post {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))}
    {before state out : MachineState} (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (reached : out∈support (CheckerCap.Visit.capDfsEntryTrace
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (CheckerCap.Visit.capMarkedState state))) :
    out.pc=4096+4*2718 ∧ out.getReg .x21=out.getReg .x22 ∧
      out.getReg .x25=wordAddress 2048 ∧ out.getReg .x9=wordAddress 536871424 := by
  have ready := checker_decoded_cap_ready decoded boundary
  have post := CheckerCap.Visit.cap_entry_post (CheckerCap.Visit.cap_mark_ready ready) reached
  have kept (reg : Reg) (found : reg∈TwoPermutationPrototype.Packed.Checker.capFixedRegisters)
      (other : reg≠.x11 ∧ reg≠.x13 ∧ reg≠.x6 ∧ reg≠.x7 ∧ reg≠.x28 ∧ reg≠.x29) :
      out.getReg reg=state.getReg reg :=
    (post.2.2.2 reg found other.1 other.2.1).trans
      (CheckerCap.Visit.cap_marked_register state reg other.2.2.1 other.2.2.2.1 other.2.2.2.2.1 other.2.2.2.2.2)
  have claim : (checkerCryptoRecordState before).getReg .x9=wordAddress 536871424 := by
    rw [checker_crypto_record_assigned before .x9 (by decide)]
    change before.getReg .x11=wordAddress 536871424
    exact (decoded.abi ⟨0,by decide⟩).trans (checker_input_registers input).2.1
  refine ⟨post.1,?_,(kept .x25 (by decide) (by decide)).trans boundary.roots,
    (kept .x9 (by decide) (by decide)).trans (boundary.claim.trans claim)⟩
  have cursor : out.getReg .x21=BitVec.ofNat 64
      (checkingRawBase+498*input.positions.card+30*(checkerInputFooterNodes input).length) := by
    simpa only [checkerInputFooterNodes] using post.2.1.proof
  exact cursor.trans ((kept .x22 (by decide) (by decide)).trans ready.endReg).symm

def checkerCapFinish (input : CheckInput) (state : MachineState) (fuel : Nat) : OracleComp World Execution := do
  let groups := (input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup
  let out ← CheckerCap.Visit.capDfsEntryTrace groups (CheckerCap.Visit.capMarkedState state)
  let result ← execute (Artifact.submission.image .check) (16+fuel) out false
  return result.charge
    (2556+CheckerCap.Visit.capTreeSteps groups 1 8+7*TwoPermutationPrototype.Checker.capHashCount groups 1 8)
    (TwoPermutationPrototype.Checker.capHashCount groups 1 8)

theorem checker_cap_finish_execution {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))}
    {before state : MachineState} (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) (fuel : Nat) :
    execute (Artifact.submission.image .check)
      (2556+CheckerCap.Visit.capTreeSteps
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8+16+fuel) state false=
      checkerCapFinish input state fuel := by
  simpa only [checkerCapFinish,checking_manifest_image,Nat.add_assoc] using
    CheckerCap.Visit.cap_mark_dfs_execution (checker_decoded_cap_ready decoded boundary) (16+fuel)

theorem checker_cap_finish_limits {input : CheckInput}
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))}
    {before state : MachineState} (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (fuel : Nat) {result : Execution} (reached : result∈support (checkerCapFinish input state fuel)) :
    result.exit≠.unfinished ∧ result.cycles≤63047 ∧ result.oracleCalls≤ min (8*input.positions.card) 255 := by
  simp only [checkerCapFinish,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨out,passed,terminal,ended,rfl⟩ := reached
  have post := checker_decoded_cap_post decoded boundary passed
  obtain ⟨finished,success,calls,done,cycles,run⟩ := CheckerCap.Visit.execute_root_check out 536871424 fuel
    post.1 post.2.2.1 post.2.2.2 (by decide)
  rw [checking_manifest_image,run,support_pure,Set.mem_singleton_iff] at ended
  subst terminal
  have limits := CheckerCap.Visit.cap_mark_dfs_limits
    ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
  have groups : TwoPermutationPrototype.Checker.capHashCount
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8≤8*input.positions.card := by
    simpa using TwoPermutationPrototype.Checker.cap_hash_count_root
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
  refine ⟨done,?_,?_⟩
  · change 2556+CheckerCap.Visit.capTreeSteps
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8+
      7*TwoPermutationPrototype.Checker.capHashCount
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8+finished.cycles≤63047
    omega
  · change TwoPermutationPrototype.Checker.capHashCount
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8+finished.oracleCalls≤ min (8*input.positions.card) 255
    exact Nat.le_min.mpr ⟨by omega,by omega⟩

def checkerDecodedRun (input : CheckInput) (before : MachineState) (fuel : Nat) : OracleComp World Execution := do
  let records ← checkerRecordPrefix input input.positions.card 0 (checkerRecordEntryState before)
  let left := 3725*input.positions.card-records.instructions
  let groups := (input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup
  let capInstructions := 2556+CheckerCap.Visit.capTreeSteps groups 1 8
  let result ← if records.rejected then
      execute (Artifact.submission.image .check) (left+61262+fuel) records.state false
    else checkerCapFinish input records.state (left+(61246-capInstructions)+fuel)
  return result.charge (2073+records.cycles) records.calls

theorem checker_decoded_execution {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (fuel : Nat) :
    execute (Artifact.submission.image .check) (2073+3725*input.positions.card+61262+fuel) before false=
      checkerDecodedRun input before fuel := by
  rw [show 2073+3725*input.positions.card+61262+fuel=2073+3725*input.positions.card+(61262+fuel) by omega,
    checker_decoded_records_execution nonempty decoded input.positions.card (by omega)]
  simp only [checkerDecodedRun]
  apply bind_congr_of_forall_mem_support
  intro records reached
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty decoded) (by omega) reached
  cases flag : records.rejected with
  | true => simp only [flag,↓reduceIte,Nat.add_assoc]
  | false =>
    have boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 records.state := by
      simpa only [Nat.zero_add,Nat.sub_self] using (good.continuation flag).2
    let capInstructions := 2556+CheckerCap.Visit.capTreeSteps
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8
    have room : capInstructions≤61246 := (CheckerCap.Visit.cap_mark_dfs_limits
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)).1
    rw [show 3725*input.positions.card-records.instructions+(61262+fuel)=
      capInstructions+16+(3725*input.positions.card-records.instructions+(61246-capInstructions)+fuel) by omega,
      checker_cap_finish_execution decoded boundary]
    simp only [Bool.false_eq_true,↓reduceIte,capInstructions]

theorem checker_decoded_limits {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : SplitCodec.Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (fuel : Nat) {result : Execution}
    (reached : result∈support (checkerDecodedRun input before fuel)) :
    result.exit≠.unfinished ∧ result.cycles≤2073+4413*input.positions.card+63047 ∧
      result.oracleCalls≤92*input.positions.card+min (8*input.positions.card) 255 := by
  simp only [checkerDecodedRun,mem_support_bind_iff] at reached
  obtain ⟨records,seen,returned⟩ := reached
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty decoded) (by omega) seen
  have bounded : records.cycles≤4413*input.positions.card := by have := good.cycles;have := good.work;omega
  have counted : records.calls≤92*input.positions.card := by have := good.calls;have := good.work;omega
  cases flag : records.rejected with
  | true =>
    simp only [flag,Bool.false_eq_true,↓reduceIte,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at returned
    obtain ⟨terminal,returned,rfl⟩ := returned
    have pc := good.badpc flag
    let tail := 3725*input.positions.card-records.instructions+61262+fuel
    have room : 3≤tail := by dsimp only [tail];omega
    have run : execute (Artifact.submission.image .check) tail records.state false=
        pure ⟨.failure,CheckerCap.Visit.rejectState records.state,3,0⟩ := by
      rw [checking_manifest_image,show tail=3+(tail-3) by omega,CheckerCap.Visit.execute_reject records.state pc]
    rw [run,support_pure,Set.mem_singleton_iff] at returned
    subst terminal
    refine ⟨by change Exit.failure≠Exit.unfinished;decide,?_,?_⟩
    · change 2073+records.cycles+3≤_;omega
    · change records.calls+0≤_;omega
  | false =>
    simp only [flag,Bool.false_eq_true,↓reduceIte,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at returned
    obtain ⟨terminal,returned,rfl⟩ := returned
    have boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 records.state := by
      simpa only [Nat.zero_add,Nat.sub_self] using (good.continuation flag).2
    have finished := checker_cap_finish_limits decoded boundary _ returned
    refine ⟨finished.1,?_,?_⟩
    · change 2073+records.cycles+terminal.cycles≤_;have := finished.2.1;omega
    · change records.calls+terminal.oracleCalls≤_;have := finished.2.2;omega

theorem checker_initial_admitted_limits (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (room : 110987+6112*input.positions.card≤fuel) {result : Execution}
    (reached : result∈support (execute (Artifact.submission.image .check) fuel
      (Artifact.submission.initialState .check input) false)) :
    result.exit≠.unfinished ∧ result.cycles≤112772+6800*input.positions.card ∧
      result.oracleCalls≤92*input.positions.card+min (8*input.positions.card) 255 := by
  rcases checker_decoded_input_cases input nonempty lower upper with rejected | admitted
  · obtain ⟨cycles,bound,after,rejects⟩ := rejected
    rw [show fuel=cycles+(fuel-cycles) by omega,rejects,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact ⟨by change Exit.failure≠Exit.unfinished;decide,by change cycles≤_;omega,by change 0≤_;omega⟩
  · obtain ⟨footer,before,cycles,bound,ran,decoded⟩ := admitted
    let extra := fuel-cycles-(2073+3725*input.positions.card+61262)
    rw [show fuel=cycles+(2073+3725*input.positions.card+61262+extra) by dsimp only [extra];omega,
      ran,checker_decoded_execution nonempty decoded extra] at reached
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
    obtain ⟨terminal,finished,rfl⟩ := reached
    have good := checker_decoded_limits nonempty decoded extra finished
    refine ⟨good.1,?_,?_⟩
    · change cycles+terminal.cycles≤_;have := good.2.1;omega
    · change 0+terminal.oracleCalls≤_;have := good.2.2;omega

theorem checker_initial_budgets (input : CheckInput) :
    110987+6112*input.positions.card≤Artifact.submission.steps .check ∧
    112772+6800*input.positions.card≤Artifact.submission.steps .check ∧
    92*input.positions.card+min (8*input.positions.card) 255≤2^31 := by
  have cardinal : input.positions.card≤16777216 := by
    have bound : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bound
  change 110987+6112*input.positions.card≤1099511627776 ∧
    112772+6800*input.positions.card≤1099511627776 ∧ 92*input.positions.card+min (8*input.positions.card) 255≤2^31
  have := Nat.min_le_right (8*input.positions.card) 255
  omega

private theorem checker_header_prefix_pc (s : MachineState) (pc : s.pc=4096)
    (count : Nat) (bounded : count≤12)
    (lower : 5<count → ¬BitVec.ult (s.getReg .x17) (checkerMinimumWord s))
    (upper : 8<count → ¬BitVec.ult (checkerMinimumWord s+1888+1888) (s.getReg .x17))
    (n : Nat) (small : n≤count) :
    (checkerEmptyState n s).pc=4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD n 0) := by
  have next (i : Fin 12) (present : i.val<count) :
      (checkerEmptyState (i.val+1) s).pc=(checkerEmptyState i.val s).pc+
        BitVec.ofNat 64 (4*(checkerAdmissionIndices.getD (i.val+1) 0-checkerAdmissionIndices.getD i.val 0)) := by
    rw [checker_empty_state_succ]
    fin_cases i <;> try rfl
    · have taken : execInstrBr (checkerEmptyState 5 s) (.BGEU .x17 .x2 8)=
          (checkerEmptyState 5 s).setPC ((checkerEmptyState 5 s).pc+8) := by
        apply ite_eq_left
        rw [checker_admission_register 5 s (by decide) .x17 (by decide),checker_admission_minimum]
        exact lower (by omega)
      exact congrArg MachineState.pc taken
    · have taken : execInstrBr (checkerEmptyState 8 s) (.BGEU .x3 .x17 8)=
          (checkerEmptyState 8 s).setPC ((checkerEmptyState 8 s).pc+8) := by
        apply ite_eq_left
        rw [checker_admission_register 8 s (by decide) .x17 (by decide),checker_admission_maximum]
        exact upper (by omega)
      exact congrArg MachineState.pc taken
  induction n with
  | zero => rw [checker_empty_state_zero,pc];rfl
  | succ n ih =>
    have present : n<count := by omega
    rw [next ⟨n,by omega⟩ present,ih (by omega)]
    have arithmetic (i : Fin 12) :
        4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD i.val 0)+
          BitVec.ofNat 64 (4*(checkerAdmissionIndices.getD (i.val+1) 0-checkerAdmissionIndices.getD i.val 0))=
          4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD (i.val+1) 0) := by
      fin_cases i <;> decide +kernel
    exact arithmetic ⟨n,by omega⟩

private theorem checker_header_prefix_execution (s : MachineState) (pc : s.pc=4096)
    (count : Nat) (bounded : count≤12)
    (lower : 5<count → ¬BitVec.ult (s.getReg .x17) (checkerMinimumWord s))
    (upper : 8<count → ¬BitVec.ult (checkerMinimumWord s+1888+1888) (s.getReg .x17))
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerEmptyState count s) coins
          return result.charge count 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_empty_state_zero s]
  apply execute_unit_steps (states := fun n => checkerEmptyState n s)
  intro i inside
  have small : i<12 := by omega
  refine ⟨.base (checkerEmptyOps.getD i .EBREAK),?_,?_,?_⟩
  · have opcode : checkerEmptyOps.getD i .EBREAK=chainedCheckerOps.getD (checkerAdmissionIndices.getD i 0) .EBREAK := by
      interval_cases i <;> rfl
    rw [opcode]
    apply chained_checker_ops_at _ (by rw [chained_checker_ops_length];interval_cases i <;> decide) _
      (checker_header_prefix_pc s pc count bounded lower upper i (by omega))
  · rw [checker_empty_state_succ]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem checker_header_jump_rejects (s : MachineState) (offset : BitVec 21)
    (fetched : fetch chainedCheckerImage s=some (.base (.JAL .x0 offset)))
    (target : s.pc+signExtend21 offset=4096+4*2364) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) s coins=
      pure ⟨.failure,checkerFailureState (s.setPC (4096+4*2364)),4,0⟩ := by
  have step : ordinaryStep s (.base (.JAL .x0 offset))=some (s.setPC (4096+4*2364)) := by
    change some (s.setPC (s.pc+signExtend21 offset))=_
    rw [target]
  rw [show 4+fuel=(3+fuel)+1 by omega,execute_ordinary_step _ _ _ _ _ coins fetched step,
    checker_failure_execution _ (by rfl)]
  rfl

theorem checker_header_lower_rejects (s : MachineState) (pc : s.pc=4096)
    (invalid : BitVec.ult (s.getReg .x17) (checkerMinimumWord s)) : CheckerRejectedBlock s 10 := by
  let before := checkerEmptyState 5 s
  let next := before.setPC (4096+4*6)
  have at5 : before.pc=4096+4*5 :=
    checker_header_prefix_pc s pc 5 (by decide) (by omega) (by omega) 5 (by decide)
  have fetched : fetch chainedCheckerImage before=some (.base (.BGEU .x17 .x2 8)) :=
    chained_checker_ops_at 5 (by rw [chained_checker_ops_length];decide) before at5
  have step : ordinaryStep before (.base (.BGEU .x17 .x2 8))=some next := by
    change some (if ¬BitVec.ult (before.getReg .x17) (before.getReg .x2) then _ else _)=_
    rw [checker_admission_register 5 s (by decide) .x17 (by decide),checker_admission_minimum,
      if_neg (not_not_intro invalid)]
    change some (before.setPC (before.pc+4))=_
    rw [at5];rfl
  have jump : fetch chainedCheckerImage next=some (.base (.JAL .x0 9432)) :=
    chained_checker_ops_at 6 (by rw [chained_checker_ops_length];decide) next rfl
  refine ⟨checkerFailureState (next.setPC (4096+4*2364)),?_⟩
  intro fuel coins
  rw [show 10+fuel=5+(1+(4+fuel)) by omega,
    checker_header_prefix_execution s pc 5 (by decide) (by omega) (by omega),checking_manifest_image,
    show 1+(4+fuel)=(4+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ coins fetched step,checker_header_jump_rejects next 9432 jump (by rfl)]
  rfl

theorem checker_header_upper_rejects (s : MachineState) (pc : s.pc=4096)
    (lower : ¬BitVec.ult (s.getReg .x17) (checkerMinimumWord s))
    (invalid : BitVec.ult (checkerMinimumWord s+1888+1888) (s.getReg .x17)) : CheckerRejectedBlock s 13 := by
  let before := checkerEmptyState 8 s
  let next := before.setPC (4096+4*10)
  have at8 : before.pc=4096+4*9 :=
    checker_header_prefix_pc s pc 8 (by decide) (fun _ => lower) (by omega) 8 (by decide)
  have fetched : fetch chainedCheckerImage before=some (.base (.BGEU .x3 .x17 8)) :=
    chained_checker_ops_at 9 (by rw [chained_checker_ops_length];decide) before at8
  have step : ordinaryStep before (.base (.BGEU .x3 .x17 8))=some next := by
    change some (if ¬BitVec.ult (before.getReg .x3) (before.getReg .x17) then _ else _)=_
    rw [checker_admission_register 8 s (by decide) .x17 (by decide),checker_admission_maximum,
      if_neg (not_not_intro invalid)]
    change some (before.setPC (before.pc+4))=_
    rw [at8];rfl
  have jump : fetch chainedCheckerImage next=some (.base (.JAL .x0 9416)) :=
    chained_checker_ops_at 10 (by rw [chained_checker_ops_length];decide) next rfl
  refine ⟨checkerFailureState (next.setPC (4096+4*2364)),?_⟩
  intro fuel coins
  rw [show 13+fuel=8+(1+(4+fuel)) by omega,
    checker_header_prefix_execution s pc 8 (by decide) (fun _ => lower) (by omega),checking_manifest_image,
    show 1+(4+fuel)=(4+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ coins fetched step,checker_header_jump_rejects next 9416 jump (by rfl)]
  rfl

theorem checker_empty_nonzero_rejects (s : MachineState) (pc : s.pc=4096)
    (bounds : CheckerAdmissionBounds s) (empty : s.getReg .x16=0#64) (nonzero : s.getReg .x17≠0#64) :
    CheckerRejectedBlock s 18 := by
  let before := checkerEmptyState 12 s
  let middle := before.setPC (4096+4*15)
  let next := middle.setPC (4096+4*16)
  have at12 : before.pc=4096+4*14 :=
    checker_header_prefix_pc s pc 12 (by decide) (fun _ => bounds.1) (fun _ => bounds.2) 12 (by decide)
  have fetched : fetch chainedCheckerImage before=some (.base (.BNE .x16 .x0 16)) :=
    chained_checker_ops_at 14 (by rw [chained_checker_ops_length];decide) before at12
  have step : ordinaryStep before (.base (.BNE .x16 .x0 16))=some middle := by
    change some (if before.getReg .x16 != before.getReg .x0 then _ else _)=_
    rw [checker_admission_register 12 s (by decide) .x16 (by decide),empty]
    change some (before.setPC (before.pc+4))=_
    rw [at12];rfl
  have second : fetch chainedCheckerImage middle=some (.base (.BEQ .x17 .x0 8)) :=
    chained_checker_ops_at 15 (by rw [chained_checker_ops_length];decide) middle rfl
  have skipped : (middle.getReg .x17 == middle.getReg .x0)=false := by
    change ((checkerEmptyState 12 s).getReg .x17 == 0#64)=false
    rw [checker_admission_register 12 s (by decide) .x17 (by decide)]
    exact beq_eq_false_iff_ne.mpr nonzero
  have again : ordinaryStep middle (.base (.BEQ .x17 .x0 8))=some next := by
    change some (if middle.getReg .x17 == middle.getReg .x0 then _ else _)=_
    rw [skipped]
    rfl
  have jump : fetch chainedCheckerImage next=some (.base (.JAL .x0 9392)) :=
    chained_checker_ops_at 16 (by rw [chained_checker_ops_length];decide) next rfl
  refine ⟨checkerFailureState (next.setPC (4096+4*2364)),?_⟩
  intro fuel coins
  rw [show 18+fuel=12+(1+(1+(4+fuel))) by omega,
    checker_header_prefix_execution s pc 12 (by decide) (fun _ => bounds.1) (fun _ => bounds.2),checking_manifest_image,
    show 1+(1+(4+fuel))=(1+(4+fuel))+1 by omega,
    execute_ordinary_step _ _ _ _ _ coins fetched step,
    show 1+(4+fuel)=(4+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ coins second again,checker_header_jump_rejects next 9392 jump (by rfl)]
  rfl

theorem checker_initial_limits (input : CheckInput) (valid : input.proof.length≤Artifact.submission.sizes.proof)
    (fuel : Nat) (room : 110987+6112*input.positions.card≤fuel) {result : Execution}
    (reached : result∈support (execute (Artifact.submission.image .check) fuel
      (Artifact.submission.initialState .check input) false)) :
    result.exit≠.unfinished ∧ result.cycles≤112772+6800*input.positions.card ∧
      result.oracleCalls≤92*input.positions.card+min (8*input.positions.card) 255 := by
  let s := Artifact.submission.initialState .check input
  have regs := checker_input_registers input
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have maximum : 482*LENGTH+3776<2^64 := by decide +kernel
  have lengthBound : input.proof.length≤8355061248 := valid
  have lengthFit : input.proof.length<2^64 := by omega
  have lowFit : 482*input.positions.card<2^64 := by omega
  have highFit : 482*input.positions.card+3776<2^64 := by omega
  have minimum : checkerMinimumWord s=BitVec.ofNat 64 (482*input.positions.card) :=
    checker_minimum_of_count s _ cardinal regs.2.2.2.2.2.1
  have maximumWord : checkerMinimumWord s+1888+1888=BitVec.ofNat 64 (482*input.positions.card+3776) := by
    rw [minimum]
    change BitVec.ofNat 64 (482*input.positions.card)+BitVec.ofNat 64 1888+BitVec.ofNat 64 1888=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  have lowIff : BitVec.ult (s.getReg .x17) (checkerMinimumWord s) ↔ input.proof.length<482*input.positions.card := by
    rw [regs.2.2.2.2.2.2,minimum]
    simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthFit,Nat.mod_eq_of_lt lowFit]
  have highIff : BitVec.ult (checkerMinimumWord s+1888+1888) (s.getReg .x17) ↔
      482*input.positions.card+3776 < input.proof.length := by
    rw [regs.2.2.2.2.2.2,maximumWord]
    simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthFit,Nat.mod_eq_of_lt highFit]
  have failure (cycles : Nat) (short : cycles≤21) (bad : CheckerRejectedBlock s cycles) :
      result.exit≠.unfinished ∧ result.cycles≤112772+6800*input.positions.card ∧
        result.oracleCalls≤92*input.positions.card+min (8*input.positions.card) 255 := by
    obtain ⟨after,rejects⟩ := bad
    rw [show fuel=cycles+(fuel-cycles) by omega,rejects,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact ⟨by change Exit.failure≠Exit.unfinished;decide,by change cycles≤_;omega,by change 0≤_;omega⟩
  by_cases lower : 482*input.positions.card ≤ input.proof.length
  · have goodLow : ¬BitVec.ult (s.getReg .x17) (checkerMinimumWord s) := by rw [lowIff];omega
    by_cases upper : input.proof.length≤482*input.positions.card+3776
    · by_cases empty : input.positions.card=0
      · have emptyReg : s.getReg .x16=0#64 := by rw [regs.2.2.2.2.2.1,empty]
        by_cases zero : input.proof.length=0
        · have zeroReg : s.getReg .x17=0#64 := by rw [regs.2.2.2.2.2.2,zero]
          rw [checking_manifest_image,show fuel=21+(fuel-21) by omega,
            checker_empty_execution s regs.1 emptyReg zeroReg,support_pure,Set.mem_singleton_iff] at reached
          subst result
          exact ⟨by change Exit.success≠Exit.unfinished;decide,by change 21≤_;omega,by change 0≤_;omega⟩
        · have nonzero : s.getReg .x17≠0#64 := by
            rw [regs.2.2.2.2.2.2]
            exact word_of_nat_ne _ _ lengthFit (by decide) zero
          exact failure 18 (by decide) (checker_empty_nonzero_rejects s regs.1
            (checker_seed_input_bounds input lower upper) emptyReg nonzero)
      · exact checker_initial_admitted_limits input empty lower upper fuel room reached
    · exact failure 13 (by decide) (checker_header_upper_rejects s regs.1 goodLow (highIff.mpr (by omega)))
  · exact failure 10 (by decide) (checker_header_lower_rejects s regs.1 (lowIff.mpr (by omega)))

theorem checker_run_limits (input : CheckInput) {result : Execution}
    (reached : result∈support (Artifact.submission.run .check input)) :
    result.exit≠.unfinished ∧ result.cycles≤112772+6800*input.positions.card ∧
      result.oracleCalls≤92*input.positions.card+min (8*input.positions.card) 255 := by
  by_cases valid : input.proof.length≤Artifact.submission.sizes.proof
  · have run : Artifact.submission.run .check input=execute (Artifact.submission.image .check)
        (Artifact.submission.steps .check) (Artifact.submission.initialState .check input) false := by
      simp [Submission.run,valid]
    rw [run] at reached
    exact checker_initial_limits input valid _ (checker_initial_budgets input).1 reached
  · have run : Artifact.submission.run .check input=pure ⟨.failure,initialMachine,0,0⟩ := by
      simp [Submission.run,valid]
    rw [run,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact ⟨by change Exit.failure≠Exit.unfinished;decide,by change 0≤_;omega,by change 0≤_;omega⟩

theorem checker_run_query_budget (input : CheckInput) {result : Execution}
    (reached : result∈support (Artifact.submission.run .check input)) :
    result.oracleCalls≤ CHECK_BUDGET input.positions.card := by
  have bounded := (checker_run_limits input reached).2.2
  have := Nat.min_le_left (8*input.positions.card) 255
  change result.oracleCalls≤100*input.positions.card
  omega

end CommitGolfCandidate.Chained.Native.RecordTail
