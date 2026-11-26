import CommitGolf.Artifact
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.Reconstruction.HonestCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000

def image (check : Bool) := Artifact.submission.image (if check then .check else .opening)
def wordCount (check : Bool) : Nat := if check then 126 else 50
def srcBase (check : Bool) : Nat := 2^36 - 8 * wordCount check
def dstBase : Nat := 2097152
private def w (n : Nat) := BitVec.ofNat 64 n
private def ops (check : Bool) : List Instr :=
  [.BNE .x16 .x0 20,
   .AUIPC .x6 0x1ff,.ADDI .x6 .x6 0xfec,.AUIPC .x7 0x1ff,
   .ADDI .x7 .x7 (if check then 0x3d4 else 0x174),.ADDI .x28 .x2 0,
   .BEQ .x6 .x7 24,.LD .x29 .x28 0,.SD .x6 .x29 0,.ADDI .x28 .x28 8,
   .ADDI .x6 .x6 8,.JAL .x0 2097132,
   .ADDI .x10 .x16 0,.ADDI .x11 .x17 0,.AUIPC .x1 0,.JALR .x1 .x1 24]

private def pc (i : Nat) := if i = 0 then 4096 else 4096 + 4 * (i+4)

private theorem table (c : Bool) (i : Fin 16) :
    ((image c).code[(if i.val = 0 then 0 else i.val+4)]?).bind decodeInstruction =
      some (.base ((ops c)[i.val]?.getD .EBREAK)) := by
  cases c <;> fin_cases i <;> rfl

private theorem fetch_at (c : Bool) (i : Fin 16) (s : MachineState)
    (atPc : s.pc = w (pc i.val)) :
    fetch (image c) s = some (.base ((ops c)[i.val]?.getD .EBREAK)) := by
  let n := if i.val = 0 then 0 else i.val+4
  have hs := i.isLt
  have index : s.pc.toNat = 4096+4*n := by
    rw [atPc]; simp only [pc, w, BitVec.toNat_ofNat, n]
    split <;> omega
  rw [fetch, index, ite_eq_left (by omega), show (4096+4*n-4096)/4=n by omega]
  have h := table c i
  change ((image c).code[n]?).bind _ = _ at h
  cases hword : (image c).code[n]? <;> simp_all

private def runOps (s : MachineState) (ls : List Instr) (n : Nat) := (ls.take n).foldl execInstrBr s

def start (c : Bool) (s : MachineState) := runOps s (ops c) 6

theorem start_run (c : Bool) (s : MachineState) (p : s.pc = 4096)
    (nonempty : s.getReg .x16 ≠ 0) (fuel : Nat) (coins : Bool) :
    execute (image c) (6+fuel) s coins =
    (do let r ← execute (image c) fuel (start c s) coins; return r.charge 6 0) := by
  apply execute_unit_steps (states := runOps s (ops c))
  intro i hi
  refine ⟨.base ((ops c)[i]?.getD .EBREAK), fetch_at c ⟨i,by omega⟩ _ ?_, ?_, ?_⟩
  · have count : s.regs .x16 ≠ 0#64 := nonempty
    cases c <;> interval_cases i <;> simp [runOps, ops, pc, w, execInstrBr,
      MachineState.setPC, MachineState.getReg, count, p, signExtend13]
  · cases c <;> interval_cases i <;> rfl
  · cases c <;> interval_cases i <;> rfl

theorem start_regs (c : Bool) (s : MachineState) (p : s.pc = 4096)
    (nonempty : s.getReg .x16 ≠ 0) (stack : s.getReg .x2 = w (srcBase c)) :
    (start c s).pc = 4136 ∧ (start c s).getReg .x6 = w dstBase ∧
    (start c s).getReg .x7 = w (dstBase + 8*wordCount c) ∧
    (start c s).getReg .x28 = w (srcBase c) ∧ (start c s).mem = s.mem := by
  have count : s.regs .x16 ≠ 0#64 := nonempty
  have stk : s.regs .x2 = w (srcBase c) := stack
  cases c <;> simp [start, runOps, ops, execInstrBr, MachineState.setPC, MachineState.setReg,
    MachineState.getReg, signExtend12, signExtend13, w, count, p, srcBase, dstBase, wordCount] at stk ⊢ <;> exact stk

private def body : List Instr := [.BEQ .x6 .x7 24,.LD .x29 .x28 0,.SD .x6 .x29 0,
  .ADDI .x28 .x28 8,.ADDI .x6 .x6 8,.JAL .x0 2097132]
def loopStep (s : MachineState) := runOps s body 6
def ptr (base i : Nat) := w (base + 8*i)

private theorem word_nat (c : Bool) (i : Nat) (hi : i < wordCount c) :
    (ptr (srcBase c) i).toNat = srcBase c + 8*i ∧
    (ptr dstBase i).toNat = dstBase+8*i ∧
    ptr dstBase i ≠ ptr dstBase (wordCount c) ∧
    accessValid (ptr (srcBase c) i) 8 = true ∧ accessValid (ptr dstBase i) 8 = true := by
  have loc : ∀ b : Bool, srcBase b + 8 * wordCount b = 2^36 := by decide
  have fits : ∀ b : Bool, wordCount b ≤ 126 := by decide
  have align : ∀ b : Bool, srcBase b % 8 = 0 := by decide
  have hs := loc c
  have n := fits c
  have sa := align c
  have f₁ : srcBase c + 8*i < 2^64 := by omega
  have f₂ : dstBase + 8*i < 2^64 := by unfold dstBase; omega
  have endfits : dstBase + 8*wordCount c < 2^64 := by unfold dstBase; omega
  have a : (ptr (srcBase c) i).toNat = srcBase c + 8*i := by
    simp only [ptr, w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt f₁]
  have b : (ptr dstBase i).toNat = dstBase + 8*i := by
    simp only [ptr, w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt f₂]
  refine ⟨a,b,?_,?_,?_⟩
  · intro eq
    have vals := congrArg BitVec.toNat eq
    simp only [ptr, w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt f₂, Nat.mod_eq_of_lt endfits] at vals
    omega
  · simp [accessValid, rangeValid, MEMORY_BYTES, a]; omega
  · simp only [accessValid, rangeValid, MEMORY_BYTES, b, Bool.and_eq_true, decide_eq_true_eq]
    unfold dstBase
    omega


theorem loop_step_run (c : Bool) (i : Nat) (hi : i < wordCount c) (s : MachineState)
    (p : s.pc = 4136) (dst : s.getReg .x6 = ptr dstBase i)
    (stop : s.getReg .x7 = ptr dstBase (wordCount c))
    (src : s.getReg .x28 = ptr (srcBase c) i) (fuel : Nat) (coins : Bool) :
    execute (image c) (6+fuel) s coins =
    (do let r ← execute (image c) fuel (loopStep s) coins; return r.charge 6 0) := by
  obtain ⟨_, _, ne, srcOK, dstOK⟩ := word_nat c i hi
  have regs : s.regs .x6 ≠ s.regs .x7 := by
    change s.getReg .x6 ≠ s.getReg .x7
    rwa [dst, stop]
  have s28 : s.regs .x28 = ptr (srcBase c) i := src
  have s6 : s.regs .x6 = ptr dstBase i := dst
  have s7 : s.regs .x7 = ptr dstBase (wordCount c) := stop
  apply execute_unit_steps (states := runOps s body)
  intro j hj
  refine ⟨.base (body[j]?.getD .EBREAK), ?_, ?_, ?_⟩
  · have eq : (ops c)[6+j]?.getD .EBREAK = body[j]?.getD .EBREAK := by
      cases c <;> interval_cases j <;> rfl
    rw [← eq]
    apply fetch_at c ⟨6+j,by omega⟩
    interval_cases j <;> simp [runOps, body, execInstrBr, MachineState.setPC, MachineState.setMem,
      MachineState.getReg, pc, w, p, regs]
  · interval_cases j <;> simp [runOps, body, ordinaryStep, memoryArgumentsValid, memAccess,
      execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg, s28, s6, s7, ne,
      signExtend12, srcOK, dstOK]
  · interval_cases j <;> rfl

theorem loop_step_effects (s : MachineState) (p : s.pc = 4136)
    (ne : s.regs .x6 ≠ s.regs .x7) :
    (loopStep s).pc = 4136 ∧
    (loopStep s).regs .x6 = s.regs .x6 + 8 ∧
    (loopStep s).regs .x28 = s.regs .x28 + 8 ∧
    (∀ r, r ≠ .x6 → r ≠ .x28 → r ≠ .x29 → (loopStep s).getReg r = s.getReg r) ∧
    (∀ a, (loopStep s).getMem a =
      if a = s.regs .x6 then s.getMem (s.regs .x28) else s.getMem a) := by
  simp [loopStep, runOps, body, execInstrBr, MachineState.setPC, MachineState.setReg,
    MachineState.setMem, MachineState.getReg, MachineState.getMem, signExtend12,
    ne, p, signExtend21]
  intro r r6 r28 r29
  cases r <;> simp_all

private theorem ptr_succ (base i : Nat) : ptr base i + 8 = ptr base (i+1) := by
  change BitVec.ofNat 64 (base+8*i) + BitVec.ofNat 64 8 = BitVec.ofNat 64 (base+8*(i+1))
  rw [← BitVec.ofNat_add, show base+8*i+8 = base+8*(i+1) by omega]

def copied (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => copied (loopStep s) n

/-- The executable performs exactly six unit-cycle instructions per table word.
The statement holds for any prefix of the copy and all following fuel. -/
theorem copy_many (c : Bool) (n i : Nat) (bound : i+n ≤ wordCount c)
    (s : MachineState) (p : s.pc = 4136) (dst : s.getReg .x6 = ptr dstBase i)
    (stop : s.getReg .x7 = ptr dstBase (wordCount c)) (src : s.getReg .x28 = ptr (srcBase c) i)
    (fuel : Nat) (coins : Bool) :
    execute (image c) (6*n+fuel) s coins =
    (do let r ← execute (image c) fuel (copied s n) coins; return r.charge (6*n) 0) := by
  induction n generalizing i s with
  | zero => simp [copied, Execution.charge]
  | succ n ih =>
    have hi : i < wordCount c := by omega
    have ne : s.regs .x6 ≠ s.regs .x7 := by
      change s.getReg .x6 ≠ s.getReg .x7
      rw [dst, stop]; exact (word_nat c i hi).2.2.1
    obtain ⟨p',dst',src',regs',_⟩ := loop_step_effects s p ne
    change (loopStep s).getReg .x6 = s.getReg .x6 + 8 at dst'
    change (loopStep s).getReg .x28 = s.getReg .x28 + 8 at src'
    rw [dst,ptr_succ] at dst'
    rw [src,ptr_succ] at src'
    have nextStop := (regs' .x7 (by decide) (by decide) (by decide)).trans stop
    rw [show 6*(n+1)+fuel = 6+(6*n+fuel) by omega,
      loop_step_run c i hi s p dst stop src _ coins,
      ih (i+1) (by omega) (loopStep s) p' dst' nextStop src']
    simp [copied, Execution.charge, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm]

private theorem pointer_facts (c : Bool) (i j : Nat)
    (hi : i ≤ wordCount c) (hj : j ≤ wordCount c) :
    (ptr dstBase i = ptr dstBase j → i = j) ∧ ptr (srcBase c) j ≠ ptr dstBase i := by
  have n := (by decide : ∀ b : Bool, wordCount b ≤ 126) c
  have endAt := (by decide : ∀ b : Bool, srcBase b + 8 * wordCount b = 2^36) c
  have above := (by decide : ∀ b : Bool, 2^35 < srcBase b) c
  have s : srcBase c + 8*j < 2^64 := by omega
  have a : dstBase + 8*i < 2^64 := by unfold dstBase; omega
  have b : dstBase + 8*j < 2^64 := by unfold dstBase; omega
  constructor <;> intro eq <;> have v := congrArg BitVec.toNat eq <;>
    simp only [ptr,w,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt s] at v <;>
    unfold dstBase at v <;> omega

structure CopyInv (c : Bool) (initial current : MachineState) (i n : Nat) : Prop where
  pc_at : current.pc = 4136
  destination : current.getReg .x6 = ptr dstBase (i+n)
  last : current.getReg .x7 = ptr dstBase (wordCount c)
  source : current.getReg .x28 = ptr (srcBase c) (i+n)
  regs : ∀ r, r ≠ .x6 → r ≠ .x28 → r ≠ .x29 → current.getReg r = initial.getReg r
  word : ∀ j < n, current.getMem (ptr dstBase (i+j)) = initial.getMem (ptr (srcBase c) (i+j))
  frame : ∀ a, (∀ j < n, a ≠ ptr dstBase (i+j)) → current.getMem a = initial.getMem a

/-- The actual load/store sequence copies exactly this prefix of the embedded table.
All other memory is unchanged, including trapdoor bytes and serialized positions. -/
theorem copy_effects (c : Bool) (n i : Nat) (bound : i+n ≤ wordCount c)
    (s : MachineState) (p : s.pc = 4136) (dst : s.getReg .x6 = ptr dstBase i)
    (stop : s.getReg .x7 = ptr dstBase (wordCount c)) (src : s.getReg .x28 = ptr (srcBase c) i) :
    CopyInv c s (copied s n) i n := by
  induction n generalizing i s with
  | zero => exact ⟨p,dst,stop,src,by simp [copied],by simp,by simp [copied]⟩
  | succ n ih =>
    have hi : i < wordCount c := by omega
    have ne : s.regs .x6 ≠ s.regs .x7 := by
      change s.getReg .x6 ≠ s.getReg .x7
      rw [dst, stop]; exact (word_nat c i hi).2.2.1
    obtain ⟨p',dst',src',regs',mem'⟩ := loop_step_effects s p ne
    change (loopStep s).getReg .x6 = s.getReg .x6 + 8 at dst'
    change (loopStep s).getReg .x28 = s.getReg .x28 + 8 at src'
    rw [dst,ptr_succ] at dst'
    rw [src,ptr_succ] at src'
    have nextStop := (regs' .x7 (by decide) (by decide) (by decide)).trans stop
    have tail := ih (i+1) (by omega) (loopStep s) p' dst' nextStop src'
    change ∀ a, (loopStep s).getMem a =
      if a = s.getReg .x6 then s.getMem (s.getReg .x28) else s.getMem a at mem'
    simp only [dst, src] at mem'
    have shift (j : Nat) : i+1+j = i+(j+1) := by omega
    refine ⟨tail.pc_at, (shift n) ▸ tail.destination, tail.last,
      (shift n) ▸ tail.source, ?_, ?_, ?_⟩
    · exact fun r h₁ h₂ h₃ => (tail.regs r h₁ h₂ h₃).trans (regs' r h₁ h₂ h₃)
    · intro j hj
      cases j with
      | zero =>
        have untouched := tail.frame (ptr dstBase i) (fun k hk h => by
          have bad := (pointer_facts c i (i+1+k) (by omega) (by omega)).1 h
          omega)
        exact untouched.trans (by simp only [mem', ite_true, Nat.add_zero])
      | succ j =>
        have word := tail.word j (by omega)
        rw [shift j, mem', ite_eq_right (pointer_facts c i (i+(j+1)) (by omega) (by omega)).2] at word
        exact word
    · intro a outside
      have unchanged := tail.frame a (fun j hj => (shift j).symm ▸ outside (j+1) (by omega))
      have other : a ≠ ptr dstBase i := by simpa only [Nat.add_zero] using outside 0 (by omega)
      exact unchanged.trans (by rw [mem', ite_eq_right other])

private def exits : List Instr := [.BEQ .x6 .x7 24,.ADDI .x10 .x16 0,
  .ADDI .x11 .x17 0,.AUIPC .x1 0,.JALR .x1 .x1 24]
private def exitIndex (i : Nat) := if i = 0 then 6 else 11+i
def callState (s : MachineState) := runOps s exits 5

private theorem finish_copy (c : Bool) (s : MachineState)
    (p : s.pc = 4136) (eq : s.regs .x6 = s.regs .x7) (fuel : Nat) (coins : Bool) :
    execute (image c) (5+fuel) s coins =
      (do let r ← execute (image c) fuel (callState s) coins; return r.charge 5 0) := by
  apply execute_unit_steps (states := runOps s exits)
  intro i hi
  have idx : exitIndex i < 16 := by unfold exitIndex; split <;> omega
  have same : (ops c)[exitIndex i]?.getD .EBREAK = exits[i]?.getD .EBREAK := by
    cases c <;> interval_cases i <;> rfl
  refine ⟨.base (exits[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · rw [← same]
    apply fetch_at c ⟨exitIndex i, idx⟩
    interval_cases i <;> simp [runOps, exits, pc, exitIndex, w, execInstrBr, MachineState.setPC,
      MachineState.getReg, eq, p, signExtend13]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem call_effects (s : MachineState) (p : s.pc = 4136)
    (eq : s.regs .x6 = s.regs .x7) :
    (callState s).pc = 4192 ∧ (callState s).getReg .x1 = 4176 ∧
    (callState s).getReg .x10 = s.getReg .x16 ∧ (callState s).getReg .x11 = s.getReg .x17 ∧
    (callState s).getReg .x2 = s.getReg .x2 ∧ (callState s).mem = s.mem := by
  simp [callState, runOps, exits, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, eq, p, signExtend12, signExtend13]

private theorem start_inputs (c : Bool) (s : MachineState)
    (nonempty : s.getReg .x16 ≠ 0) :
    (start c s).getReg .x16 = s.getReg .x16 ∧ (start c s).getReg .x17 = s.getReg .x17 ∧
    (start c s).getReg .x2 = s.getReg .x2 := by
  have count : s.regs .x16 ≠ 0#64 := nonempty
  cases c <;> simp [start, runOps, ops, execInstrBr, MachineState.setPC, MachineState.setReg,
    MachineState.getReg, count]

def ready (c : Bool) (s : MachineState) := callState (copied (start c s) (wordCount c))

/-- Complete nonempty entry protocol for the delivered opening and checker: copy
image constants from the ABI stack into the linked table and enter the C body. -/
theorem enter_body (c : Bool) (s : MachineState) (p : s.pc = 4096)
    (nonempty : s.getReg .x16 ≠ 0) (stack : s.getReg .x2 = w (srcBase c)) (fuel : Nat)
    (coins : Bool) :
    let t := ready c s
    execute (image c) ((11+6*wordCount c)+fuel) s coins =
      (do let r ← execute (image c) fuel t coins; return r.charge (11+6*wordCount c) 0) ∧
    t.pc = 4192 ∧ t.getReg .x1 = 4176 ∧ t.getReg .x10 = s.getReg .x16 ∧
    t.getReg .x11 = s.getReg .x17 ∧ t.getReg .x2 = s.getReg .x2 ∧
    (∀ j < wordCount c, t.getMem (ptr dstBase j) = s.getMem (ptr (srcBase c) j)) ∧
    (∀ a, (∀ j < wordCount c, a ≠ ptr dstBase j) → t.getMem a = s.getMem a) := by
  obtain ⟨p',dst,stop,src,mem⟩ := start_regs c s p nonempty stack
  let initial := start c s
  have dst' : initial.getReg .x6 = ptr dstBase 0 := dst
  have src' : initial.getReg .x28 = ptr (srcBase c) 0 := src
  let done := copied initial (wordCount c)
  have facts := copy_effects c (wordCount c) 0 (by omega) initial p' dst' stop src'
  have donePC : done.pc = 4136 := facts.pc_at
  have eq : done.regs .x6 = done.regs .x7 := by
    change done.getReg .x6 = done.getReg .x7
    exact (by simpa only [Nat.zero_add] using facts.destination : done.getReg .x6 = ptr dstBase (wordCount c)) |>.trans facts.last.symm
  obtain ⟨pcBody,ra,a0,a1,sp,frame⟩ := call_effects done donePC eq
  obtain ⟨count,len,stackKept⟩ := start_inputs c s nonempty
  have regr (r : Reg) (a : r ≠ .x6) (b : r ≠ .x28) (d : r ≠ .x29) :
      done.getReg r = initial.getReg r := facts.regs r a b d
  refine ⟨?_,pcBody,ra,a0.trans ((regr _ (by decide) (by decide) (by decide)).trans count),
    a1.trans ((regr _ (by decide) (by decide) (by decide)).trans len),
    sp.trans ((regr _ (by decide) (by decide) (by decide)).trans stackKept), ?_, ?_⟩
  · rw [show 11+6*wordCount c+fuel = 6+(6*wordCount c+(5+fuel)) by omega,
      start_run c s p nonempty]
    rw [copy_many c (wordCount c) 0 (by omega) initial p' dst' stop src',
      finish_copy c done donePC eq]
    simp [ready, done, initial, Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [show 5+(6+6*wordCount c) = 11+6*wordCount c by omega]
  · intro j hj
    have srcMem := congrFun mem (ptr (srcBase c) j)
    have copyMem := facts.word j hj
    have finalMem := congrFun frame (ptr dstBase j)
    exact finalMem.trans ((by simpa only [Nat.zero_add] using copyMem : done.getMem _ = initial.getMem _).trans srcMem)
  · intro a outside
    have unchanged := facts.frame a (by simpa only [Nat.zero_add] using outside)
    exact (congrFun frame a).trans (unchanged.trans (congrFun mem a))

end CommitGolfCandidate.Reconstruction.HonestCopy
