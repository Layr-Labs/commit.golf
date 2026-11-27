import CommitGolfCandidate.Stage3cOpenMemory
import CommitGolfCandidate.Stage3cOpenCode
set_option Elab.async false

namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive CopySite where | salt | sibling (level : Fin 24)
deriving DecidableEq, Fintype

def CopySite.pc : CopySite → Nat
  | .salt => 470
  | .sibling level => 487+19*level.val

def CopySite.words : CopySite → Nat
  | .salt => 3 | _ => 4

def copyPair (s : MachineState) (i : Nat) :=
  let n := BitVec.ofNat 12 (8*i)
  execInstrBr (execInstrBr s (.LD .x28 .x6 n)) (.SD .x19 .x28 n)

private theorem enc (site : CopySite) (i : Fin 4) (inside : i.val<site.words) :
    decodeInstruction (openWord (site.pc+2*i.val)) = some (.base (.LD .x28 .x6 (BitVec.ofNat 12 (8*i.val)))) ∧
    decodeInstruction (openWord (site.pc+2*i.val+1)) = some (.base (.SD .x19 .x28 (BitVec.ofNat 12 (8*i.val)))) := by
  exact (by decide +kernel : ∀ k : CopySite, ∀ j : Fin 4, j.val<k.words →
    decodeInstruction (openWord (k.pc+2*j.val))=some (.base (.LD .x28 .x6 (BitVec.ofNat 12 (8*j.val)))) ∧
    decodeInstruction (openWord (k.pc+2*j.val+1))=some (.base (.SD .x19 .x28 (BitVec.ofNat 12 (8*j.val))))) site i inside

private theorem offset_eq (n : Nat) (lt : n<4) :
    signExtend12 (BitVec.ofNat 12 (8*n))=BitVec.ofNat 64 (8*n) := by interval_cases n <;> rfl

def AddrOK (a n : Nat) := a%8=0 ∧ a+n≤MEMORY_BYTES

private theorem access_word (a i : Nat) (ok : AddrOK a (8*(i+1))) :
    accessValid (BitVec.ofNat 64 (a+8*i)) 8 = true := by
  obtain ⟨al,r⟩ := ok
  have b : a+8*i < 2^64 := by unfold MEMORY_BYTES at r;omega
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt b,
    show a+8*i+8 ≤ MEMORY_BYTES by omega,show (a+8*i)%8=0 by omega,decide_true,Bool.true_and]

theorem copy_pair_run (site : CopySite) (i : Fin 4) (lt : i.val<site.words) (s : MachineState)
    (pc : s.pc=pcAt (site.pc+2*i.val)) (src dst : Nat)
    (sp : s.getReg .x6=BitVec.ofNat 64 src) (dp : s.getReg .x19=BitVec.ofNat 64 dst)
    (sa : AddrOK src (8*(i.val+1))) (da : AddrOK dst (8*(i.val+1))) :
    Runs s (copyPair s i.val) 2 2 := by
  let off := BitVec.ofNat 12 (8*i.val)
  let t := execInstrBr s (.LD .x28 .x6 off)
  have pt : t.pc=pcAt (site.pc+2*i.val+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have dp' : t.getReg .x19=BitVec.ofNat 64 dst := dp
  obtain ⟨x,y⟩ := enc site i lt
  have small : site.pc+2*i.val+1 < 939 := (by decide +kernel : ∀ k : CopySite,∀ j : Fin 4,k.pc+2*j.val+1<939) site i
  have sv : memoryArgumentsValid s (.LD .x28 .x6 off)=true := by
    change accessValid (s.getReg .x6+signExtend12 (BitVec.ofNat 12 (8*i.val))) 8 = true
    rw [sp,offset_eq _ i.isLt,←BitVec.ofNat_add];exact access_word _ _ sa
  have dv : memoryArgumentsValid t (.SD .x19 .x28 off)=true := by
    change accessValid (t.getReg .x19+signExtend12 (BitVec.ofNat 12 (8*i.val))) 8 = true
    rw [dp',offset_eq _ i.isLt,←BitVec.ofNat_add];exact access_word _ _ da
  dsimp only [off] at sv dv
  have first : Runs s t 1 1 := one _ (by omega) _ x _ _ pc (by simp only [ordinaryStep,sv,↓reduceIte];rfl)
  have last : Runs t (copyPair s i.val) 1 1 := one _ small _ y _ _ pt (by simp only [ordinaryStep,dv,↓reduceIte];rfl)
  exact first.trans last

theorem copy_pair_keeps (s : MachineState) (i : Nat) (r : Reg) (diff : Reg.x28≠r) :
    (copyPair s i).getReg r=s.getReg r := by
  have storeReg (q : MachineState) (a v : Word) : (q.setMem a v).getReg r=q.getReg r := by cases r <;> rfl
  simp only [copyPair,execInstrBr,MachineState.getReg_setPC,storeReg,MachineState.getReg_setReg_ne _ _ _ _ diff]

theorem copy_pair_pc (s : MachineState) (i : Nat) : (copyPair s i).pc=s.pc+8 := by
  change s.pc+4+4=_;rw [BitVec.add_assoc];rfl

theorem copy_word_effect (s : MachineState) (i : Nat) (small : i<4) (src dst a : Nat)
    (sp : s.getReg .x6=BitVec.ofNat 64 src) (dp : s.getReg .x19=BitVec.ofNat 64 dst)
    (aval : a<2^64) (dval : dst+8*i<2^64) :
    wordAt (copyPair s i) a = if a=dst+8*i then wordAt s (src+8*i) else wordAt s a := by
  change (if BitVec.ofNat 64 a == s.getReg .x19+signExtend12 (BitVec.ofNat 12 (8*i))
    then s.getMem (s.getReg .x6+signExtend12 (BitVec.ofNat 12 (8*i))) else s.getMem (BitVec.ofNat 64 a)) = _
  rw [sp,dp,offset_eq _ small,←BitVec.ofNat_add,←BitVec.ofNat_add]
  by_cases e : a=dst+8*i
  · subst a;simp [wordAt]
  · have ne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (dst+8*i) := by
      intro eq;have := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt aval,Nat.mod_eq_of_lt dval] at this;contradiction
    simp only [if_neg e,if_neg (fun h => ne (beq_iff_eq.mp h)),wordAt]

def copyWords (s : MachineState) : Nat → MachineState
  | 0 => s | n+1 => copyPair (copyWords s n) n

theorem copy_keeps (s : MachineState) (n : Nat) (r : Reg) (diff : Reg.x28≠r) :
    (copyWords s n).getReg r=s.getReg r := by
  induction n with
  | zero => rfl
  | succ n ih => exact (copy_pair_keeps _ _ _ diff).trans ih

theorem copy_pc (s : MachineState) (n : Nat) : (copyWords s n).pc = s.pc+BitVec.ofNat 64 (8*n) := by
  induction n with
  | zero => simp [copyWords]
  | succ n ih =>
    rw [copyWords,copy_pair_pc,ih,BitVec.add_assoc]
    change s.pc + (BitVec.ofNat 64 _ + BitVec.ofNat 64 8) = _
    rw [←BitVec.ofNat_add,Nat.mul_succ]

theorem copy_run (site : CopySite) (s : MachineState) (pc : s.pc=pcAt site.pc) (src dst : Nat)
    (sp : s.getReg .x6=BitVec.ofNat 64 src) (dp : s.getReg .x19=BitVec.ofNat 64 dst)
    (n : Nat) (hn : n≤site.words) (sa : AddrOK src (8*n)) (da : AddrOK dst (8*n)) :
    Runs s (copyWords s n) (2*n) (2*n) := by
  induction n with
  | zero => exact Runs.refl _
  | succ n ih =>
    have t : (copyWords s n).pc=pcAt (site.pc+2*n) := by
      rw [copy_pc,pc]; unfold pcAt; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have bound : site.words ≤ 4 := by cases site <;> simp [CopySite.words]
    have step := copy_pair_run site ⟨n,by omega⟩ (show n<site.words by omega) (copyWords s n) t src dst
      ((copy_keeps s n _ (by decide)).trans sp) ((copy_keeps s n _ (by decide)).trans dp) sa da
    simpa only [copyWords,Nat.mul_succ] using (ih (by omega) ⟨sa.1,by have := sa.2;omega⟩
      ⟨da.1,by have := da.2;omega⟩).trans step

end CommitGolfCandidate.Chained.BinaryMachine.Open
