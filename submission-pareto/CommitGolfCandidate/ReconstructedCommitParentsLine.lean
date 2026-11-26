import CommitGolfCandidate.ReconstructedCommitParentsImage
import CommitGolfCandidate.ReconstructedCommitParentsMemory

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitExact
open Image (Atom)

def Loaded (im : CommitGolf.Riscv.Image) (p : Word) (ops : List Atom) :=
  ∀ j : Fin ops.length, ∀ s : MachineState,
    s.pc = p + BitVec.ofNat 64 (4*j.val) → fetch im s = some (.base ops[j.val].op)

theorem Loaded.head {im p a ops} (hs : Loaded im p (a::ops)) (s : MachineState) (pc : s.pc = p) :
    fetch im s = some (.base a.op) :=
  hs 0 s (by simpa using pc)

theorem Loaded.tail {im p a ops} (hs : Loaded im p (a::ops)) :
    Loaded im (p+4) ops := by
  intro j s pc
  apply hs ⟨j+1,by simp⟩ s
  change s.pc = p + BitVec.ofNat 64 (4*(j.val+1))
  rw [pc,BitVec.add_assoc,show 4*(j.val+1) = 4+4*j.val by omega,BitVec.ofNat_add]
  rfl

theorem Loaded.split {im p xs ys} (hs : Loaded im p (xs++ys)) :
    Loaded im p xs ∧ Loaded im (p+BitVec.ofNat 64 (4*xs.length)) ys := by
  constructor
  · intro j s pc
    have := hs ⟨j.val,by simp;omega⟩ s pc
    simpa only [List.getElem_append_left j.isLt] using this
  · intro j s pc
    have ix : xs.length+j.val < (xs++ys).length := by simp
    have off : s.pc = p+BitVec.ofNat 64 (4*(xs.length+j.val)) := by
      rw [pc,BitVec.add_assoc,←BitVec.ofNat_add,Nat.mul_add]
    have h := hs ⟨xs.length+j.val,ix⟩ s off
    simpa only [List.getElem_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left] using h

def runPlain (s : MachineState) : List Atom → MachineState
  | [] => s
  | a::ops => runPlain (execInstrBr s a.op) ops

def ready (s : MachineState) : List Atom → Prop
  | [] => True
  | a::ops => a ≠ .compress ∧ memoryArgumentsValid s a.op = true ∧ ready (execInstrBr s a.op) ops

theorem nojump {a : Atom} (notCall : a≠.compress) (s : MachineState) :
    (execInstrBr s a.op).pc = s.pc+4 := by cases a <;> first | rfl | contradiction

theorem plain_segment (o : Oracle) (im : CommitGolf.Riscv.Image) (s : MachineState) (ops : List Atom)
    (f : Loaded im s.pc ops) (ok : ready s ops) :
    Segment o im ops.length s (runPlain s ops) ∧ (runPlain s ops).pc = s.pc + BitVec.ofNat 64 (4*ops.length) := by
  induction ops generalizing s with
  | nil => exact ⟨empty _ _ _,(BitVec.add_zero _).symm⟩
  | cons a ops ih =>
    obtain ⟨notCall,allowed,tail⟩ := ok
    have step : ordinaryStep s (.base a.op) = some (execInstrBr s a.op) := by
      cases a <;> first | contradiction | exact ite_eq_left allowed
    have head := plain o im s _ _ (f.head s rfl) step
    have pc := nojump notCall s
    have rem := f.tail
    rw [←pc] at rem
    obtain ⟨seg,done⟩ := ih _ rem tail
    constructor
    · simpa only [List.length_cons,Nat.one_add,Nat.succ_eq_add_one,runPlain] using compose head seg
    · change _ = s.pc+BitVec.ofNat 64 (4*(ops.length+1))
      rw [runPlain,done,pc,BitVec.add_assoc,show 4*(ops.length+1) = 4+4*ops.length by omega,BitVec.ofNat_add]
      rfl

end CommitGolfCandidate.Reconstruction.CommitParents
