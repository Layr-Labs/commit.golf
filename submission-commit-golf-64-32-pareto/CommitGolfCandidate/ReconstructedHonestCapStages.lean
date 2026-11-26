import CommitGolf.Artifact
import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestCapStages
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRegisters HonestCuts
open CommitBlocks (addr)

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

abbrev Facts := List (Reg × Word)
abbrev Choice := Nat × Facts

def file : Facts → Known
  | [], _ => none
  | (r,v)::xs, k => if r = k then some v else file xs k

def holds (s : MachineState) (xs : Facts) := ∀ r v, (r,v) ∈ xs → s.getReg r = v

def describes (m : Known) (xs : Facts) := xs.all (fun (r,v) => m r == some v)

def alternatives (outputs : List Choice) (pc : Word) (m : Known) :=
  outputs.any (fun (i,fs) => (pc == addr i) && describes m fs)

def stops (pc : Word) := [1429,1449,1451,1469,1470,1483,1511,1512,1581,1602,1603,1610,1625,1626,1641].any
  (fun i => pc == addr i)

def checked (i : Nat) (inputs : Facts) (tracked : List Reg) (outputs : List Choice) (fee : Nat) :=
  HonestBlocks.check Artifact.openingCode stops (alternatives outputs) (fun _ r => tracked.contains r)
    fee (addr i) (file inputs) fee

@[simp] theorem holds_nil (s : MachineState) : holds s [] := by intro r v h; cases h

@[simp] theorem holds_cons (s : MachineState) (r : Reg) (v : Word) (xs : Facts) :
    holds s ((r,v)::xs) ↔ s.getReg r = v ∧ holds s xs := by
  constructor
  · intro h; exact ⟨h _ _ List.mem_cons_self,fun a b mem => h _ _ (List.mem_cons_of_mem _ mem)⟩
  · rintro ⟨head,tail⟩ a b mem
    rcases List.mem_cons.mp mem with same | rest
    · cases same; exact head
    · exact tail a b rest

private theorem valid_file (s : MachineState) (xs : Facts) (given : holds s xs) : Agrees s (file xs) := by
  induction xs with
  | nil => intro r v h; cases h
  | cons cell xs ih =>
    rcases cell with ⟨k,w⟩
    intro r v eq
    by_cases key : k = r
    · subst k; simp only [file,ite_true,Option.some.injEq] at eq
      exact eq ▸ given r w List.mem_cons_self
    · have rest := ih (fun a b h => given a b (List.mem_cons_of_mem _ h))
      exact rest _ v (by simpa only [file,ite_eq_right key] using eq)

/-- A verified table of acceptable control states holds on every real execution
that reaches its next cutpoint, with all untracked registers and RAM arbitrary. -/
theorem transfer (i : Nat) (inputs : Facts) (tracks : List Reg) (outputs : List Choice) (fee : Nat)
    (proof : checked i inputs tracks outputs fee = true) (s t : MachineState) (coins : Bool)
    (pc : s.pc = addr i) (given : holds s inputs)
    (path : Reaches (Artifact.submission.image .opening) coins stops s t) :
    ∃ c ∈ outputs, t.pc = addr c.1 ∧ holds t c.2 := by
  have h := postcondition Artifact.openingCode (Artifact.submission.image .opening)
    (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops _ _ fee _ _ fee proof coins s t pc
    (valid_file s inputs given) path
  obtain ⟨facts,accept,agree⟩ := h
  obtain ⟨c,mem,test⟩ := List.any_eq_true.mp accept
  rcases c with ⟨next,regs⟩
  simp only [Bool.and_eq_true,beq_iff_eq] at test
  refine ⟨_,mem,test.1,?_⟩
  intro r v h
  exact agree r v (beq_iff_eq.mp (List.all_eq_true.mp test.2 (r,v) h))

theorem transfer_single (i : Nat) (inputs : Facts) (tracks : List Reg) (j : Nat) (out : Facts) (fee : Nat)
    (proof : checked i inputs tracks [(j,out)] fee = true) (s t : MachineState) (coins : Bool)
    (pc : s.pc = addr i) (given : holds s inputs)
    (path : Reaches (Artifact.submission.image .opening) coins stops s t) : t.pc = addr j ∧ holds t out := by
  obtain ⟨c,m,whereAt,values⟩ := transfer _ _ _ _ _ proof s t coins pc given path
  obtain rfl := List.mem_singleton.mp m
  exact ⟨whereAt,values⟩

def pending (p : Nat) : Facts := [(.x20,BitVec.ofNat 64 p)]
def afterScan (p : Nat) : List Choice := [(1469,pending p),(1469,pending (p+1))]

/-- The cap pair body reaches its incremented-index guard. The pending counter
either stays unchanged or increases once, for every possible pair of input flags. -/
theorem scan_pending_table (p : Fin 257) : checked 1470 (pending p.val) [.x20] (afterScan p.val) 17 = true := by
  exact (by decide +kernel : ∀ i : Fin 257, checked 1470 (pending i.val) [.x20] (afterScan i.val) 17 = true) p

theorem scan_pending (p : Fin 257) (s t : MachineState) (coins : Bool) (pc : s.pc = addr 1470)
    (counter : s.getReg .x20 = BitVec.ofNat 64 p.val)
    (path : Reaches (Artifact.submission.image .opening) coins stops s t) :
    t.pc = addr 1469 ∧ (t.getReg .x20 = BitVec.ofNat 64 p.val ∨ t.getReg .x20 = BitVec.ofNat 64 (p.val+1)) := by
  have given : holds s (pending p.val) := by
    intro r v h; simp only [pending,List.mem_singleton,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h; exact counter
  obtain ⟨c,mem,whereAt,values⟩ := transfer _ _ _ _ _ (scan_pending_table p) s t coins pc given path
  simp only [afterScan,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl
  · exact ⟨whereAt,Or.inl (values _ _ List.mem_cons_self)⟩
  · exact ⟨whereAt,Or.inr (values _ _ List.mem_cons_self)⟩

end CommitGolfCandidate.Reconstruction.HonestCapStages
