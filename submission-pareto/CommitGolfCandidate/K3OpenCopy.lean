import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! Straight-line word copies `ld x31, 8a(src); sd x31, 8b(dst)` as used by the K3 prefix (level-22
sibling and record cell), with their effect on the word view. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 800000

/-- The word view after the copies: destination word `B+b` takes word `A+a` of `src`. -/
def pairView (m src : Memory) (A B : Nat) : List (Nat × Nat) → Memory
  | [] => m
  | (a,b)::rest => pairView (writeWord m (B+b) (src (A+a))) src A B rest

structure PairArgs (A B : Nat) (pairs : List (Nat × Nat)) : Prop where
  imm : ∀ p ∈ pairs, signExtend12 (BitVec.ofNat 12 (8*p.1)) = BitVec.ofNat 64 (8*p.1) ∧
    signExtend12 (BitVec.ofNat 12 (8*p.2)) = BitVec.ofNat 64 (8*p.2)
  room : ∀ p ∈ pairs, A+p.1 < 2^33 ∧ B+p.2 < 2^33
  apart : ∀ p ∈ pairs, ∀ q ∈ pairs, B+p.2 ≠ A+q.1

theorem PairArgs.tail {A B a b : Nat} {rest : List (Nat × Nat)} (h : PairArgs A B ((a,b)::rest)) :
    PairArgs A B rest :=
  ⟨fun p hp => h.imm p (List.mem_cons_of_mem _ hp), fun p hp => h.room p (List.mem_cons_of_mem _ hp),
   fun p hp q hq => h.apart p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)⟩

theorem pair_view_congr (pairs : List (Nat × Nat)) (m m' src src' : Memory) (A B : Nat)
    (room : ∀ p ∈ pairs, A+p.1 < 2^33 ∧ B+p.2 < 2^33)
    (same : ∀ w, w < 2^33 → m w = m' w) (sources : ∀ p ∈ pairs, src (A+p.1) = src' (A+p.1)) :
    ∀ w, w < 2^33 → pairView m src A B pairs w = pairView m' src' A B pairs w := by
  induction pairs generalizing m m' with
  | nil => exact same
  | cons p rest ih =>
    obtain ⟨a,b⟩ := p
    apply ih _ _ (fun q hq => room q (List.mem_cons_of_mem _ hq)) _ (fun q hq => sources q (List.mem_cons_of_mem _ hq))
    intro w hw
    have v := sources (a,b) (by simp)
    simp only [writeWord]
    split
    · exact v
    · exact same w hw

theorem pair_view_outside (pairs : List (Nat × Nat)) (m src : Memory) (A B w : Nat)
    (away : ∀ p ∈ pairs, w ≠ B+p.2) : pairView m src A B pairs w = m w := by
  induction pairs generalizing m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a,b⟩ := p
    rw [pairView, ih _ (fun q hq => away q (List.mem_cons_of_mem _ hq))]
    simp only [writeWord, if_neg (away (a,b) (by simp))]

/-- If every pair writing `B+b` reads `A+a`, the copied view holds the source word there. -/
theorem pair_view_inside (pairs : List (Nat × Nat)) (m src : Memory) (A B a b : Nat)
    (member : (a,b) ∈ pairs) (unique : ∀ p ∈ pairs, B+p.2 = B+b → p.1 = a) :
    pairView m src A B pairs (B+b) = src (A+a) := by
  induction pairs generalizing m with
  | nil => simp at member
  | cons p rest ih =>
    obtain ⟨a',b'⟩ := p
    rw [pairView]
    by_cases later : (a,b) ∈ rest
    · exact ih _ later (fun q hq => unique q (List.mem_cons_of_mem _ hq))
    · have here : (a,b) = (a',b') := by
        simp only [List.mem_cons] at member
        rcases member with h|h
        · exact h
        · exact absurd h later
      have far : ∀ q ∈ rest, B+b ≠ B+q.2 := by
        intro q hq eq
        have := unique q (List.mem_cons_of_mem _ hq) eq.symm
        obtain ⟨qa,qb⟩ := q
        simp only at this eq
        have : (qa,qb) = (a,b) := by rw [this]; congr 1; omega
        exact later (this ▸ hq)
      rw [pair_view_outside _ _ _ _ _ _ far]
      simp only [Prod.mk.injEq] at here
      obtain ⟨rfl,rfl⟩ := here
      simp [writeWord]

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg open_zero MachineState.getMem_setPC MachineState.getMem_setReg

private theorem load_address (s : MachineState) (src : Reg) (A a : Nat) (rs : s.getReg src = wordAddress A)
    (imm : signExtend12 (BitVec.ofNat 12 (8*a)) = BitVec.ofNat 64 (8*a)) :
    s.getReg src + signExtend12 (BitVec.ofNat 12 (8*a)) = wordAddress (A+a) := by
  rw [rs, imm, wordAddress_add]; rfl

private theorem valid_word (w : Nat) (room : w < 2^33) : accessValid (wordAddress w) 8 = true :=
  Opening.aligned_access (8*w) (by omega) (by unfold MEMORY_BYTES; omega)

private def loaded (s : MachineState) (src : Reg) (a : Nat) := execInstrBr s (.LD .x31 src (BitVec.ofNat 12 (8*a)))
private def stored (s : MachineState) (dst : Reg) (b : Nat) := execInstrBr s (.SD dst .x31 (BitVec.ofNat 12 (8*b)))

private theorem load_facts (s : MachineState) (src : Reg) (A a : Nat) (rs : s.getReg src = wordAddress A)
    (imm : signExtend12 (BitVec.ofNat 12 (8*a)) = BitVec.ofNat 64 (8*a)) (room : A+a < 2^33) :
    ordinaryStep s (.base (.LD .x31 src (BitVec.ofNat 12 (8*a)))) = some (loaded s src a) ∧
    (loaded s src a).pc = s.pc+4 ∧ (loaded s src a).mem = s.mem ∧
    (loaded s src a).getReg .x31 = s.getMem (wordAddress (A+a)) ∧
    (∀ r, r ≠ .x31 → (loaded s src a).getReg r = s.getReg r) := by
  have ad := load_address s src A a rs imm
  have ok := valid_word (A+a) room
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, ad, ok, loaded]
  · simp [loaded, execInstrBr]
  · simp [loaded, execInstrBr]
  · simp [loaded, execInstrBr, ad]
  · intro r ne; simp [loaded, execInstrBr, Ne.symm ne]

private theorem store_facts (s : MachineState) (dst : Reg) (B b : Nat) (rd : s.getReg dst = wordAddress B)
    (imm : signExtend12 (BitVec.ofNat 12 (8*b)) = BitVec.ofNat 64 (8*b)) (room : B+b < 2^33) :
    ordinaryStep s (.base (.SD dst .x31 (BitVec.ofNat 12 (8*b)))) = some (stored s dst b) ∧
    (stored s dst b).pc = s.pc+4 ∧
    (stored s dst b).mem = (s.setMem (wordAddress (B+b)) (s.getReg .x31)).mem ∧
    (∀ r, (stored s dst b).getReg r = s.getReg r) := by
  have ad := load_address s dst B b rd imm
  have ok := valid_word (B+b) room
  refine ⟨?_,?_,?_,?_⟩
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, ad, ok, stored]
  · simp [stored, execInstrBr]
  · simp [stored, execInstrBr, ad]
  · intro r; simp [stored, execInstrBr]

theorem pair_rows_run (pairs : List (Nat × Nat)) (s : MachineState) (start : Nat) (src dst : Reg) (A B : Nat)
    (hs : src ≠ .x31) (hd : dst ≠ .x31) (pc : s.pc = address start)
    (rs : s.getReg src = wordAddress A) (rd : s.getReg dst = wordAddress B) (args : PairArgs A B pairs) :
    legal (pairRows start src dst pairs) s ∧
      (walkRows s (pairRows start src dst pairs)).pc = address (start+2*pairs.length) ∧
      (∀ r, r ≠ .x31 → (walkRows s (pairRows start src dst pairs)).getReg r = s.getReg r) ∧
      (∀ w, w < 2^33 → memoryView (walkRows s (pairRows start src dst pairs)) w =
        pairView (memoryView s) (memoryView s) A B pairs w) := by
  induction pairs generalizing s start with
  | nil =>
    refine ⟨trivial, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [pairRows, walkRows, List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]; exact pc
  | cons p rest ih =>
    obtain ⟨a,b⟩ := p
    have imm := args.imm (a,b) (by simp)
    have room := args.room (a,b) (by simp)
    let l := loaded s src a
    let t := stored l dst b
    obtain ⟨lo,lpc,lmem,lval,lkeep⟩ := load_facts s src A a rs imm.1 room.1
    have lrd : l.getReg dst = wordAddress B := (lkeep dst hd).trans rd
    obtain ⟨so,spc,smem,skeep⟩ := store_facts l dst B b lrd imm.2 room.2
    have tpc : t.pc = address (start+2) := by
      change (stored l dst b).pc = _; rw [spc, lpc, pc, address_succ, address_succ]
    have treg (r : Reg) (ne : r ≠ .x31) : t.getReg r = s.getReg r := (skeep r).trans (lkeep r ne)
    have tview : ∀ w, w < 2^33 → memoryView t w = writeWord (memoryView s) (B+b) (memoryView s (A+a)) w := by
      intro w hw
      change t.mem (wordAddress w) = _
      rw [show t.mem = _ from smem]
      change (l.setMem (wordAddress (B+b)) (l.getReg .x31)).getMem (wordAddress w) = _
      rw [lval]
      have st := memory_at_store (state := l) (address := B+b) (index := w) (value := s.getMem (wordAddress (A+a)))
        (by omega) (by omega)
      change memoryView (l.setMem (wordAddress (B+b)) (s.getMem (wordAddress (A+a)))) w = _ at st
      unfold memoryView at st ⊢
      rw [st]
      simp only [writeWord]
      split
      · rfl
      · change l.mem (wordAddress w) = s.mem (wordAddress w); rw [show l.mem = s.mem from lmem]
    obtain ⟨ok,rpc,rkeep,rview⟩ := ih t (start+2) tpc ((treg src hs).trans rs) ((treg dst hd).trans rd) args.tail
    have walk : walkRows s (pairRows start src dst ((a,b)::rest)) = walkRows t (pairRows (start+2) src dst rest) := rfl
    refine ⟨⟨pc, lo, lpc.trans (by rw [pc]; exact address_succ start), so, ?_⟩, ?_, ?_, ?_⟩
    · exact ok
    · rw [walk, rpc, List.length_cons]; congr 1; omega
    · intro r ne; rw [walk, rkeep r ne]; exact treg r ne
    · intro w hw
      rw [walk, rview w hw, pairView]
      refine pair_view_congr rest _ _ _ _ A B (fun q hq => args.room q (List.mem_cons_of_mem _ hq)) tview ?_ w hw
      intro q hq
      rw [tview _ (args.room q (List.mem_cons_of_mem _ hq)).1]
      simp only [writeWord, if_neg (args.apart (a,b) (by simp) q (List.mem_cons_of_mem _ hq)).symm]

end TwoPermutationPrototype.GroupedOpening
