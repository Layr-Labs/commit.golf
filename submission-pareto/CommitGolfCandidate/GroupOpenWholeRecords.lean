import CommitGolfCandidate.GroupOpenWholeNode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
set_option maxRecDepth 18000

def runNodes (c first : Nat) : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => if live : first<14 then runNodes c (first+1) n (step c ⟨first,live⟩ s) else s

theorem point_mono (c : Fin 4) (a b : Nat) (lo : a≤b) (hi : b≤14) : point c a≤point c b := by
  have h : ∀ c : Fin 4, ∀ a b : Fin 15, a.val≤b.val → point c a≤point c b := by decide
  exact h c ⟨a,by omega⟩ ⟨b,by omega⟩ lo

private theorem payload_stable {s t : MachineState} (i : Index) (l b : Nat) (small : b<siblingWidth l)
    (input : ∀ a<proofBase,t.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a))
    (key : t.getReg .x10=s.getReg .x10) : payload t i l b=payload s i l b := by
  have src:=(sibling_address_inside i l).2.2
  have sep : nonceBase<proofBase := by decide
  have size:=sibling_width_le l
  unfold payload
  split
  · rw [tag,tag,key,half_from_words input _ (by omega)]
  · exact byte_from_words input _ (by omega)

structure RangeResult (s u : MachineState) (i : Index) (o first n : Nat) : Prop where
  run : RunsOpeningBlock s u (point (pageClass o) (first+n)-point (pageClass o) first)
  next : WholeCursor u i o (first+n)
  kept : ∀ r,r≠.x6 → r≠.x7 → r≠.x21 → r≠.x31 → r≠.x29 → u.getReg r=s.getReg r
  input : ∀ a<proofBase,u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)
  frame : ∀ a<2^64, a<siblingDestination o first ∨ siblingDestination o (first+n)≤a →
    u.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a)
  fields : ∀ l, first≤l → l<first+n → ∀ b<siblingWidth l,
    u.getByte (BitVec.ofNat 64 (siblingDestination o l+b))=payload s i l b

theorem run_nodes (s : MachineState) (i : Index) (o first n : Nat) (oBound : o<LENGTH) (bound : first+n≤14)
    (cursor : WholeCursor s i o first) (ptr : first=0 → ZeroInput s i) :
    RangeResult s (runNodes (pageClass o) first n s) i o first n := by
  let c : Fin 4:=⟨pageClass o,class_lt o⟩
  induction n generalizing s first with
  | zero =>
    refine ⟨?_,cursor,fun _ _ _ _ _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl,?_⟩
    · simpa [runNodes] using run_zero s
    · intro l hl hh;omega
  | succ n ih =>
    have live : first<14 := by omega
    let l : Fin 14:=⟨first,live⟩
    let m:=step c l s
    have a:=node_result s i o l oBound cursor ptr
    have b:=ih m (first+1) (by omega) a.next (by intro bad;omega)
    have len : first+(n+1)=(first+1)+n := by omega
    have mono:=destination_mono o
    have e : siblingDestination o (first+1)=siblingDestination o first+siblingWidth first := by
      unfold siblingDestination;rw [sibling_offset_next first live,Nat.add_assoc]
    have stay : RunsOpeningBlock s (runNodes c (first+1) n m) (point c (first+(n+1))-point c first) := by
      have chain:=a.run.next b.run
      have u:=point_mono c first (first+1) (by omega) (by omega)
      have v:=point_mono c (first+1) (first+1+n) (by omega) (by omega)
      have eq : (point c (first+1)-point c first)+(point c (first+1+n)-point c (first+1))=point c (first+(n+1))-point c first := by
        rw [len];omega
      rw [←eq];exact chain
    simp only [runNodes,dif_pos live]
    refine ⟨stay,by rw [len];exact b.next,fun r h1 h2 h3 h4 h5 => (b.kept r h1 h2 h3 h4 h5).trans (a.kept r h1 h2 h3 h4 h5),
      fun q lo => (b.input q lo).trans (a.input q lo),?_,?_⟩
    · intro q fit outer
      rw [len] at outer
      have q1:=mono (show first≤first+1 by omega)
      have q2:=mono (show first+1≤first+1+n by omega)
      have away : q<siblingDestination o first ∨ siblingDestination o (first+1)≤q := outer.imp id (by omega)
      exact (b.frame q fit (outer.imp (by omega) id)).trans (a.frame q fit away)
    · intro lev low high byte inside
      by_cases start : lev=first
      · subst lev
        have f:=all_sibling_copies_fit i o first oBound live
        have ram : MEMORY_BYTES<2^64 := by decide
        exact (b.frame _ (by have:=f.2.2.2;omega) (Or.inl (by omega))).trans (a.bytes byte inside)
      · exact (b.fields lev (by omega) (by omega) byte inside).trans
          (payload_stable i lev byte inside a.input (a.kept _ (by decide) (by decide) (by decide) (by decide) (by decide)))

end TwoPermutationPrototype.GroupedOpening.Whole
