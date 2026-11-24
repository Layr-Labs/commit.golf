import CommitGolfCandidate.ChainedFastNode
import CommitGolfCandidate.ChainedFastCode
import CommitGolfCandidate.ChainedParentInit

namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def written : Cmd→Option Reg
  | .calc r _ | .get r _ => some r | .getTop=>some .x1
  | .dstChain | .dstParent=>some .x12 | .srcChain | .srcChild=>some .x10
  | _=>none
def saved : List Reg := [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x11,.x13,.x14,.x15,.x16,.x17,.x18,.x19]

private theorem cmdReg (n : Nat) (a : Cmd) (s t : MachineState) (r : Reg)
    (hit:t∈support (command n s a)) (keep:written a≠some r) : t.getReg r=s.getReg r := by
  cases a with
  | hash f l =>
    simp only [command,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨v,_,rfl⟩:=hit;exact writeBits_register ..
  | get d i | «calc» d i | getTop | dstChain | dstParent | srcChild | srcChain =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t
    simp [written] at keep
    simp only [putR,MachineState.getReg_setPC];apply MachineState.getReg_setReg_ne;exact keep
  | put i val | tag val | putTop =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t;cases r <;> rfl

theorem nodeReg {s t : MachineState} {h : Low} {n : Nat} (hit:t∈support (trace n (plan h) s))
    (r : Reg) (keep:r∈saved) : t.getReg r=s.getReg r := by
  have safe : ∀ j : Low, saved.all (fun x=>(plan j).all fun a=>written a != some x)=true := by decide +kernel
  have all := List.all_eq_true.mp ((List.all_eq_true.mp (safe h)) r keep)
  have aux (xs : List Cmd) (s t : MachineState) (h1:∀ a∈xs,written a≠some r) (ht:t∈support (trace n xs s)) :
      t.getReg r=s.getReg r := by
    induction xs generalizing s with
    | nil => simpa [trace] using congrArg (fun z : MachineState=>z.getReg r) (show t=s by simpa [trace] using ht)
    | cons a xs ih =>
      simp only [trace,mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
      exact (ih mid (fun _ m=>h1 _ (by simp [m])) rest).trans (cmdReg n a s mid r one (h1 _ (by simp)))
  exact aux _ s t (fun a m=>by simpa using all a m) hit

theorem endPC (n : Nat) (k : Lane) (xs : List Cmd) (m : Known) (s t : MachineState)
    (tr:Tracked n k m s) (ok:checked m xs=true) (base : Nat) (pc0:s.pc=pc base)
    (ht:t∈support (trace n xs s)) : t.pc=pc (base+xs.length) := by
  induction xs generalizing s base m with
  | nil =>
    have e:t=s:=by simpa [trace] using ht
    simpa [e] using pc0
  | cons a xs ih =>
    simp only [trace,mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
    simp only [checked,Bool.and_eq_true] at ok
    have pst:=cmd_post tr a ok.1 mid one
    have sub:=ih (nextRegs m a) mid pst.1 ok.2 (base+1)
      (by rw [pst.2,pc0];exact word_pc _) rest
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using sub

def SafeWord (n q : Nat) := q%8=0 ∧ q+32≤2^64 ∧ ∀ i:Slot,i.val≤16 → q≠address n i

private theorem cmdMem (n : Nat) (b : Bounds n) (q : Nat) (safe:SafeWord n q)
    (a : Cmd) (s t : MachineState) (hit:t∈support (command n s a)) :
    t.getMem (W q)=s.getMem (W q) := by
  obtain ⟨al,room,ne⟩:=safe
  have away (i : Slot) (hi:i.val≤16) : W q≠W (address n i) := by
    intro eq;have same:=congrArg BitVec.toNat eq
    rw [word_addr b,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at same
    exact ne i hi same
  cases a with
  | hash f l =>
    simp only [command,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨v,_,rfl⟩:=hit
    have exc (i : Fin 4) : q≠address n (dstPort l).slot+8*i.val := by
      have off : (dstPort l).slot.val+i.val≤16 := by cases l <;> simp [dstPort,Port.slot] <;>omega
      let idx:Slot:=⟨(dstPort l).slot.val+i.val,by omega⟩
      have eq:address n idx=address n (dstPort l).slot+8*i.val := by
        have:=i.isLt;cases l <;>simp [address,idx,dstPort,Port.slot] <;>(try split_ifs) <;>omega
      rw [←eq];exact ne idx off
    have gap:q+8≤address n (dstPort l).slot ∨ address n (dstPort l).slot+32≤q := by
      by_contra! overlap
      have x:=aligned n (dstPort l).slot
      let j:Fin 4:=⟨(q-address n (dstPort l).slot)/8,by omega⟩
      have bad:=exc j
      dsimp [j] at bad;omega
    exact written_other _ _ _ _ al (by have:=address_room b (dstPort l).slot;omega) room gap
  | get d i | «calc» d i | getTop | dstChain | dstParent | srcChild | srcChain =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t;simp [putR,MachineState.getMem_setReg]
  | put i r =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t
    apply MachineState.getMem_setMem_ne;exact away (cslot i) (by have:=i.isLt;dsimp [cslot];omega)
  | putTop =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t
    apply MachineState.getMem_setMem_ne;exact away 11 (by decide)
  | tag _ =>
    simp only [command,support_pure,Set.mem_singleton_iff] at hit;subst t
    apply MachineState.getMem_setMem_ne;exact away 16 (by decide)

theorem traceMem (n : Nat) (b : Bounds n) (q : Nat) (safe:SafeWord n q) (xs : List Cmd)
    (s t : MachineState) (ht:t∈support (trace n xs s)) : t.getMem (W q)=s.getMem (W q) := by
  induction xs generalizing s with
  | nil =>
    have same:t=s:=by simpa [trace] using ht
    rw [same]
  | cons a xs ih =>
    simp only [trace,mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
    exact (ih mid rest).trans (cmdMem n b q safe a s mid one)

theorem nodeFetch (h : Low) (k : Lane) : FetchList k (nodeStart h k) (plan h) := by
  have bound : ∀ (j : Low) (u : Lane), nodeStart j u+(node j u).length≤233483 := by decide +kernel
  intro i s here
  have atWord:=congrArg (fun xs : List Instr=>xs[i.val]?) (plan_op h k)
  have inside:i.val<(node h k).length := by rw [←plan_op,List.length_map];exact i.isLt
  have word : (plan h)[i.val].op k=(node h k)[i.val] := by
    simpa only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,Option.map_some,
      List.getElem?_eq_getElem inside,Option.some.injEq] using atWord
  change _ = some _
  rw [show (plan h)[i] = (plan h)[i.val] from rfl, word]
  exact fetchAt (nodes h k) (bound h k) ⟨i.val,inside⟩ _ here

end CommitGolfCandidate.Chained.Native.Fast
