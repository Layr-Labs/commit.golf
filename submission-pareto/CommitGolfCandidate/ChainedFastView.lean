import CommitGolfCandidate.ChainedFastOps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000

inductive Expr where
  | reg (r : Reg) | cell (i : Slot) | ptr (p : Port) | reply (j : Nat) (i : Fin 4)
  | band (a b : Expr) | bor (a b : Expr) | shl (a : Expr) (i : Nat) | shr (a : Expr) (i : Nat)
  deriving DecidableEq

def ew (x : Output) (i : Fin 4) := x.extractLsb' (64*i.val) 64
def interp (orig : MachineState) (n : Nat) (ys : Nat→Output) : Expr→Word
  | .reg r=>orig.getReg r | .cell i=>orig.getMem (W (address n i))
  | .ptr p=>ptr n p | .reply j i=>ew (ys j) i
  | .band a b=>interp orig n ys a &&& interp orig n ys b
  | .bor a b=>interp orig n ys a ||| interp orig n ys b
  | .shl a i=>interp orig n ys a <<< i | .shr a i=>interp orig n ys a >>> i

structure View where
  r : Reg→Expr
  m : Slot→Expr
  calls : Nat

def initial : View := ⟨Expr.reg,Expr.cell,0⟩
def math (m : View) : Arith→Expr
  | .band a b=>.band (m.r a) (m.r b) | .bor a b=>.bor (m.r a) (m.r b)
  | .shl a i=>.shl (m.r a) i.toNat | .shr a i=>.shr (m.r a) i.toNat
def View.setR (m : View) (r : Reg) (v : Expr) : View := {m with r:=fun q=>if q=r ∧ r≠.x0 then v else m.r q}
def View.setM (m : View) (i : Slot) (v : Expr) : View := {m with m:=fun j=>if j=i then v else m.m j}
def destSlot (last : Bool) (i : Fin 4) : Slot := ⟨(if last then 8 else 12)+i.val,by cases last <;> simp <;> omega⟩
def srcSlot (first : Bool) (i : Fin 8) : Slot := ⟨(if first then 0 else 12)+i.val,by cases first <;>simp <;>omega⟩
def View.hash (m : View) (last : Bool) : View :=
  { m with calls:=m.calls+1, m:=fun j=>
    let base:=if last then 8 else 12
    if hit : base≤j.val ∧ j.val<base+4 then .reply m.calls ⟨j.val-base,by omega⟩ else m.m j }
def update (m : View) : Cmd→View
  | .get r i=>m.setR r (m.m (cslot i)) | .put i r=>m.setM (cslot i) (m.r r)
  | .calc r a=>m.setR r (math m a)
  | .srcChild=>m.setR .x10 (.ptr .child) | .srcChain=>m.setR .x10 (.ptr .chain)
  | .dstChain=>m.setR .x12 (.ptr .chain) | .dstParent=>m.setR .x12 (.ptr .parent)
  | .tag r=>m.setM 16 (m.r r) | .getTop=>m.setR .x1 (m.m 11) | .putTop=>m.setM 11 (m.r .x1)
  | .hash _ l=>m.hash l

abbrev Request := Nat × (Fin 8→Expr)
def requests (m : View) : List Cmd→List Request
  | []=>[] | (.hash f l)::xs=>(m.calls,fun i=>m.m (srcSlot f i)) :: requests (m.hash l) xs
  | a::xs=>requests (update m a) xs

def Trust (oracle : Oracle) (orig : MachineState) (n : Nat) (ys : Nat→Output) (req : Request) :=
  oracle.compression (cat8 (fun i=>interp orig n ys (req.2 i)))=ys req.1

structure Matches (orig : MachineState) (n : Nat) (ys : Nat→Output) (m : View) (s : MachineState) : Prop where
  regs : ∀ r,s.getReg r=interp orig n ys (m.r r)
  mem : ∀ i,s.getMem (W (address n i))=interp orig n ys (m.m i)
  frame : ∀ q : Nat,q%8=0 → q+32≤2^64 → (∀ i:Slot,q≠address n i) → s.getMem (W q)=orig.getMem (W q)

theorem initial_matches (s : MachineState) (n ys) : Matches s n ys initial s :=
  ⟨fun _=>rfl,fun _=>rfl,fun _ _ _ _=>rfl⟩

private theorem Matches.assign {o n ys m s} (x:Matches o n ys m s) (r v) :
    Matches o n ys (m.setR r v) (putR s r (interp o n ys v)) := by
  refine ⟨?_,?_,?_⟩
  · intro q
    simp only [putR,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg,View.setR]
    by_cases same:r=q ∧ r≠.x0
    · rw [if_pos same,if_pos ⟨same.1.symm,same.2⟩]
    · have rev : ¬(q=r ∧ r≠.x0):=fun e=>same ⟨e.1.symm,e.2⟩
      rw [if_neg same,if_neg rev];exact x.regs q
  · intro i;simpa [putR,View.setR,MachineState.getMem_setReg] using x.mem i
  · intro q a b c;simpa [putR,MachineState.getMem_setReg] using x.frame q a b c

private theorem Matches.store {o n ys m s} (x:Matches o n ys m s) (b:Bounds n) (i v) :
    Matches o n ys (m.setM i v) (putM s n i (interp o n ys v)) := by
  refine ⟨?_,?_,?_⟩
  · intro r;simpa only [putM,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setMem,View.setM] using x.regs r
  · intro j
    by_cases eq:j=i
    · subst j;simp [putM,View.setM,MachineState.getMem_setMem_eq]
    · have ne:W (address n j)≠W (address n i) := by
        intro same;have p:=congrArg BitVec.toNat same;rw [word_addr b,word_addr b] at p;exact eq ((address_inj b j i).mp p)
      simpa [putM,View.setM,eq,MachineState.getMem_setMem_ne,ne,Ne.symm ne] using x.mem j
  · intro q a qb outside
    have ne:W q≠W (address n i) := by
      intro same;have p:=congrArg BitVec.toNat same
      rw [word_addr b,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at p;exact outside i p
    simpa [putM,MachineState.getMem_setMem_ne,ne,Ne.symm ne] using x.frame q a qb outside

theorem source_addr (n : Nat) (f : Bool) (i : Fin 8) :
    address n (srcSlot f i)=address n (srcPort f).slot+8*i.val := by
  have := i.isLt
  cases f <;> simp [address,srcSlot,srcPort,Port.slot] <;> (try split_ifs) <;> omega

theorem dest_addr (n : Nat) (l : Bool) (i : Fin 4) :
    address n (destSlot l i)=address n (dstPort l).slot+8*i.val := by
  have := i.isLt
  cases l <;> simp [address,destSlot,dstPort,Port.slot] <;> (try split_ifs) <;> omega

private theorem writeAway {n : Nat} (b:Bounds n) (s : MachineState) (v : Output) (l : Bool) (q : Nat)
    (al:q%8=0) (room:q+32≤2^64) (ne:∀ i:Fin 4,q≠address n (destSlot l i)) :
    (writeBits s (ptr n (dstPort l)) v).getMem (W q)=s.getMem (W q) := by
  let a:=address n (dstPort l).slot
  have aa:a%8=0:=aligned ..;have bound:=address_room b (dstPort l).slot
  have sep:q+8≤a ∨ a+32≤q := by
    by_contra! inside
    have index:(q-a)/8<4:=by omega
    have bad:=ne ⟨(q-a)/8,index⟩
    rw [dest_addr] at bad
    change q≠a+8*((q-a)/8) at bad;omega
  exact written_other _ _ _ _ al (by dsimp [a] at *;omega) room sep

private theorem Matches.written {o n ys m s} (x:Matches o n ys m s) (b:Bounds n) (l : Bool) :
    Matches o n ys (m.hash l) (writeBits s (ptr n (dstPort l)) (ys m.calls)) := by
  refine ⟨fun r=>(writeBits_register ..).trans (x.regs r),?_,?_⟩
  · intro j
    let base:=if l then 8 else 12
    by_cases hit:base≤j.val ∧ j.val<base+4
    · let i:Fin 4:=⟨j.val-base,by omega⟩
      have eq:destSlot l i=j := by apply Fin.ext;change base+(j.val-base)=j.val;omega
      have a:=dest_addr n l i
      rw [eq] at a
      change _ = interp o n ys (if h:base≤j.val ∧ j.val<base+4 then .reply m.calls ⟨j.val-base,by omega⟩ else m.m j)
      rw [a,dif_pos hit]
      exact written_word s (ys m.calls) (address n (dstPort l).slot) i (aligned ..)
    · have out (i : Fin 4) : address n j≠address n (destSlot l i) := by
        intro same;have eq:=congrArg Fin.val ((address_inj b _ _).mp same)
        change j.val=base+i.val at eq;have:=i.isLt;omega
      rw [writeAway b _ _ l _ (aligned ..) (by have:=address_room b j;omega) out]
      simpa [View.hash,base] using (show s.getMem (W (address n j))=interp o n ys (if h:base≤j.val ∧ j.val<base+4 then .reply m.calls ⟨j.val-base,by omega⟩ else m.m j) from by rw [dif_neg hit];exact x.mem j)
  · intro q al room ne
    rw [writeAway b _ _ l q al room (fun i=>ne _)];exact x.frame q al room ne

theorem simulate (oracle : Oracle) {orig n ys} (b : Bounds n) (xs : List Cmd) (m : View) (s : MachineState)
    (ok:Matches orig n ys m s) (queries:∀ req∈requests m xs,Trust oracle orig n ys req) :
    Matches orig n ys (xs.foldl update m) (checkEvaluation oracle (trace n xs s)).1 := by
  induction xs generalizing s m with
  | nil => simpa [trace,check_evaluation_pure] using ok
  | cons a xs ih =>
    rw [trace,check_evaluation_bind,List.foldl_cons]
    apply ih
    · cases a with
      | hash f l =>
        have input : readBuffer s (address n (srcPort f).slot) 64 =
            cat8 (fun i=>interp orig n ys (m.m (srcSlot f i))) := by
          rw [read8 _ _ (aligned ..)]
          apply congrArg cat8;funext i;rw [←source_addr]
          exact ok.mem _
        have eq:=queries (m.calls,fun i=>m.m (srcSlot f i)) (by simp [requests])
        change oracle.compression _=ys m.calls at eq
        simp only [command,check_evaluation_public_bind,check_evaluation_pure]
        change Matches _ _ _ _ (writeBits s _ (oracle.compression _))
        rw [input,eq];exact ok.written b l
      | get r i | getTop =>
        simp only [command,check_evaluation_pure,update,ok.mem];apply ok.assign
      | put i r | putTop | tag r =>
        simp only [command,check_evaluation_pure,update,ok.regs];apply ok.store b
      | srcChild | srcChain | dstParent | dstChain =>
        simp only [command,check_evaluation_pure,update];apply ok.assign
      | «calc» r op =>
        cases op <;> simp only [command,check_evaluation_pure,update,Arith.value,ok.regs] <;> apply ok.assign
    · intro req member;apply queries;cases a <;> simp_all [requests,update]

end CommitGolfCandidate.Chained.Native.Fast
