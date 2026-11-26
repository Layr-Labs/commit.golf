import CommitGolfCandidate.ReconstructedLeafComplete
import CommitGolfCandidate.ReconstructedCommitParentsMemory
import CommitGolfCandidate.ReconstructedCommitParentsHeap

namespace CommitGolfCandidate.Reconstruction.LeafTree
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open TwoPermutationPrototype (Words window)
open LeafModel LeafContent CommitWindows Generator

set_option maxRecDepth 8192

def digest (b : BitVec 1600) : Binding.Digest :=
  ((replyWords b 2 ++ replyWords b 1) ++ replyWords b 0,replyWords b 3 &&& 0xffffffffffff)

def leafNumber (j : Nat) : Index := ⟨(j-2^24)%2^24,by change _<2^24;omega⟩

def values (o : Oracle) (k : Key) (msg : Message) (j : Nat) := digest (lastReply o k msg (leafNumber j))

def tree (o : Oracle) (k : Key) (msg : Message) := CommitParents.node (CommitParents.rawC o) (values o k msg)

theorem canonical (o : Oracle) (k : Key) (msg : Message) (j : Nat) : Binding.Canonical 24 (values o k msg j) := by
  change ((replyWords _ 3) &&& 0xffffffffffff#64).toNat < Binding.radix 24
  rw [show Binding.radix 24=2^48 by decide,BitVec.toNat_and]
  have cut (n : Nat) : n &&& 281474976710655 < 2^48 := by
    change n &&& (2^48-1)<2^48
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)
  exact cut _

private theorem read_word (s : MachineState) (m : Model) (fits : Fits s m) (w offset : Nat)
    (ok : w+offset < 2^33) :
    CommitParents.atWord s (8*w+8*offset) = m.mem (w+offset) := by
  rw [show 8*w+8*offset=8*(w+offset) by omega]
  exact fits.memory _ ok

theorem read_cell (s : MachineState) (m : Model) (fits : Fits s m) (w : Nat) (ok : w+4≤2^33) :
    CommitParents.cell s (8*w) = ((m.mem (w+2) ++ m.mem (w+1)) ++ m.mem w,m.mem (w+3)) := by
  rw [CommitParents.cell_words s _ (by omega)]
  have h (j : Nat) (room : j<4) := read_word s m fits w j (by omega)
  have a : CommitParents.atWord s (8*w+16)=m.mem (w+2) := h 2 (by decide)
  have b : CommitParents.atWord s (8*w+8)=m.mem (w+1) := h 1 (by decide)
  have c : CommitParents.atWord s (8*w)=m.mem w := by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by decide)
  have d : CommitParents.atWord s (8*w+24)=m.mem (w+3) := h 3 (by decide)
  rw [a,b,c,d]

private theorem stamped (b : BitVec 1600) :
    (((markedReply b 2 ++ markedReply b 1) ++ markedReply b 0),markedReply b 3) =
      CommitParents.written 24 (digest b) := by
  have tag : Binding.childMask 24 false=0xffff000000000000 := by decide
  have masked (w : Word) : w ||| 0xffff000000000000 = w &&& 0xffffffffffff ||| 0xffff000000000000 := by
    apply BitVec.eq_of_getLsbD_eq
    intro bit small
    have masks : ∀ j : Fin 64, (0xffffffffffff : Word).getLsbD j.val =
        !(0xffff000000000000 : Word).getLsbD j.val := by decide
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,masks ⟨bit,small⟩]
    cases w.getLsbD bit <;> cases (0xffff000000000000 : Word).getLsbD bit <;> rfl
  change ((_,_):Binding.Digest) = Binding.marked 24 false (digest b)
  exact Prod.ext rfl (by change _ = ((replyWords b 3 &&& _) ||| Binding.childMask 24 false);rw [tag];exact masked _)

private theorem fresh_cell (o : Oracle) (k : Key) (msg : Message) (s : MachineState) (m : Model)
    (fits : Fits s m) (pre : Prefix o k msg LENGTH m.mem) (e j : Nat) (dep : e<24) (size : j≤2^(e+1)) :
    CommitParents.cell s (CommitParents.addr e j)=Binding.zeroDigest := by
  let w := 536871428+4*(j+e)
  have address : CommitParents.addr e j=8*w := by unfold CommitParents.addr; dsimp [w];omega
  have cap := Nat.pow_le_pow_right (n:=2) (by decide) (show e+1≤24 by omega)
  have bound : w+4≤heapBase := by dsimp [w]; unfold heapBase;omega
  have bot : 4294971424 ≤ 8*w := by dsimp [w];omega
  have z (x : Nat) (small : x<4) : m.mem (w+x)=0 := pre.parents _ (by omega) (by omega)
  rw [address,read_cell s m fits w (by unfold heapBase at bound;omega),z 2 (by decide),z 1 (by decide),z 3 (by decide)]
  rw [show m.mem w=0 by simpa only [Nat.add_zero] using z 0 (by decide)];rfl

attribute [local irreducible] lastReply markedReply

theorem snapshot (o : Oracle) (k : Key) (msg : Message) (s : MachineState) (m : Model)
    (fits : Fits s m) (pre : Prefix o k msg LENGTH m.mem) :
    CommitParents.Snapshot (CommitParents.cell s) (tree o k msg) 23 (2^23) := by
  apply CommitParents.entry_snapshot
  · intro j lo hi
    let i := leafNumber j
    have idx : i.val=j-2^24 := Nat.mod_eq_of_lt (by omega)
    have geom : CommitParents.addr 24 j=8*location i := by unfold CommitParents.addr location heapBase;omega
    have h := pre.past i i.isLt
    have get (v : Fin 4) : m.mem (location i+v.val)=markedReply (lastReply o k msg i) v := congrFun h v
    have bounds := LeafLane.limits i
    rw [geom,read_cell s m fits _ (by unfold generatorBase at bounds;omega)]
    change _=CommitParents.written 24 (digest (lastReply o k msg i))
    have d := get (⟨0,by decide⟩ : Fin 4)
    change m.mem (location i+0) = markedReply (lastReply o k msg i) 0 at d
    rw [Nat.add_zero] at d
    have d1 : m.mem (location i+1)=markedReply (lastReply o k msg i) 1 := get 1
    have d2 : m.mem (location i+2)=markedReply (lastReply o k msg i) 2 := get 2
    have d3 : m.mem (location i+3)=markedReply (lastReply o k msg i) 3 := get 3
    rw [d,d1,d2,d3]
    exact stamped _
  · intro e j dep _ top
    exact fresh_cell o k msg s m fits pre e j dep top.le
  · intro e dep
    exact fresh_cell o k msg s m fits pre e _ dep (by rfl)

end CommitGolfCandidate.Reconstruction.LeafTree
