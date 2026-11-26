import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowEffect
open CommitGolf RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut OpeningWordFields OpeningRowEntry
open TwoPermutationPrototype (Memory)
open Encoding
set_option maxRecDepth 12000

def outside (w : Nat) := w<OpeningPut.base ∨ OpeningPut.base+capacity<w

theorem put_frame (m : Memory) (c n w : Nat) (v : Word) (room : c/64<capacity) (away : outside w) :
    put m c n v w=m w := by
  apply keep
  all_goals unfold cell outside at *;omega

theorem low_frame (m : Memory) (c d : Nat) (r : Nat→Word) (room : (c+192)/64<capacity) (w : Nat)
    (away : outside w) : CapWriter.lowMemory m c d r w=m w := by
  unfold CapWriter.lowMemory
  rw [put_frame _ (c+192) _ w _ room away,put_frame _ (c+128) _ w _ (by omega) away,
      put_frame _ (c+64) _ w _ (by omega) away,put_frame _ c _ w _ (by omega) away]

theorem tree_frame (m t : Memory) (trap : CommitStorage.Trapdoor) (ps : Positions) (mem : Heap m trap ps)
    (frame : ∀ w, outside w → t w=m w) : Heap t trap ps := by
  intro d j cell w small
  have le := cell.1
  have lim := Nat.pow_le_pow_right (n:=2) (by decide) (show d+1≤25 by omega)
  have jlim := cell.2.2.trans_le lim
  rw [frame _ (Or.inl (by unfold CommitParents.addr OpeningPut.base;omega))]
  exact mem d j cell w small

def fields (o : Oracle) (key : Generator.Key) (msg : Message) (e : Env) (d : Nat) :=
  lowFields (LeafTree.tree o key msg d (sibling e.index d)) (lows d)

structure Valid (e : Env) (initial m : Model) (t : CommitStorage.Trapdoor) (ps : Positions)
    (fs : List Wire.Field) (offset : Nat) : Prop where
  bits : Wire.bits fs=e.cursor+offset
  data : Serialized m.mem (Wire.pack fs)
  heap : Heap m.mem t ps
  frame : ∀ w, outside w → m.mem w=initial.mem w
  stack : Stack e m.mem

theorem advance (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o key msg trap) (ps : Positions) (ne : 0<ps.card) (e : Env)
    (initial m t : Model) (fs : List Wire.Field) (d : Fin 25) (pos : 0<d.val)
    (offset next : Nat) (len : 192+(lows d-192)=next-offset) (lt : offset≤next) (small : offset+192≤3633)
    (valid : Valid e initial m trap ps fs offset)
    (effect : t.mem=CapWriter.lowMemory m.mem (e.cursor+offset) d (OpeningNodeStream.words m.mem e.index d)) :
    Valid e initial t trap ps (fs++fields o key msg e d) next := by
  have b := e.room
  have room : (e.cursor+offset+192)/64<capacity := by omega
  have step (w : Nat) (away : outside w) : t.mem w=m.mem w := by
    rw [effect];exact low_frame _ _ _ _ room w away
  refine ⟨?_,?_,tree_frame _ _ _ _ valid.heap step,fun w h => (step w h).trans (valid.frame w h),
    keepStack e _ _ valid.stack (fun w hw => step w (Or.inr (by unfold OpeningPut.base capacity;omega)))⟩
  · rw [Wire.bits_append,valid.bits,fields,low_bits,len];omega
  · rw [effect,←valid.bits]
    exact OpeningNodeStream.serialize m.mem trap ps ne valid.heap o key msg stored e.index d pos fs valid.data
      (by rwa [valid.bits])

end CommitGolfCandidate.Reconstruction.OpeningRowEffect
