import CommitGolfCandidate.ReconstructedOpeningRecordFrame
import CommitGolfCandidate.ReconstructedOpeningHeaderStream

namespace CommitGolfCandidate.Reconstruction.OpeningHeaderReady
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningPut OpeningCursor OpeningRowEntry OpeningRowEffect
open OpeningHeaderAddress OpeningHeader OpeningRecordFrame
open TwoPermutationPrototype (Memory)
open TwoPermutationPrototype.RV64
set_option maxRecDepth 24000
set_option maxHeartbeats 2000000

structure Constants (m : Memory) : Prop where
  stack1856 : m 8589934262=W 281474976710655
  stack1848 : m 8589934261=W 70368744177663
  stack1840 : m 8589934260=W 17592186044415
  stack1832 : m 8589934259=W 8589934591
  stack1872 : m 8589934264=W 4294967295
  stack1864 : m 8589934263=W 2147483647
  stack1816 : m 8589934257=W 1073741823
  stack1808 : m 8589934256=W 536870911
  stack1800 : m 8589934255=W 2051

theorem initial_constants (trap : CommitStorage.Trapdoor) (ps : Positions) :
    Constants (memoryView (HonestInputs.first trap ps)) := by
  constructor <;> rfl

theorem constants (m : Memory) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (same : Agrees m (memoryView (HonestInputs.first trap ps))) : Constants m := by
  have initial := initial_constants trap ps
  constructor
  · rw [same _ (by decide : stable 8589934262)];exact initial.stack1856
  · rw [same _ (by decide : stable 8589934261)];exact initial.stack1848
  · rw [same _ (by decide : stable 8589934260)];exact initial.stack1840
  · rw [same _ (by decide : stable 8589934259)];exact initial.stack1832
  · rw [same _ (by decide : stable 8589934264)];exact initial.stack1872
  · rw [same _ (by decide : stable 8589934263)];exact initial.stack1864
  · rw [same _ (by decide : stable 8589934257)];exact initial.stack1816
  · rw [same _ (by decide : stable 8589934256)];exact initial.stack1808
  · rw [same _ (by decide : stable 8589934255)];exact initial.stack1800

theorem unchanged (x : Context) (q : Model) (room : (x.cursor+184)/64<capacity)
    (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) (w : Nat) (away : outside w) :
    (to416 x q).mem w=(s345 x).mem w := by
  rw [memory x q room st,put_frame _ (x.cursor+184) _ _ _ room away,put_frame _ (x.cursor+120) _ _ _ (by omega) away]

theorem stable_words (x : Context) (q : Model) (room : (x.cursor+184)/64<capacity)
    (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) : Agrees (to416 x q).mem x.initial.mem := by
  intro w good
  rw [unchanged x q room st w good.1]
  exact front_memory x w (by have := good.2.2.1;omega)

theorem inputs (e : Env) (m q : Model) (sp : m.reg .x2=W 68719474016) (setup : Constants m.mem)
    (saved : m.mem OpeningQuery.saveCount=e.count)
    (st : OpeningHeaderLow.Staged (s345 ⟨m,e.index,e.cursor⟩) q (e.cursor+120)) :
    let x : Context := ⟨m,e.index,e.cursor⟩
    Ready24 e (to416 x q) ∧ Stack e (to416 x q).mem := by
  let x : Context := ⟨m,e.index,e.cursor⟩
  have bound := e.room
  have room : (x.cursor+184)/64<capacity := by change (e.cursor+184)/64<capacity;omega
  have z : (to396 x q).reg .x0=0 := rfl
  have restored := OpeningHeaderWrite.saved (to396 x q) (x.cursor+184) room z
  have m9 : (to396 x q).mem 8589934261=m.mem 8589934261 := by
    change (s389 x q).mem _=_
    rw [low_memory x q st,put_frame _ _ _ _ _ (by omega) (Or.inr (by decide))]
    exact front_memory x _ (Or.inl (by decide))
  constructor
  · constructor
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x0 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x2 (by decide)).trans sp
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x8 (by decide)).trans rfl
    · exact restored.1.trans (m9.trans setup.stack1848)
    · exact restored.2
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x22 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x25 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x10 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x7 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x28 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x26 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x20 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x27 (by decide)).trans rfl
    · exact (OpeningHeaderWrite.frame (to396 x q) (x.cursor+184) .x15 (by decide)).trans rfl
  · constructor
    · rw [unchanged x q room st 8589934262 (Or.inr (by decide))]
      exact (front_memory x 8589934262 (Or.inl (by decide))).trans setup.stack1856
    · rw [unchanged x q room st 8589934261 (Or.inr (by decide))]
      exact (front_memory x 8589934261 (Or.inl (by decide))).trans setup.stack1848
    · rw [unchanged x q room st 8589934260 (Or.inr (by decide))]
      exact (front_memory x 8589934260 (Or.inl (by decide))).trans setup.stack1840
    · rw [unchanged x q room st 8589934259 (Or.inr (by decide))]
      exact (front_memory x 8589934259 (Or.inl (by decide))).trans setup.stack1832
    · rw [unchanged x q room st 8589934264 (Or.inr (by decide))]
      exact (front_memory x 8589934264 (Or.inl (by decide))).trans setup.stack1872
    · rw [unchanged x q room st 8589934263 (Or.inr (by decide))]
      exact (front_memory x 8589934263 (Or.inl (by decide))).trans setup.stack1864
    · rw [unchanged x q room st 8589934257 (Or.inr (by decide))]
      exact (front_memory x 8589934257 (Or.inl (by decide))).trans setup.stack1816
    · rw [unchanged x q room st 8589934256 (Or.inr (by decide))]
      exact (front_memory x 8589934256 (Or.inl (by decide))).trans setup.stack1808
    · rw [unchanged x q room st 8589934255 (Or.inr (by decide))]
      exact (front_memory x 8589934255 (Or.inl (by decide))).trans setup.stack1800
    · rw [unchanged x q room st 8589934271 (Or.inr (by decide))]
      exact (front_memory x 8589934271 (Or.inr (by decide))).trans saved
    · rw [unchanged x q room st 8589934269 (Or.inr (by decide))]
      rfl
    · rw [unchanged x q room st 8589934268 (Or.inr (by decide))]
      rfl
    · rw [unchanged x q room st 8589934267 (Or.inr (by decide))]
      rfl
    · rw [unchanged x q room st 8589934266 (Or.inr (by decide))]
      rfl
    · rw [unchanged x q room st 8589934265 (Or.inr (by decide))]
      rfl

end CommitGolfCandidate.Reconstruction.OpeningHeaderReady
