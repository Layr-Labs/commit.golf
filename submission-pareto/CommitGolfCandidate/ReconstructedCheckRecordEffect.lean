import CommitGolfCandidate.ReconstructedCheckRecordSlots

namespace CommitGolfCandidate.Reconstruction.CheckRecordEffect
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecordAccess CheckRecordSlots CheckRecordWrite
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 13000
set_option maxHeartbeats 1250000
abbrev W:=BitVec.ofNat 64

private theorem flagWord (k : Nat) : alignToDword (CheckRecordAccess.flag k)=wordAddress ((4259840+k)/8):=OpeningCursor.aligned _

private theorem apart (w k : Nat) (small : w<2^33) (room : k<1024) (diff : w ≠ (4259840+k)/8) :
    wordAddress w≠alignToDword (CheckRecordAccess.flag k) := by
  rw [flagWord];intro e;have h:=congrArg BitVec.toNat e
  change (8*w)%2^64=(8*((4259840+k)/8))%2^64 at h;omega

private theorem plain (s : MachineState) (k w : Nat) (small : k<1024) (bound : w<2^33)
    (diff : w ≠ (4259840+k)/8) : (s.setByte (CheckRecordAccess.flag k) 1).getMem (wordAddress w)=s.getMem (wordAddress w) :=
  MachineState.getMem_setMem_ne (apart w k bound small diff)

theorem fixed {s t : MachineState} {k ord count : Nat} (r : CheckRecordWrite.After s t k ord count) (room : k<1024) :
    CheckRecordImmutable.Fixed s t := by
  intro a bound aligned away
  obtain ⟨w,hw⟩ : ∃ w,a=8*w:=⟨a/8,by omega⟩;subst a
  change t.getMem (wordAddress w)=_
  rw [r.words w (by omega),CheckRecordWrite.memory,windowFrame]
  · exact plain s k w room (by omega) (by unfold CheckRecordImmutable.Outside at away;omega)
  · unfold capWord CheckRecordImmutable.Outside at *;omega

theorem flagChange {s t : MachineState} {k ord count : Nat} (r : CheckRecordWrite.After s t k ord count) (room : k<1024)
    (j : Nat) (small : j<1024) : t.getByte (CheckRecordAccess.flag j)=(if j=k then 1 else s.getByte (CheckRecordAccess.flag j)) := by
  let mark:=s.setByte (CheckRecordAccess.flag k) 1
  have m : t.getByte (CheckRecordAccess.flag j)=mark.getByte (CheckRecordAccess.flag j):=by
    change extractByte (t.getMem (alignToDword _)) _=extractByte (mark.getMem (alignToDword _)) _
    rw [flagWord];apply congrArg (fun v=>extractByte v _)
    rw [r.words _ (by omega),CheckRecordWrite.memory,windowFrame]
    · rfl
    · unfold capWord;omega
  rw [m,show mark=s.setByte (CheckRecordAccess.flag k) 1 by rfl,set_byte_read]
  have iff : CheckRecordAccess.flag j=CheckRecordAccess.flag k ↔ j=k:=by
    refine ⟨fun e=>?_,congrArg CheckRecordAccess.flag⟩
    have z:=congrArg BitVec.toNat e;change (4259840+j)%2^64=(4259840+k)%2^64 at z;omega
  simp only [iff]

theorem holds {s t : MachineState} {a : Slots} {k ord count : Nat} (h : Holds s a)
    (r : CheckRecordWrite.After s t k ord count) (room : k<1024) (node : Binding.Digest)
    (input : CheckPairPhysical.child s CheckPair.current node) : Holds t (replace a k node) := by
  constructor
  · intro j small;rw [flagChange r room j small,h.flag j small];by_cases hit : j=k <;> simp [replace,hit,present]
  · intro j small v stored l
    have fits : capWord j l<2^33:=by have:=l.isLt;unfold capWord;omega
    rw [r.words _ fits,CheckRecordWrite.memory]
    by_cases hit : j=k
    · subst j;rw [windowRead];have eq : node=v:=by simpa [replace] using stored
      exact eq ▸ input l
    · have eq : a j=some v:=by simpa [replace,hit] using stored
      have far : capWord j l<capWord k 0 ∨ capWord k 0+4≤capWord j l:=by have:=l.isLt;unfold capWord;omega
      rw [windowFrame _ _ _ _ far]
      have neq : capWord j l≠(4259840+k)/8:=by have:=l.isLt;unfold capWord;omega
      exact (plain s k _ room fits neq).trans (h.words j small v eq l)

end CommitGolfCandidate.Reconstruction.CheckRecordEffect
