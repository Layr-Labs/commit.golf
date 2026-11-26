import CommitGolfCandidate.ReconstructedCheckCapHonestStep
import CommitGolfCandidate.ReconstructedCheckHonestOrdinals

namespace CommitGolfCandidate.Reconstruction.CheckCapHonest
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckCapLevel CheckCapHonestStep CheckCapIterate
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
open CapSchedule (rest)
set_option maxRecDepth 15500
set_option maxHeartbeats 1200000

theorem traverse (o : Oracle) (key : Generator.Key) (msg : Message) (f : Nat→Bool)
    (stream d c : Nat) (s : MachineState) (out : Option Nat) (t : MachineState) (log : List PublicRow)
    (tr : Trail o f stream d c s out t log) (fs : List Wire.Field) (lim : d≤9) (cur : c=Wire.bits fs)
    (layout : stream=Wire.pack (fs++rest (LeafTree.tree o key msg) f d))
    (known : Known (LeafTree.tree o key msg) f d s) :
    out=some (Wire.bits (fs++rest (LeafTree.tree o key msg) f d)) ∧ Known (LeafTree.tree o key msg) f 0 t := by
  induction tr generalizing fs with
  | finish c s ready=>
    exact ⟨by change some c=some (Wire.bits (fs++[]));simpa using cur,known⟩
  | stopped k c s t log m base bad halt=>
    subst c
    have h:=(decode _ (CheckHonestWalk.canonical o key msg) f (k+1) stream (by omega) lim m fs layout).1
    rw [bad] at h;contradiction
  | level k c s u t log tail m out base good more ih=>
    subst c
    let tree:=LeafTree.tree o key msg
    let next:=fs++CapLevel.fields tree f (k+1)
    have serial : fs++rest tree f (k+1)=next++rest tree f k := by
      rw [CapSchedule.split tree f (k+1) lim (by omega)];simp only [next,CapLevel.fields,List.append_assoc,Nat.add_sub_cancel]
    have nextTime:=(decode tree (CheckHonestWalk.canonical o key msg) f (k+1) stream (by omega) lim m fs layout).2.1
    have fresh:=step o key msg f k stream (by omega) s u log m fs layout base known good
    have result:=ih next (by omega) nextTime (layout.trans (congrArg Wire.pack serial)) fresh
    exact ⟨result.1.trans (congrArg (fun ys=>some (Wire.bits ys)) serial.symm),result.2⟩

theorem rootLive (f : Nat→Bool) (idx : Index) (d : Nat) (lim : d≤9)
    (live : Live f d (CheckWalkValues.heap idx d)=true) : Live f 0 1=true := by
  induction d with
  | zero=>simpa only [CheckCapPaths.heap_zero] using live
  | succ d ih=>exact ih (by omega) (CheckCapPaths.active f idx d (by omega) live)

theorem flagsAt (ps : Positions) (idx : Index) (inside : idx∈ps) :
    Live (CapEntry.flags ps) 9 (CheckWalkValues.heap idx 9)=true := by
  let offset:=idx.val/32768
  have off : offset<512:=(Frontier.heap_endpoint idx).2
  have fold (xs : List Index) (bs : List Bool) (len : bs.length=512)
      (hit : idx∈xs ∨ bs[offset]?.getD false=true) :
      (xs.foldl Frontier.mark bs)[offset]?.getD false=true := by
    induction xs generalizing bs with
    | nil=>exact hit.resolve_left List.not_mem_nil
    | cons a xs ih=>
      apply ih (Frontier.mark bs a) (by simp [Frontier.mark,len])
      rcases hit with h|h
      · rcases List.mem_cons.mp h with first|later
        · subst a;right;unfold Frontier.mark
          rw [List.getElem?_set_self (len ▸ off)];rfl
        · exact Or.inl later
      · right;unfold Frontier.mark
        by_cases eq : offset=a.val/32768
        · rw [←eq,List.getElem?_set_self (len ▸ off)];rfl
        · simpa [eq,Ne.symm eq] using h
  have yes:=fold (ps.sort (·≤·)) (List.replicate 512 false) (by simp) (Or.inl (by simpa using inside))
  have slot : CheckWalkValues.heap idx 9=512+offset:=by
    change (16777216+idx.val)/32768=512+idx.val/32768;omega
  rw [slot]
  change (Frontier.flags (ps.sort (·≤·)))[512+offset-512]?.getD false=true
  rw [Nat.add_sub_cancel_left]
  exact yes

/-- On an honestly serialized opening, every successful lower record feeds its exact tree slot
to the shared checker. The upper traversal reaches the root at the last encoded bit. -/
theorem nine (o : Oracle) (key : Generator.Key) (msg : Message) (ps : Positions) (nonempty : ps.Nonempty)
    (s t : MachineState) (out : Option Nat) (log : List PublicRow) (c stream : Nat)
    (tr : Trail o (CapEntry.flags ps) stream 9 c s out t log)
    (salts : OpenedSalts ps) (honest : stream=Wire.pack (Encoding.fields (LeafTree.tree o key msg) ps salts))
    (cursor : c=3633*ps.card) (known : Known (LeafTree.tree o key msg) (CapEntry.flags ps) 9 s) :
    out=some (Wire.bits (Encoding.fields (LeafTree.tree o key msg) ps salts)) ∧
    node t 1=LeafTree.tree o key msg 0 1 := by
  let tree:=LeafTree.tree o key msg
  let f:=CapEntry.flags ps
  let fs:=CapIterate.records tree ps salts
  have recordBits : Wire.bits fs=3633*ps.card:=by
    unfold fs CapIterate.records
    rw [Wire.flat_bits _ _ 3633 (fun i=>Encoding.record_bits ..),Finset.length_sort]
  have layout:=CapIterate.concat tree ps salts
  have good:=traverse o key msg f stream 9 c s out t log tr fs (by decide)
    (cursor.trans recordBits.symm) (honest.trans (congrArg Wire.pack layout.symm)) known
  obtain ⟨idx,member⟩:=nonempty
  have top:=rootLive f idx 9 (by decide) (flagsAt ps idx member)
  exact ⟨good.1.trans (congrArg (fun xs=>some (Wire.bits xs)) layout),good.2 1 (by decide) (by decide) top⟩

end CommitGolfCandidate.Reconstruction.CheckCapHonest

