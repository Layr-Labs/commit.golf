import CommitGolfCandidate.LateCheckGap

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W AddrOK)
set_option maxRecDepth 4000
attribute [local irreducible] Normal.Runs readBuffer

instance (a n : Nat) : Decidable (AddrOK a n) := inferInstanceAs (Decidable (a%8=0 ∧ a+n≤MEMORY_BYTES))

def anchors : List Reg := [.x1,.x8,.x19,.x20,.x21,.x24,.x25,.x26,.x27,.x30]
def Keeps (s t : MachineState) := ∀ reg∈anchors, t.getReg reg=s.getReg reg

theorem Keeps.then {s t u : MachineState} (x : Keeps s t) (y : Keeps t u) : Keeps s u :=
  fun r h => (y r h).trans (x r h)

private def canKeep (part : Part) := anchors.all fun r => decide (part.equation r=Open.original r)
theorem blockKeeps {s : MachineState} {p : Part} (x : BlockResult p s) (ok : canKeep p) : Keeps s (p.after s) :=
  fun r hr=>x.keep r (of_decide_eq_true (List.all_eq_true.mp ok r hr))

theorem callKeeps {o op s t src dst} (x : CallResult o op s t src dst) : Keeps s t := by
  intro r hr
  exact x.keep r (by intro e;subst r;exact (by decide : ¬Reg.x10∈anchors) hr)
    (by intro e;subst r;exact (by decide : ¬Reg.x12∈anchors) hr)

theorem copyKeeps (p : Site) (s : MachineState) (n : Nat) : Keeps s (copies p s n) :=
  fun r hr => copies_keep p s n r (by intro e;subst r;exact (by decide : ¬Reg.x6∈anchors) hr)

theorem copiesMode (p : Site) (s : MachineState) (n : Nat) (m : Mode s) : Mode (copies p s n) :=
  ⟨(copies_keep p s n _ (by decide : Reg.x6≠.x5)).trans m.select,(copies_keep p s n _ (by decide : Reg.x6≠.x13)).trans m.kind,
   (copies_keep p s n _ (by decide : Reg.x6≠.x11)).trans m.width⟩

structure First (o : Oracle) (s t : MachineState) (v : CommitGolf.Entry) : Prop where
  pc : t.pc=pcAt 406
  keep : Keeps s t
  mode : Mode t
  high : High s t
  middle : readBuffer t 352 96=middleBlock v (o.compression (firstBlock v))
  runs : Normal.Runs o s t 22 1

theorem first (o : Oracle) (s : MachineState) (v : CommitGolf.Entry) (a : Nat)
    (pc : s.pc=pcAt 384) (value : s.getReg .x8=W a) (range : AddrOK a 256) (highA : 448≤a)
    (vread : readBuffer s a 256=v) : ∃ t, First o s t v := by
  let r:=Part.leafReady.after s
  have prefixRun:=basic .leafReady s pc rfl
  have keep:=blockKeeps prefixRun (by decide)
  have mode : Mode r:=⟨prefixRun.regs .x5,prefixRun.regs .x13,prefixRun.regs .x11⟩
  have r8 : r.getReg .x8=W a := (keep .x8 (by decide)).trans value
  have firstRead : readBuffer r a 96=firstBlock v := by
    exact (read_congr_mem r s a 96 prefixRun.mem).trans ((read_buffer_slice s a 256 0 96 (by decide)).symm.trans (congrArg firstBlock vread))
  let u:=result .first r (o.compression (readBuffer r a 96))
  have call:=doCall o .first r a 352 prefixRun.pc mode
    (by change r.getReg .x8+0=W a;rw [r8];exact BitVec.add_zero _) (by rfl)
    ⟨range.1,by have :=range.2;omega⟩ (by decide)
  change CallResult o .first r u a 352 at call
  have ptr : Pointers .middle u (a+96) 384 := by
    constructor
    · change u.getReg .x8+W 96=_;rw [call.keep _ (by decide) (by decide),r8];exact (BitVec.ofNat_add _ _).symm
    · change u.getReg .x12+W 32=_;rw [call.dest];rfl
  have srcok : AddrOK (a+96) 64 := ⟨by have :=range.1;omega,by have :=range.2;omega⟩
  have cp:=copies_run .middle u 8 (a+96) 384 call.pc (by decide) ptr srcok (by decide)
  have copied:=copies_effect .middle u (a+96) 384 8 (by decide) ptr srcok (by decide) (by omega)
  let t:=copies .middle u 8
  have high1 : High s u := (High.memory prefixRun.mem).trans (call.high (by decide))
  have original : readBuffer u (a+96) 64=v.extractLsb' 768 512 := by
    rw [high1 _ _ (by omega) (by have :=range.2;omega),←read_buffer_slice s a 256 96 64 (by decide),vread] <;> rfl
  have tail : readBuffer t 384 64=v.extractLsb' 768 512 := (copied_read copied srcok.1 (by decide)).trans original
  have head : readBuffer t 352 32=o.compression (firstBlock v) := by
    rw [Open.outside_read copied.outside (by decide) (by decide) 352 32 (by decide) (Or.inl (by decide)),call.written,firstRead]
  have joined : readBuffer t 384 64 ++ readBuffer t 352 32=readBuffer t 352 96 :=
    (read_join t 352 32 64).trans BitVec.extractLsb'_eq_self
  refine ⟨t,cp.2,(keep.then (callKeeps call)).then (copyKeeps .middle u 8),copiesMode _ _ _ (call.mode mode),
    high1.trans (high_write copied.outside (by decide) (by decide) (by decide)),?_,?_⟩
  · rw [←joined,tail,head];rfl
  · exact ((Normal.deterministic o prefixRun.runs).trans call.runs).trans (Normal.deterministic o cp.1)

structure Middle (o : Oracle) (s t : MachineState) (v : CommitGolf.Entry) (odd : Bool) : Prop where
  pc : t.pc=pcAt 415
  keep : Keeps s t
  mode : Mode t
  bit : t.getReg .x28=regBit odd
  high : High s t
  a : readBuffer t (da odd) 32=o.compression (middleBlock v (o.compression (firstBlock v)))
  b : readBuffer t (da odd+32) 32=o.compression (lastBlock v)
  runs : Normal.Runs o s t 31 3

private theorem parity (i : Index) : (W i.val &&& 1)=regBit (i.val.testBit 0) := by
  change (BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^1-1)) = _
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod,Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.pow_zero,Nat.div_one]
  have split : i.val%2=0 ∨ i.val%2=1 := by omega
  rcases split with e|e <;> rw [e] <;> rfl

theorem middle (o : Oracle) (s : MachineState) (v : CommitGolf.Entry) (a : Nat) (i : Index)
    (pc : s.pc=pcAt 384) (value : s.getReg .x8=W a) (index : s.getReg .x20=W i.val)
    (range : AddrOK a 256) (highA : 448≤a) (vread : readBuffer s a 256=v) :
    ∃ t, Middle o s t v (i.val.testBit 0) := by
  let odd:=i.val.testBit 0
  obtain ⟨t,f⟩:=first o s v a pc value range highA vread
  let r:=Part.parity.after t
  have setup:=basic .parity t f.pc rfl
  have keep:=blockKeeps setup (by decide)
  have ix : t.getReg .x20=W i.val := (f.keep _ (by decide)).trans index
  have flag : r.getReg .x28=regBit odd := by rw [setup.regs];change (t.getReg .x20 &&& 1)=_;rw [ix,parity]
  have off : r.getReg .x7=W (da odd) := by
    rw [setup.regs];change ((t.getReg .x20 &&& 1) <<< 5)+160=_
    rw [ix,parity];change (regBit odd <<< 5)+160=_;cases odd <;> rfl
  have mode : Mode r := ⟨(setup.keep _ rfl).trans f.mode.select,(setup.keep _ rfl).trans f.mode.kind,
    (setup.keep _ rfl).trans f.mode.width⟩
  have mid : readBuffer r 352 96=middleBlock v (o.compression (firstBlock v)) :=
    (read_congr_mem _ _ _ _ setup.mem).trans f.middle
  let u:=result .middle r (o.compression (readBuffer r 352 96))
  have left:=doCall o .middle r 352 (da odd) setup.pc mode (by rfl)
    (by change r.getReg .x7+0=_;simpa using off) (by decide) (by cases odd <;> decide)
  change CallResult o .middle r u 352 (da odd) at left
  have a8 : u.getReg .x8=W a := (left.keep _ (by decide) (by decide)).trans ((keep _ (by decide)).trans ((f.keep _ (by decide)).trans value))
  have high1:=f.high.trans ((High.memory setup.mem).trans (left.high (by cases odd <;> decide)))
  have last : readBuffer u (a+160) 96=lastBlock v := by
    rw [high1 _ _ (by omega) (by have :=range.2;omega),←read_buffer_slice s a 256 160 96 (by decide),vread];rfl
  let z:=result .last u (o.compression (readBuffer u (a+160) 96))
  have right:=doCall o .last u (a+160) (da odd+32) left.pc (left.mode mode)
    (by change u.getReg .x8+W 160=_;rw [a8];exact (BitVec.ofNat_add _ _).symm)
    (by change u.getReg .x7+W 32=_;rw [left.keep _ (by decide) (by decide),off];exact (BitVec.ofNat_add _ _).symm)
    ⟨by have :=range.1;omega,by have :=range.2;omega⟩ (by cases odd <;> decide)
  change CallResult o .last u z (a+160) (da odd+32) at right
  refine ⟨z,right.pc,((f.keep.then keep).then (callKeeps left)).then (callKeeps right),right.mode (left.mode mode),
    (right.keep _ (by decide) (by decide)).trans ((left.keep _ (by decide) (by decide)).trans flag),
    high1.trans (right.high (by cases odd <;> decide)),?_,?_,?_⟩
  · rw [right.away _ _ (by cases odd <;> decide) (by cases odd <;> decide) (Or.inl le_rfl),left.written,mid]
  · rw [right.written,last]
  · exact ((f.runs.trans (Normal.deterministic o setup.runs)).trans left.runs).trans right.runs

end CommitGolfCandidate.Late.Check.Micro
