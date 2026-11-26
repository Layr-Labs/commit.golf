import CommitGolfCandidate.S5BottomLookup
import CommitGolfCandidate.S5OrdinarySibling
import CommitGolfCandidate.S5NormalBytes
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node bytes)

def normalSite (second : Bool) := if second then PeerSite.normalSecond else PeerSite.normalFirst
def copySite (second : Bool) := if second then CopySite.secondPeer else CopySite.firstPeer
def peerNumber (second : Bool) := if second then 2 else 1
def slotNumber (i : Index) (p : Nat) :=3*(i.val/3)+(i.val%3+p)%3
theorem slot_valid (i : Index) (p : Nat) : slotNumber i p<sourceCount 0 := by
  change 3*(i.val/3)+(i.val%3+p)%3<16777218
  have hi:=i.isLt;change i.val<16777216 at hi;omega

def PeerKeeps (s t : MachineState) := ∀ r : Reg,r∉([.x6,.x7,.x19,.x28] : List Reg) → t.getReg r=s.getReg r
set_option maxRecDepth 18000
set_option maxHeartbeats 600000
attribute [local irreducible] copyWords readBuffer evaluated
theorem copy_peer (s : MachineState) (i : Index) (dst : Nat) (second : Bool) (xs : List Index)
    (tree : Levels) (salt : SaltTape) (size : xs.length≤LENGTH) (pc : s.pc=pcAt (normalSite second).pc)
    (group : s.getReg .x4=W (rowAddress 0 (i.val/3))) (digit : s.getReg .x7=W ((i.val%3+(if second then 1 else 0))%3))
    (three : s.getReg .x25=3) (ptr : s.getReg .x19=W dst) (room : AddrOK dst 32)
    (high : proofBase≤dst) (src : Sources s xs tree salt) (tab : Capacity s) :
    ∃ t,Runs s t 13 16 ∧ t.pc=pcAt ((normalSite second).pc+13) ∧
      t.getReg .x7=W ((i.val%3+peerNumber second)%3) ∧ t.getReg .x19=W (dst+32) ∧
      PeerKeeps s t ∧ Sources t xs tree salt ∧ Capacity t ∧
      Written s t dst (bytes (n:=32) (bottomSibling tree i (peerNumber second))) := by
  let p:=normalSite second
  let digit0:=(i.val%3+(if second then 1 else 0))%3
  let u:=evaluated p.ops s
  let a:=nodeAddress 0 (slotNumber i (peerNumber second))
  have q:=peer_lookup s p _ digit0 pc group digit (Nat.mod_lt _ (by decide)) three
  obtain ⟨r₁,ip,mem,dig,addr,keep⟩:=q
  have nth : (digit0+1)%3=(i.val%3+peerNumber second)%3 := by cases second <;> dsimp [digit0,peerNumber] <;> omega
  have toReg : p.target=.x6 := by cases second <;> rfl
  have srcPtr : u.getReg .x6=W a := by
    rw [toReg,nth] at addr;apply addr.trans;apply congrArg W
    change 4294975488+levelOffset 0+96*(i.val/3)+32*((i.val%3+peerNumber second)%3)=4294975488+32*(3*(i.val/3)+(i.val%3+peerNumber second)%3)
    rw [show levelOffset 0=0 by rfl];omega
  have dstPtr : u.getReg .x19=W dst := (keep _ (by decide) (by decide) (toReg ▸ (by decide : Reg.x19≠.x6))).trans ptr
  have entry : u.pc=pcAt (copySite second).pc := ip.trans (congrArg pcAt (by cases second <;> rfl))
  have cnt : (copySite second).words=4 := by cases second <;> rfl
  have good:=node_ok 0 _ (slot_valid i (peerNumber second))
  have ok : AddrOK a 32 := ⟨good.2.2,good.2.1.trans (by decide)⟩
  let v:=copyWords u 4
  have r₂:=copy_run (copySite second) u entry a dst srcPtr dstPtr 4 (by rw [cnt]) ok room
  have copy:=copied u a dst srcPtr dstPtr 4 le_rfl ok room (good.2.1.trans ((by decide : tdEnd≤proofBase).trans high))
  have raw : readBuffer u a 32=bottomSibling tree i (peerNumber second) :=
    (read_congr_mem u s a 32 mem).trans (src.node 0 (by decide) _ (slot_valid ..))
  have w:=copied_bytes copy ok.1 room.1 _ raw
  let t:=execInstrBr v (.ADDI .x19 .x19 32)
  have pcv : v.pc=pcAt (p.pc+12) := by rw [show v.pc=_ from copy_pc u 4,ip];cases second <;> rfl
  have inc : decodeInstruction (openWord (p.pc+12))=some (.base (.ADDI .x19 .x19 32)) := (by decide +kernel : ∀ b : Bool,decodeInstruction (openWord ((normalSite b).pc+12))=some (.base (.ADDI .x19 .x19 32))) second
  have r₃ : Runs v t 1 1 := one _ (by cases second <;> decide) _ inc v t pcv rfl
  have stable (r : Reg) (x : Reg.x19≠r) (y : Reg.x28≠r) : t.getReg r=u.getReg r :=
    (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ x)).trans (copy_keeps u 4 r y)
  have atEnd : t.pc=pcAt (p.pc+13) := by change v.pc+4=_;rw [pcv,pc_succ]
  have out : t.getReg .x19=W (dst+32) := by
    change v.getReg .x19+32=_;rw [copy_keeps u 4 _ (by decide),dstPtr];exact (BitVec.ofNat_add ..).symm
  have bytesOut:=w.congr_mem mem.symm (show t.mem=v.mem from rfl)
  have frame:=bytesOut.outside
  rw [show (bytes (n:=32) (bottomSibling tree i (peerNumber second))).length=32 by simp [bytes]] at frame
  refine ⟨t,(r₁.trans r₂).trans r₃,atEnd,(stable _ (by decide) (by decide)).trans (nth ▸ dig),out,?_,
    src.after size dst 32 frame high room.1 (by decide),?_,bytesOut⟩
  · intro r ne
    apply (stable r (by intro e;subst r;simp at ne) (by intro e;subst r;simp at ne)).trans
    apply keep <;> first | (rw [toReg];intro e;subst r;simp at ne) | (intro e;subst r;simp at ne)
  · intro j hj;exact (frame _ (by change _<2^36;omega) (by omega) (Or.inl (by unfold proofBase at high;omega))).trans (tab j hj)
end CommitGolfCandidate.S5Machine.Open
