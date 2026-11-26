import CommitGolfCandidate.S5BatchPath
import CommitGolfCandidate.S5NormalPeer
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node)
open Writer (widths)
def batchSite (second : Bool) := if second then PeerSite.batchSecond else PeerSite.batchFirst
def peerEmit (second : Bool) := if second then EmitSite.bottomSecond else EmitSite.bottomFirst

private theorem known_word {pg x} (good : matchesWord pg x = true) : Site pg x.1 x.2 := by
  unfold matchesWord at good
  split at good
  next h => exact site h (beq_iff_eq.mp good)
  next => contradiction

theorem mov_run (s : MachineState) (n : Nat) (rd rs : Reg) (diff : rd≠.x0) (pc : s.pc=pcAt n)
    (code : Site .opening n (.ADDI rd rs 0)) :
    let t:=execInstrBr s (.ADDI rd rs 0)
    Runs s t 1 1 ∧ t.pc=pcAt (n+1) ∧ t.getReg rd=s.getReg rs ∧ t.mem=s.mem ∧
      ∀ r,r≠rd → t.getReg r=s.getReg r := by
  let t:=execInstrBr s (.ADDI rd rs 0)
  have run : Runs s t 1 1:=fun fuel=>execute_ordinary_step _ _ _ _ _ _ (code s pc) rfl
  refine ⟨run,?_,?_,?_,?_⟩
  · change s.pc+4=_;rw [pc,pc_succ]
  · simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq diff,show signExtend12 0=0#64 by rfl,BitVec.add_zero]
  · cases rd <;> rfl
  · intro r ne;exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)

set_option maxHeartbeats 800000
set_option maxRecDepth 16000
private theorem outer_safe (r : Reg) (hr : r∈outerRegs) :
    Writer.preserved r ∧ r≠.x1 ∧ r≠.x11 ∧ r≠.x7 ∧ r∉([.x7,.x6,.x10,.x15] : List Reg) := by
  cases r <;> simp_all [outerRegs,Writer.preserved]

attribute [local irreducible] evaluated emitted
theorem pack_peer (s : MachineState) (i : Index) (second : Bool) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List S5.Field) (limit : widths fs≤555170) (size : xs.length≤LENGTH) (env : InputRows s xs seen tree salt)
    (cur : FieldCursor tree s fs) (pc : s.pc=pcAt (batchSite second).pc) (group : s.getReg .x4=W (rowAddress 0 (i.val/3)))
    (digit : s.getReg .x7=W ((i.val%3+(if second then 1 else 0))%3)) (three : s.getReg .x25=3) :
    let f : S5.Field:=(256,(bottomSibling tree i (peerNumber second)).toNat)
    let e:=peerEmit second
    ∃ t,Runs s t (6+emitCycles e (widths fs)) (9+emitCycles e (widths fs)) ∧ t.pc=pcAt ((batchSite second).pc+8) ∧
      t.getReg .x7=W ((i.val%3+peerNumber second)%3) ∧ t.getReg .x4=s.getReg .x4 ∧ t.getReg .x14=s.getReg .x14 ∧
      FieldCursor tree t (fs++[f]) ∧ InputRows t xs seen tree salt ∧ OuterKeeps s t := by
  let p:=batchSite second
  let e:=peerEmit second
  let u:=evaluated p.ops s
  let a:=nodeAddress 0 (slotNumber i (peerNumber second))
  let digit0:=(i.val%3+(if second then 1 else 0))%3
  obtain ⟨r₁,ip,m₁,dig,addr,keep⟩:=peer_lookup s p _ digit0 pc group digit (Nat.mod_lt _ (by decide)) three
  have nth : (digit0+1)%3=(i.val%3+peerNumber second)%3 := by cases second <;> dsimp [digit0,peerNumber] <;> omega
  have dstReg : p.target=.x10 := by cases second <;> rfl
  have from_ : u.getReg .x10=W a := by
    rw [dstReg,nth] at addr;apply addr.trans;apply congrArg W
    change 4294975488+levelOffset 0+96*(i.val/3)+32*((i.val%3+peerNumber second)%3)=4294975488+32*(3*(i.val/3)+(i.val%3+peerNumber second)%3)
    rw [show levelOffset 0=0 by rfl];omega
  let z:=execInstrBr u (.ADDI .x15 .x7 0)
  have codes : ∀ b : Bool,matchesWord .opening ((batchSite b).pc+4,.ADDI .x15 .x7 0) ∧
      matchesWord .opening ((peerEmit b).pc+2,.ADDI .x7 .x15 0) := by decide +kernel
  have siteA := known_word (codes second).1
  have siteB := known_word (codes second).2
  obtain ⟨r₂,ip₂,save,m₂,k₂⟩:=mov_run u (p.pc+4) .x15 .x7 (by decide) ip siteA
  have keepZ (r : Reg) (safe : r∉([.x7,.x6,.x10,.x15] : List Reg)) : z.getReg r=s.getReg r := by
    apply (k₂ r (by intro eq;subst r;simp at safe)).trans;apply keep <;> first | (rw [dstReg];intro q;subst r;simp at safe) | (intro q;subst r;simp at safe)
  have mz : z.mem=s.mem:=m₂.trans m₁
  have cz:=cursor_same cur mz (keepZ _ (by decide)) (keepZ _ (by decide)) (keepZ _ (by decide)) (keepZ _ (by decide))
  have room:=node_ok 0 _ (slot_valid i (peerNumber second))
  have ready : z.pc=pcAt e.pc:=ip₂.trans (congrArg pcAt (by cases second <;> rfl))
  have w : e.width=256 := by cases second <;> rfl
  let v:=emitted e (widths fs) z
  have send:=put_field z e fs tree a 32 _ cz ready ((k₂ _ (by decide)).trans from_) room.2.2
    (room.2.1.trans (by decide)) limit (fun _=>w ▸ (node tree 0 (slotNumber i (peerNumber second))).isLt)
    ((read_congr_mem z s a 32 mz).trans (env.sources.node 0 (by decide) _ (slot_valid ..)))
    (by rw [w];decide)
  let t:=execInstrBr v (.ADDI .x7 .x15 0)
  obtain ⟨r₄,ip₄,restored,m₄,k₄⟩:=mov_run v _ .x7 .x15 (by decide) send.pc siteB
  have cursor:=cursor_same send.cursor m₄ (k₄ _ (by decide)) (k₄ _ (by decide)) (k₄ _ (by decide)) (k₄ _ (by decide))
  have retPC : t.pc=pcAt (p.pc+8) := ip₄.trans (congrArg pcAt (by cases second <;> rfl))
  have finalReg (r : Reg) (legal : Writer.preserved r) (r1 : r≠.x1) (r11 : r≠.x11) (r7 : r≠.x7)
      (zsafe : r∉([.x7,.x6,.x10,.x15] : List Reg)) : t.getReg r=s.getReg r :=
    (k₄ r r7).trans ((send.keep r legal r1 r11).trans (keepZ r zsafe))
  have orig:=((r₁.trans r₂).trans send.run).trans r₄
  refine ⟨t,?_,retPC,restored.trans ((send.keep _ (by simp [Writer.preserved]) (by decide) (by decide)).trans (save.trans (nth ▸ dig))),
    finalReg _ (by simp [Writer.preserved]) (by decide) (by decide) (by decide) (by decide),
    finalReg _ (by simp [Writer.preserved]) (by decide) (by decide) (by decide) (by decide),?_,
    inputs_mem (inputs_below (inputs_mem env mz) size send.low) m₄,?_⟩
  · convert orig using 1 <;> dsimp only [e] <;> omega
  · change FieldCursor tree t (fs++[(256,(bottomSibling tree i (peerNumber second)).toNat)])
    simpa only [FieldCursor,t,w,slotNumber,bottomSibling] using cursor
  · intro r hr;obtain ⟨a,b,c,d,g⟩:=outer_safe r hr;exact finalReg r a b c d g
end CommitGolfCandidate.S5Machine.Open
