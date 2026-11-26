import CommitGolfCandidate.S5FirstRound
import CommitGolfCandidate.S5SiblingLookup
import CommitGolfCandidate.S5OpenWrites
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (bytes Levels node)

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
attribute [local irreducible] copyWords readBuffer evaluated

def Capacity (s : MachineState) := ∀ d<25, wordAt s (2048+8*d)=W (layerBase d)
def ordinarySibling (s : MachineState) (d : Fin 23) :=
  execInstrBr (copyWords ((Lookup.ordinary d).after s) 4) (.ADDI .x19 .x19 32)

structure SiblingCopied (s t : MachineState) (d : Fin 23) (p : Index) (dst : Nat) (tree : Levels) : Prop where
  run : Runs s t 19 19
  pc : t.pc=pcAt (550+19*(d.val+1))
  ptr : t.getReg .x19=W (dst+32)
  idx : t.getReg .x14=W (indexAbove p (d.val+2))
  regs : ∀ r, r∉([.x4,.x6,.x7,.x14,.x19,.x28] : List Reg)→t.getReg r=s.getReg r
  written : Written s t dst (bytes (n:=32) (node tree (d.val+1) (mate p (d.val+1))))
  table : Capacity t

theorem ordinary_sibling (s : MachineState) (d : Fin 23) (p : Index) (dst : Nat) (tree : Levels)
    (pc : s.pc=pcAt (550+19*d.val)) (gp : s.getReg .x3=W 2048) (tab : Capacity s)
    (idx : s.getReg .x14=W (indexAbove p (d.val+1))) (ptr : s.getReg .x19=W dst)
    (high : proofBase≤dst) (valid : AddrOK dst 32)
    (src : readBuffer s (nodeAddress (d.val+1) (mate p (d.val+1))) 32=node tree (d.val+1) (mate p (d.val+1))) :
    SiblingCopied s (ordinarySibling s d) d p dst tree := by
  let k:=Lookup.ordinary d
  let u:=k.after s
  let v:=copyWords u 4
  let a:=nodeAddress (d.val+1) (mate p (d.val+1))
  have jb : indexAbove p (d.val+1)<2^64 := by unfold indexAbove S4.nodeIndex;have h:=p.isLt;change p.val<16777216 at h;have :=Nat.div_le_self p.val (S4.span (d.val+1));omega
  obtain ⟨first,ip,mem,up,sp,keep⟩:=sibling_lookup s k _ jb pc gp idx (tab (d.val+1) (by have := d.isLt;omega))
  have up' : u.getReg .x14=W (indexAbove p (d.val+2)) := by rw [above_next _ _ (by omega)];exact up
  have dest : u.getReg .x19=W dst := (keep _ (by decide) (by decide) (by decide) (by decide) (by change Reg.x19≠.x6;decide)).trans ptr
  have good:=node_ok _ _ (mate_bound p (d.val+1) (by omega) (by have :=d.isLt;omega))
  have sb : AddrOK a 32 := ⟨good.2.2,by have h:=good.2.1;unfold tdEnd at h;change _≤2^36;exact h.trans (by decide)⟩
  have sep : a+32≤dst := good.2.1.trans ((by decide : tdEnd≤proofBase).trans high)
  have cp : v.pc=pcAt (568+19*d.val) := by
    rw [show v.pc=_ from copy_pc u 4,ip]
    change pcAt (550+19*d.val+10)+BitVec.ofNat 64 (4*8)=_
    rw [pc_delta];apply congrArg pcAt;omega
  have cpc : u.pc=pcAt (CopySite.sibling d).pc := by rw [ip];apply congrArg pcAt;change 550+19*d.val+10=560+19*d.val;omega
  have run:=copy_run (.sibling d) u cpc a dst sp dest 4 le_rfl sb valid
  have data:=copied_bytes (copied u a dst sp dest 4 le_rfl sb valid sep) sb.1 valid.1 (node tree (d.val+1) (mate p (d.val+1)))
    ((read_congr_mem u s a 32 mem).trans src)
  have code : ∀ l : Fin 23, decodeInstruction (openWord (568+19*l.val))=some (.base (.ADDI .x19 .x19 32)) := by decide +kernel
  have last : Runs v (ordinarySibling s d) 1 1 := one _ (by have := d.isLt;omega) _ (code d) _ _ cp rfl
  have full := data.congr_mem mem.symm (show (ordinarySibling s d).mem=v.mem from rfl)
  constructor
  · exact (first.trans run).trans last
  · change v.pc+4=_;rw [cp,pc_succ];apply congrArg pcAt;omega
  · change v.getReg .x19+32=_
    rw [copy_keeps u 4 _ (by decide),dest];exact (BitVec.ofNat_add dst 32).symm
  · exact (copy_keeps u 4 _ (by decide)).trans up'
  · intro r nr
    have nr19 : .x19≠r := by intro q;subst r;simp at nr
    have nz : .x28≠r := by intro q;subst r;simp at nr
    apply (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ nr19)).trans
    apply (copy_keeps u 4 r nz).trans
    apply keep <;> intro q <;> subst r <;> simp [k,Lookup.dst] at nr
  · exact full
  · intro j hj
    have len : (bytes (n:=32) (node tree (d.val+1) (mate p (d.val+1)))).length=32 := by simp [bytes]
    exact (full.outside (2048+8*j) (by change _<2^36;omega) (by omega)
      (Or.inl (by unfold proofBase at high;omega))).trans (tab j hj)
end CommitGolfCandidate.S5Machine.Open
