import CommitGolfCandidate.S5SiblingLookup
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def bottomOps : List Calc :=
  [.ld .x4 .x3 0,.remu .x7 .x14 .x25,.divu .x14 .x14 .x25,
   .slli .x6 .x14 1,.add .x6 .x6 .x14,.slli .x6 .x6 5,.add .x4 .x4 .x6]
def bottomPC (batch : Bool) := if batch then 156 else 517

theorem div_three (j : Nat) (small : j<2^64) :
    rv64_divu (W j) 3=W (j/3) ∧ rv64_remu (W j) 3=W (j%3) := by
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp [rv64_divu,rv64_remu,W,BitVec.toNat_udiv,BitVec.toNat_umod,Nat.mod_eq_of_lt small] <;> omega

theorem bottom_lookup (s : MachineState) (b : Bool) (i : Index) (pc : s.pc=pcAt (bottomPC b))
    (tab : s.getReg .x3=W 2048) (table : wordAt s 2048=W tdBase) (idx : s.getReg .x14=W i.val)
    (three : s.getReg .x25=3) :
    let t:=evaluated bottomOps s
    Runs s t 7 13 ∧ t.pc=pcAt (bottomPC b+7) ∧ t.mem=s.mem ∧
    t.getReg .x4=W (rowAddress 0 (i.val/3)) ∧ t.getReg .x7=W (i.val%3) ∧ t.getReg .x14=W (i.val/3) ∧
    ∀ r : Reg,r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → t.getReg r=s.getReg r := by
  have code : ∀ b : Bool,∀ j : Fin 7, decodeInstruction (openWord (bottomPC b+j.val))=
      some (.base (bottomOps[j.val]?.getD (.addi .x0 .x0 0)).instr) := by decide +kernel
  have orig : live s s original := by intro r;cases r <;> rfl
  have ea : s.getReg .x3+0#64=W 2048 := by rw [BitVec.add_zero,tab]
  have read : s.getMem (s.getReg .x3+0#64)=W tdBase := ea ▸ table
  have law:=evaluate_block bottomOps (bottomPC b) s s original orig rfl pc
    (by cases b <;> decide) (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : bottomOps.all (fun c=>c.dst != .x0)) c m))
    (by intro x hx;change x∈[Expr.op .add (.reg .x3) (.lit 0)] at hx;obtain rfl:=List.mem_singleton.mp hx
        change accessValid (s.getReg .x3+0#64) 8=true;rw [ea];decide)
    (fun j hj=>by simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using code b ⟨j,hj⟩)
  obtain ⟨run,regs,mem,endPC⟩:=law
  have bound : i.val<2^64 := by have h:=i.isLt;change _<16777216 at h;omega
  obtain ⟨div,rem⟩:=div_three i.val bound
  refine ⟨run,endPC,mem,?_,?_,?_,?_⟩
  · have e:=regs .x4
    change _=s.getMem (s.getReg .x3+0#64)+(((rv64_divu (s.getReg .x14) (s.getReg .x25) <<< 1)+rv64_divu (s.getReg .x14) (s.getReg .x25)) <<< 5) at e
    rw [read,idx,three,div] at e
    unfold W at e
    rw [shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add] at e
    apply e.trans;apply congrArg W;change tdBase+((i.val/3)*2^1+i.val/3)*2^5=4294975488+0+96*(i.val/3)
    unfold tdBase;omega
  · have e:=regs .x7;change _=rv64_remu (s.getReg .x14) (s.getReg .x25) at e
    rw [idx,three,rem] at e;exact e
  · have e:=regs .x14;change _=rv64_divu (s.getReg .x14) (s.getReg .x25) at e
    rw [idx,three,div] at e;exact e
  · intro r h4 h6 h7 h14;apply (regs r).trans;cases r <;> first | contradiction | rfl

inductive PeerSite | batchFirst | batchSecond | normalFirst | normalSecond deriving DecidableEq
instance : Fintype PeerSite := ⟨{.batchFirst,.batchSecond,.normalFirst,.normalSecond},by intro x;cases x <;> decide⟩
def PeerSite.pc : PeerSite → Nat | .batchFirst=>163 | .batchSecond=>171 | .normalFirst=>524 | .normalSecond=>537
def PeerSite.target : PeerSite→Reg | .batchFirst|.batchSecond=>.x10 | _=>.x6
def PeerSite.ops (p : PeerSite) : List Calc := [.addi .x7 .x7 1,.remu .x7 .x7 .x25,.slli .x6 .x7 5,.add p.target .x4 .x6]

theorem peer_lookup (s : MachineState) (p : PeerSite) (group lane : Nat) (pc : s.pc=pcAt p.pc)
    (base : s.getReg .x4=W group) (digit : s.getReg .x7=W lane) (small : lane<3) (three : s.getReg .x25=3) :
    let t:=evaluated p.ops s
    Runs s t 4 7 ∧ t.pc=pcAt (p.pc+4) ∧ t.mem=s.mem ∧ t.getReg .x7=W ((lane+1)%3) ∧
    t.getReg p.target=W (group+32*((lane+1)%3)) ∧ ∀ r : Reg,r ≠ .x7 → r ≠ .x6 → r ≠ p.target → t.getReg r=s.getReg r := by
  have code : ∀ p : PeerSite, ∀ j : Fin 4,decodeInstruction (openWord (p.pc+j.val))=some (.base (p.ops[j.val]?.getD (.addi .x0 .x0 0)).instr) := by decide +kernel
  have init : live s s original := by intro r;cases r <;> rfl
  have law:=evaluate_block p.ops p.pc s s original init rfl pc (by cases p <;> decide)
    (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp ((by decide +kernel : ∀ p : PeerSite,p.ops.all (fun c=>c.dst != .x0)) p) c m))
    (by change ∀ a∈([] : List Expr),_;simp)
    (fun j hj=>by simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using code p ⟨j,hj⟩)
  obtain ⟨run,reg,mem,next⟩:=law
  have w : rv64_remu (s.getReg .x7+signExtend12 1) (s.getReg .x25)=W ((lane+1)%3) := by
    rw [digit,three];change rv64_remu (BitVec.ofNat 64 lane+BitVec.ofNat 64 1) _=_;rw [←BitVec.ofNat_add];exact (div_three (lane+1) (by omega)).2
  refine ⟨?_,next,mem,?_,?_,?_⟩
  · have priceEq : price p.ops=7 := by cases p <;> rfl
    rw [priceEq] at run;exact run
  · apply (reg .x7).trans;cases p <;> exact w
  · apply (reg p.target).trans
    have expression : ((p.ops.foldl bump original) p.target).eval s=s.getReg .x4+(rv64_remu (s.getReg .x7+signExtend12 1) (s.getReg .x25) <<< 5) := by cases p <;> rfl
    rw [expression,w,base];unfold W;rw [shifted,←BitVec.ofNat_add];congr 1 <;> omega
  · intro r h7 h6 hd;apply (reg r).trans;cases p <;> cases r <;> first | contradiction | exact False.elim (hd rfl) | rfl
end CommitGolfCandidate.S5Machine.Open
