import CommitGolfCandidate.S5CheckLeafData
import CommitGolfCandidate.S5CheckCalc
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Late (Digest)
inductive LeafCall | first | second | third | final deriving DecidableEq
instance : Fintype LeafCall:=⟨{.first,.second,.third,.final},by intro x;cases x <;> decide⟩
def LeafCall.pc : LeafCall→Nat | .first=>160 | .second=>163 | .third=>166 | .final=>169
def LeafCall.args : LeafCall→List Sym.Calc
  | .first=>[.addi .x10 .x24 0,.addi .x12 .x24 64]
  | .second=>[.addi .x10 .x24 64,.addi .x12 .x29 0]
  | .third=>[.addi .x10 .x24 160,.addi .x12 .x29 32]
  | .final=>[.addi .x10 .x25 0,.addi .x12 .x27 0]
def LeafCall.src : LeafCall→Nat | .first=>leafBuf | .second=>leafBuf+64 | .third=>leafBuf+160 | .final=>rowBuf
def LeafCall.dst (odd : Bool) : LeafCall→Nat
  | .first=>leafBuf+64 | .second=>rowBuf+laneOffset odd | .third=>rowBuf+laneOffset odd+32 | .final=>digestBuf
structure LeafSys (s : MachineState) (odd : Bool) : Prop where
  leaf : s.getReg .x24=W leafBuf
  row : s.getReg .x25=W rowBuf
  digest : s.getReg .x27=W digestBuf
  slot : s.getReg .x29=W (rowBuf+laneOffset odd)
  sys : s.getReg .x5=0
  kind : s.getReg .x13=0
  len : s.getReg .x11=96

def LeafCallKeep (s t : MachineState) := ∀ q,q ≠ .x10 → q ≠ .x12 → t.getReg q=s.getReg q
theorem LeafCallKeep.trans {s t u} (a : LeafCallKeep s t) (b : LeafCallKeep t u) : LeafCallKeep s u :=
  fun q x y=>(b q x y).trans (a q x y)
theorem LeafSys.after {s t odd} (f : LeafSys s odd) (keep : LeafCallKeep s t) : LeafSys t odd :=
  ⟨(keep _ (by decide) (by decide)).trans f.leaf,(keep _ (by decide) (by decide)).trans f.row,
   (keep _ (by decide) (by decide)).trans f.digest,(keep _ (by decide) (by decide)).trans f.slot,
   (keep _ (by decide) (by decide)).trans f.sys,(keep _ (by decide) (by decide)).trans f.kind,(keep _ (by decide) (by decide)).trans f.len⟩
private theorem args_src (s : MachineState) (odd : Bool) (call : LeafCall) (f : LeafSys s odd) :
    ((call.args.foldl Sym.bump Sym.original) .x10).eval s=W call.src := by
  cases call
  · change s.getReg .x24+0#64=_;rw [f.leaf];rfl
  · change s.getReg .x24+64#64=_;rw [f.leaf];rfl
  · change s.getReg .x24+160#64=_;rw [f.leaf];rfl
  · change s.getReg .x25+0#64=_;rw [f.row];rfl
private theorem args_dst (s : MachineState) (odd : Bool) (call : LeafCall) (f : LeafSys s odd) :
    ((call.args.foldl Sym.bump Sym.original) .x12).eval s=W (call.dst odd) := by
  cases call
  · change s.getReg .x24+64#64=_;rw [f.leaf];rfl
  · change s.getReg .x29+0#64=_;rw [f.slot,BitVec.add_zero];rfl
  · change s.getReg .x29+32#64=_;rw [f.slot];cases odd <;> rfl
  · change s.getReg .x27+0#64=_;rw [f.digest];rfl

attribute [local irreducible] readBuffer
theorem leaf_call (o : Oracle) (s : MachineState) (call : LeafCall) (odd : Bool) (pc : s.pc=pcAt call.pc) (f : LeafSys s odd) :
    ∃ t,Flow o s t 3 1 ∧ t.pc=pcAt (call.pc+3) ∧ LeafCallKeep s t ∧
      t.mem=(compressAt o.compression s call.src (call.dst odd)).mem := by
  let u:=Sym.evaluated call.args s
  have sites : ∀ c : LeafCall,Sym.Listed c.args c.pc ∧ matchesWord .check (c.pc+2,.ECALL) :=by decide +kernel
  have size : call.args.length=2:=by cases call <;> rfl
  obtain ⟨head,out,mem,ip⟩:=Sym.compiled o call.args call.pc s pc (sites call).1 (by
    cases call <;> change ∀ a∈([] : List (Sym.Expr×Nat)),_ <;> simp)
  have stable (q : Reg) (x : q≠.x10) (y : q≠.x12) : u.getReg q=s.getReg q:=by
    apply (out q).trans;cases call <;> cases q <;> first | rfl | contradiction
  rw [size] at head ip
  have sp:=(out .x10).trans (args_src s odd call f)
  have dp:=(out .x12).trans (args_dst s odd call f)
  have query:=reply_flow o ip (known (sites call).2) ((stable _ (by decide) (by decide)).trans f.sys)
    ((stable _ (by decide) (by decide)).trans f.len) ((stable _ (by decide) (by decide)).trans f.kind) sp dp
    (by cases call <;> decide) (by cases call <;> decide) (by cases call <;> cases odd <;> decide) (by cases call <;> cases odd <;> decide)
  let t:=compressAt o.compression u call.src (call.dst odd)
  have eq : readBuffer u call.src 96=readBuffer s call.src 96:=read_buffer_memory_congr u s mem _ _
  refine ⟨t,head.trans query,?_,fun q x y=>(writeBits_register ..).trans (stable q x y),?_⟩
  · change u.pc+4=_;rw [show u.pc=pcAt (call.pc+2) from ip,pc_succ]
  · unfold t compressAt S5Machine.store;rw [eq];exact write_bits_memory_congr u s _ _ mem

theorem compress_mem {s t : MachineState} (H : Compression) (a b : Nat) (eq : s.mem=t.mem) :
    (compressAt H s a b).mem=(compressAt H t a b).mem := by
  unfold compressAt S5Machine.store;rw [read_buffer_memory_congr _ _ eq];exact write_bits_memory_congr _ _ _ _ eq

attribute [local irreducible] compressAt
set_option maxHeartbeats 650000 in
theorem four_leaf_calls (o : Oracle) (s : MachineState) (odd : Bool) (pc : s.pc=pcAt 160) (sys : LeafSys s odd) :
    ∃ t,Flow o s t 12 4 ∧ t.pc=pcAt 172 ∧ LeafCallKeep s t ∧ t.mem=(leafEffect o.compression s odd).mem := by
  obtain ⟨a,x,pa,ka,ma⟩:=leaf_call o s .first odd pc sys
  obtain ⟨b,y,pb,kb,mb⟩:=leaf_call o a .second odd pa (sys.after ka)
  obtain ⟨c,z,pc',kc,mc⟩:=leaf_call o b .third odd pb (sys.after (ka.trans kb))
  obtain ⟨d,w,pd,kd,md⟩:=leaf_call o c .final odd pc' (sys.after ((ka.trans kb).trans kc))
  have eb:=mb.trans (compress_mem o.compression _ _ ma)
  have ec:=mc.trans (compress_mem o.compression _ _ eb)
  exact ⟨d,((x.trans y).trans z).trans w,pd,((ka.trans kb).trans kc).trans kd,md.trans (compress_mem o.compression _ _ ec)⟩
end CommitGolfCandidate.S5Machine.Check
