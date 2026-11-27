import CommitGolfCandidate.RungAClear
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
attribute [local irreducible] readBuffer execute writeBits DetRun

structure Layout where
  group : Nat
  limit : Nat
  base : Nat
  off : Nat
  gfit : group<699051
  small : limit≤24
  offFit : off<2048
  address : base+off=nodeAddress 4 group

def location (c : Layout) : Dest → Nat
  | .scratch n=>32*n
  | .output=>c.base+c.off
def displacement (j : Nat) := 184*(j/2)+88*(j%2)
def rowPtr (c : Layout) := rowBase+2208*c.group
def address (c : Layout) : Source → Nat
  | .scratch n=>32*n
  | .leaf j=>rowPtr c+displacement j

def Apart (a n b : Nat) := a+n≤b ∨ b+32≤a
def Frame (c : Layout) (s t : MachineState) := ∀ a n,1024≤a → a+n≤2^64 → Apart a n (location c .output) →
    readBuffer t a n=readBuffer s a n
theorem Frame.trans {c s t u} (f : Frame c s t) (g : Frame c t u) : Frame c s u :=
  fun a n lo hi sep=>(g a n lo hi sep).trans (f a n lo hi sep)

theorem destBounds (c : Layout) : 5301604576≤location c .output ∧ location c .output+32≤5335159072 ∧ location c .output%8=0 := by
  simp only [location,c.address]
  change _≤5301604576+(96*(c.group/2)+32*(c.group%2)) ∧ _ ∧ _
  have b:=c.gfit
  change _ ∧ 5301604576+(96*(c.group/2)+32*(c.group%2))+32≤_ ∧ (5301604576+(96*(c.group/2)+32*(c.group%2)))%8=0
  omega

def SourceOK (c : Layout) : Source → Prop | .leaf j=>j<c.limit | .scratch n=>n+2<32
def DestOK : Dest → Prop | .output=>True | .scratch j=>j<32
def ReadOK (c : Layout) (sh : Bool) : Source → Prop | .leaf j=>j<c.limit ∧ sh=false | .scratch n=>n+2<32
theorem sourceBounds (c : Layout) (src : Source)
    (ok : SourceOK c src) :
    address c src%8=0 ∧ address c src+96≤MEMORY_BYTES := by
  cases src with
  | scratch n=>change n+2<32 at ok;dsimp [address,MEMORY_BYTES];omega
  | leaf j=>change j<c.limit at ok;have:=c.gfit;have:=c.small;dsimp [address,rowPtr,rowBase,displacement,MEMORY_BYTES];omega

structure Data (o : Oracle) where
  row : Nat→Late.Block
  saved : Nat→Late.Digest
def Data.eval {o} (d : Data o) := value o.compression (fun j=>o.compression (d.row j)) d.saved

structure Live (o : Oracle) (d : Data o) (c : Layout) (b : Bank) (s : MachineState) : Prop where
  env : Env s
  source : s.getReg .x21=Z (rowPtr c+1920)
  dest : s.getReg .x22=Z c.base
  rows : ∀ j,j<c.limit → readBuffer s (address c (.leaf j)) 96=d.row j
  scratch : ∀ n,n<32 → readBuffer s (32*n) 32=d.eval (b.cells n)
  out : ∀ v,b.out=some v → readBuffer s (location c .output) 32=d.eval v
  ptr : ∀ dst,b.ptr=some dst → s.getReg .x12=Z (location c dst)

instance (q : Reg) : Decidable (stableReg q) := inferInstanceAs (Decidable (q≠.x10 ∧ q≠.x12 ∧ q≠.x6))

theorem Env.stable {s t} (e : R4.Env s) (st : Stable s t) : R4.Env t :=
  ⟨(st _ (by decide)).trans e.mode,(st _ (by decide)).trans e.kind,
   (st _ (by decide)).trans e.width,(st _ (by decide)).trans e.root⟩

def srcReg : Source→Reg | .leaf _=>.x21 | .scratch _=>.x0
def srcImm : Source→BitVec 12 | .leaf j=>signedRow j | .scratch n=>BitVec.ofNat 12 (32*n)
def dstReg : Dest→Reg | .output=>.x22 | .scratch _=>.x0
def dstImm (off : Nat) : Dest→BitVec 12 | .output=>BitVec.ofNat 12 off | .scratch n=>BitVec.ofNat 12 (32*n)

theorem srcEq {o d c b s} (live : Live o d c b s) (src : Source)
    (ok : SourceOK c src) :
    s.getReg (srcReg src)+signExtend12 (srcImm src)=Z (address c src) := by
  cases src with
  | scratch n=>
    change n+2<32 at ok;simpa only [srcReg,srcImm,address,dstReg,dstImm,location,c_getReg_x0,Nat.zero_add] using add_signExtend12_ofNat_small 0 (32*n) (by omega)
  | leaf j=>
    change j<c.limit at ok;have bound:=c.small
    have sign : Z 1920+signExtend12 (signedRow j)=Z (displacement j) :=
      (by decide +kernel : ∀ i : Fin 24,Z 1920+signExtend12 (signedRow i.val)=Z (displacement i.val)) ⟨j,by omega⟩
    change s.getReg .x21+_=Z (rowPtr c+displacement j)
    rw [live.source]
    change BitVec.ofNat 64 (rowPtr c+1920)+signExtend12 (signedRow j)=BitVec.ofNat 64 (rowPtr c+displacement j)
    change BitVec.ofNat 64 1920+signExtend12 (signedRow j)=BitVec.ofNat 64 (displacement j) at sign
    rw [BitVec.ofNat_add,BitVec.add_assoc,sign,BitVec.ofNat_add]

theorem dstEq {o d c b s} (live : Live o d c b s) (dst : Dest)
    (ok : DestOK dst) :
    s.getReg (dstReg dst)+signExtend12 (dstImm c.off dst)=Z (location c dst) := by
  cases dst with
  | output=>change s.getReg .x22+_=_;rw [live.dest];exact add_signExtend12_ofNat_small _ _ c.offFit
  | scratch n=>change n<32 at ok;simpa only [srcReg,srcImm,address,dstReg,dstImm,location,c_getReg_x0,Nat.zero_add] using add_signExtend12_ofNat_small 0 (32*n) (by omega)

theorem wordEq {o d c b s} (live : Live o d c b s) (src : Source) (sh : Bool)
    (ok : ReadOK c sh src) :
    mask sh (o.compression (readBuffer s (address c src) 96))=d.eval (b.word src sh) := by
  cases src with
  | leaf j=>change j<c.limit ∧ sh=false at ok;rw [ok.2,live.rows j ok.1];rfl
  | scratch n=>
    change n+2<32 at ok
    rw [readTriple]
    change mask sh (o.compression (readBuffer s (32*n+64) 32 ++ readBuffer s (32*n+32) 32 ++ readBuffer s (32*n) 32))=_
    rw [show 32*n+64=32*(n+2) by omega,show 32*n+32=32*(n+1) by omega,live.scratch _ (by omega),live.scratch _ (by omega),live.scratch _ (by omega)]
    rfl
end CommitGolfCandidate.RungA.Kernel
