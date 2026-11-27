import CommitGolfCandidate.Stage3cCapHash
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
theorem child_bounds (d p : Nat) (hd : d<8) (hp : p<layerCount (d+1)) :
    p<groups d ∧ 2*p<paddedCount d ∧ 2*p+1<paddedCount d := by
  have e : groups d=layerCount (d+1):=(cap_geometry ⟨d,by omega⟩).2.2.2.2.2.2.1 hd
  unfold paddedCount;rw [if_neg (by omega : d≠8)];omega
theorem cache_row (s : MachineState) (v : Values) (cache : Cache s v) (d p : Nat) (hd : d<8) (hp : p<layerCount (d+1)) :
    readBuffer s (rowAt d p) 96=Late.parentBlock (v d (2*p)) (v d (2*p+1)) := by
  obtain ⟨group,left,right⟩:=child_bounds d p hd hp
  have lo : nodeAt d (2*p)=rowAt d p:=by unfold nodeAt rowAt;omega
  have hi : nodeAt d (2*p+1)=rowAt d p+32:=by unfold nodeAt rowAt;omega
  have a:=cache.node d (by omega) (2*p) left
  have b:=cache.node d (by omega) (2*p+1) right
  have c:=cache.gap d hd p group
  rw [lo] at a;rw [hi] at b
  have upper:=read_join s (rowAt d p+32) 32 32
  have all:=read_join s (rowAt d p) 32 64
  change readBuffer s (gapAt d p) 32++readBuffer s (rowAt d p+32) 32=(readBuffer s (rowAt d p+32) 64).extractLsb' 0 512 at upper
  rw [a,BitVec.extractLsb'_eq_self] at all
  rw [b,c,BitVec.extractLsb'_eq_self] at upper
  rw [←upper] at all;exact all.symm

theorem cache_base {H x} (q : Fin 4) (p : Nat) (small : p<256) :
    capVal H x q 0 p=pairValue H (lookup H x 128 (2*p)) (lookup H x 128 (2*p+1)) (slotValue x q p) := by
  unfold capVal;rw [Pw.Auth.upper,if_pos small,pair_model]
theorem cache_next (H : Compression) (x : CheckInput) (q : Fin 4) (d p : Nat) (hp : p<layerCount (d+1)) :
    capVal H x q (d+1) p=Pw.Auth.compressRow H ((16+d)+1) (Late.parentBlock (capVal H x q d (2*p)) (capVal H x q d (2*p+1))) := by
  have same : 16+(d+1)=17+d:=by omega
  change p<Geo.width (16+(d+1)) at hp;rw [same] at hp
  unfold capVal;rw [Pw.Auth.upper,if_pos hp,show 16+d+1=17+d by omega]

def upperEntry (d : Nat) := ([901,923,946,970,994,1018,1042,1066,1084] : List Nat)[d]?.getD 0
def upperLoop (d : Nat) := ([905,928,952,976,1000,1024,1048,1072] : List Nat)[d]?.getD 0
def liOps (rd : Reg) (n : Nat) : List Sym.Calc :=
  if n<2048 then [.addi rd .x0 (BitVec.ofNat 12 n)] else
    [.lui rd (BitVec.ofNat 20 ((n+2048)/4096))]++(if n%4096=0 then [] else [.addi rd rd (BitVec.ofNat 12 n)])
def upperHeader (d : Nat) :=liOps .x14 (layerStart d)++liOps .x15 (layerStart (d+1))++
  [.addi .x23 .x0 0,.addi .x9 .x0 (BitVec.ofNat 12 (layerCount (d+1)))]
def upperAddress (d : Nat) : List Sym.Calc :=
  [.slli .x6 .x23 1,.add .x6 .x6 .x23,.slli .x6 .x6 5,.add .x10 .x14 .x6]++
  (if d=7 then [.addi .x6 .x0 0] else [.srli .x6 .x23 1,.slli .x7 .x6 1,.add .x7 .x7 .x6,.slli .x7 .x7 5,
    .andi .x6 .x23 1,.slli .x6 .x6 5,.add .x6 .x7 .x6])++[.add .x12 .x15 .x6]
def configPC (d : Nat):=upperLoop d+(upperAddress d).length
def upperLatch (d : Nat):=configPC d+4
theorem upper_sites : ∀ j : Fin 8,let d:=j.val;
    Sym.Listed (upperHeader d) (upperEntry d) ∧ upperEntry d+(upperHeader d).length=upperLoop d ∧ (upperHeader d).length≤6 ∧
    Sym.Listed (upperAddress d) (upperLoop d) ∧ (upperAddress d).length≤12 ∧ parentSites (configPC d) (16+d) ∧
    upperLatch d<2147 ∧ matchesWord .check (upperLatch d,.ADDI .x23 .x23 1) ∧ BranchSite (upperLatch d+1) (upperLoop d) .lt .x23 .x9 ∧
    upperLatch d+2=upperEntry (d+1) ∧ parentFuel (16+d)=19 ∧ levelCalls (16+d)=1 :=by decide +kernel
end CommitGolfCandidate.Chained.BinaryMachine.Check
