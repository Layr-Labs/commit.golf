import CommitGolfCandidate.CapBStream
import CommitGolfCandidate.CapBWalkApi
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (handlerLen carryBits)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

def heapBase : Nat := 4294971424
def proofBase : Nat := 13824430176
def scratch : Nat := 12288
def capStart (k : Nat) := proofBase+534*k
def work (k : Nat) := if k%4=0 then capStart k else scratch
def copyDest (k : Nat) := if k%4=0 then 0 else capStart k

structure Env (groups : List Nat) (heap : Nat→D) (k : Nat) (s : MachineState) : Prop where
  count : k≤16777216
  marks : ∀ n,1≤n → n<64 → gword s (markBase+8*n)=treeWord groups n (height n)
  source : ∀ n,n<512 → ∀ i,i<4 → gword s (heapBase+32*n+8*i)=dw (heap n) i

def streamOf (seed : Word) (heap : Nat→D) (xs : List Nat) := stream seed (xs.map heap)

structure Inv (heap : Nat→D) (k : Nat) (ref : MachineState) (seed : Word) (xs : List Nat) (s : MachineState) : Prop where
  data : Buffer ref s (work k) (streamOf seed heap xs).out
  phase : s.getReg .x19=pc (startHandler xs.length)
  dest : s.getReg .x21=addr (work k+8*(streamOf seed heap xs).out.length)
  acc : s.getReg .x22=(streamOf seed heap xs).carry
  output : s.getReg .x20=addr proofBase
  one : s.getReg .x23=1#64
  first : s.getReg .x24=pc 6144
  source : s.getReg .x25=addr heapBase
  marks : s.getReg .x26=addr markBase
  leaf : s.getReg .x27=256#64
  copy : s.getReg .x14=addr (copyDest k)

theorem Inv.move {H k ref z xs s t} (a : Inv H k ref z xs s) (same : Moved s t) : Inv H k ref z xs t :=
  ⟨a.data.mem same.1,(same.2 _ (by decide)).trans a.phase,(same.2 _ (by decide)).trans a.dest,
    (same.2 _ (by decide)).trans a.acc,(same.2 _ (by decide)).trans a.output,(same.2 _ (by decide)).trans a.one,
    (same.2 _ (by decide)).trans a.first,(same.2 _ (by decide)).trans a.source,(same.2 _ (by decide)).trans a.marks,
    (same.2 _ (by decide)).trans a.leaf,(same.2 _ (by decide)).trans a.copy⟩

theorem work_geo (k : Nat) (room : k≤16777216) : (work k)%8=0 ∧ markBase+512≤work k ∧ work k+8192≤MEMORY_BYTES ∧
    (heapBase+32*512≤work k ∨ work k+8192≤heapBase) := by
  unfold work capStart proofBase scratch markBase heapBase MEMORY_BYTES;split_ifs <;> omega

private theorem height_good : ∀ n : Fin 64, ∀ h : Fin 6, 32≤n.val*2^h.val → (n.val+1)*2^h.val≤64 → height n.val=h.val := by decide +kernel

private theorem mark_at {gs H k ref z xs s} (env : Env gs H k ref) (inv : Inv H k ref z xs s) (n h : Nat)
    (lo : 32≤n*2^h) (hi : (n+1)*2^h≤64) :
    s.getMem (addr (markBase+8*n))=treeWord gs n h := by
  have power:=Nat.one_le_two_pow (n:=h)
  have pos : 0<n := by by_contra! a;simp [Nat.eq_zero_of_le_zero a] at lo
  have hn : n<64 := by nlinarith
  have small : h<6 := by
    by_contra! b
    have bound : 64≤2^h := Nat.pow_le_pow_right (by decide : 0<2) b
    nlinarith
  have geo:=work_geo k env.count
  have same:=inv.data.frame (addr (markBase+8*n)) (Or.inl (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show markBase+8*n<2^64 by unfold markBase;omega)];omega))
  exact same.trans ((env.marks n pos hn).trans (congrArg (treeWord gs n) (height_good ⟨n,hn⟩ ⟨h,small⟩ lo hi)))

theorem call_handler {gs H k ref z xs s w n} (env : Env gs H k ref) (inv : Inv H k ref z xs s)
    (num : xs.length<256) (small : w<12320) (node : n<512) (x6 : s.getReg .x6=addr n) (here : s.pc=pc w)
    (code : (openingImage.code[w]?).bind decodeInstruction=some (.base (.JALR .x18 .x19 0))) :
    ∃ t,Run openingImage s t (1+handlerLen xs.length) (1+handlerLen xs.length) ∧ t.pc=pc (w+1) ∧
      Inv H k ref z (xs++[n]) t ∧ t.getReg .x6=addr n ∧ t.getReg .x16=s.getReg .x16 := by
  let j : Fin 32:=⟨xs.length%32,by omega⟩
  let raw:=streamOf z H xs
  let base:=work k
  let dst:=base+8*raw.out.length
  let src:=heapBase+32*n
  have phase : startHandler j=startHandler xs.length := by simp [j,startHandler]
  let a:=execInstrBr s (.JALR .x18 .x19 0)
  have call : Run openingImage s a 1 1 := one (by omega) here code rfl
  have pcA : a.pc=pc (startHandler j) := by
    change ((s.getReg .x19+signExtend12 0) &&& ~~~1#64)=_
    rw [inv.phase,show signExtend12 0=0#64 from rfl,BitVec.add_zero,pc_mask,phase]
  have link : a.getReg .x18=pc (w+1) := by
    change ((s.setReg .x18 (s.pc+4)).setPC _).getReg .x18=_
    simp [MachineState.getReg_setReg_eq (by decide : Reg.x18≠.x0),here];exact pc_add w
  have stable (r : Reg) (free : r≠.x18) : a.getReg r=s.getReg r := by
    simp [a,execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ free.symm]
  have mem : a.mem=s.mem := rfl
  have geo:=work_geo k env.count
  have bsz:=stream_size z (xs.map H)
  change 8*raw.out.length=Layout2.Cap.body (xs.map H).length at bsz
  rw [List.length_map] at bsz
  have fit : 8*raw.out.length+32≤8192 := by unfold Layout2.Cap.body at bsz;omega
  have wid : width j≤4 := by unfold width;split <;> decide
  have safe : Safe ⟨dst,src,width j,4⟩ := by
    constructor
    · intro b;cases b <;> dsimp [Areas.start,src,dst,base,heapBase] <;> omega
    · intro b;cases b <;> dsimp [Areas.start,Areas.words,src,dst,base,heapBase,MEMORY_BYTES] <;> first | omega | (unfold MEMORY_BYTES at geo;omega)
    · change src+32≤dst ∨ dst+8*width j≤src
      dsimp [src,dst,base];omega
  obtain ⟨t,ran,pt,ph,dend,carry,outputs,keep,frame⟩:=emit a j (w+1) dst src (by omega) pcA
    ((stable _ (by decide)).trans (phase.symm ▸ inv.phase)) link ((stable _ (by decide)).trans inv.dest)
    (by rw [stable _ (by decide),stable _ (by decide),inv.source,x6,BitVec.shiftLeft_eq_mul_twoPow]
        change addr heapBase+addr n*addr 32=addr src
        change BitVec.ofNat 64 heapBase+(BitVec.ofNat 64 n*BitVec.ofNat 64 32)=BitVec.ofNat 64 src
        rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];congr 1;dsimp [src];omega) safe
  have heapWord (i : Nat) (bound : i<4) : gword a (src+8*i)=dw (H n) i := by
    have address : (addr (src+8*i)).toNat=src+8*i := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show src+8*i<2^64 by dsimp [src,heapBase];omega)]
    have fromMem:=inv.data.frame (addr (src+8*i)) (by rw [address];change src+8*i<work k ∨ work k+8*raw.out.length≤src+8*i;unfold src;omega)
    exact fromMem.trans (env.source n node i bound)
  have cnt : raw.count=xs.length := by simp [raw,streamOf,stream_count]
  have append : streamOf z H (xs++[n])=push raw (H n) := by simp [streamOf,raw,stream_snoc]
  have ylen : (emittedWords j raw.carry (H n)).length=width j := by simp [emittedWords]
  have buf : Buffer ref t base (raw.out++emittedWords j raw.carry (H n)) := by
    apply inv.data.append (m:=s) (by rw [ylen];change work k+8*(raw.out.length+width j)≤MEMORY_BYTES;omega)
    · intro i hi;rw [ylen] at hi
      have eq:=outputs i hi
      simp only [stable _ (by decide : Reg.x11≠.x18),stable _ (by decide : Reg.x22≠.x18),inv.acc] at eq
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rwa [ylen]),Option.getD_some]
      simp only [emittedWords,List.getElem_ofFn]
      apply eq.trans
      unfold nextWord
      split
      · rename_i small;exact heapWord i (by omega)
      · change merged _ _ (gword a (src+8*3))=_;rw [heapWord 3 (by decide)]
    · intro w free;exact (frame w (by simpa [dst,ylen] using free)).trans (by simp only [MachineState.getMem,mem])
  have outside (r : Reg) (free : r∉[.x7,.x28,.x31,.x22,.x21,.x19]) (n18 : r≠.x18) : t.getReg r=s.getReg r :=
    (keep r free).trans (stable r n18)
  have nextPhase : startHandler (j.val+1)=startHandler (xs.length+1) := by
    have eq : (xs.length%32+1)%32=(xs.length+1)%32 := by omega
    exact congrArg (fun a=>6144+16*a) eq
  refine ⟨t,?_,pt,?_,(outside _ (by decide) (by decide)).trans x6,outside _ (by decide) (by decide)⟩
  · have eq : handlerLen j=handlerLen xs.length := by simp [handlerLen,carryBits,j] <;> rfl
    simpa only [eq] using call.thenDo ran
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [append,push,cnt] using buf
    · simpa only [List.length_append,List.length_singleton,←nextPhase] using ph
    · rw [append];simp only [push,cnt,List.length_append,emittedWords,List.length_ofFn]
      rw [dend];congr 1;dsimp [dst,base,j];omega
    · rw [append];simp only [push,cnt]
      simpa only [stable _ (by decide : Reg.x22≠.x18),inv.acc,show src+24=src+8*3 by omega,heapWord 3 (by decide)] using carry
    all_goals first
      | exact (outside _ (by decide) (by decide)).trans inv.output
      | exact (outside _ (by decide) (by decide)).trans inv.one
      | exact (outside _ (by decide) (by decide)).trans inv.first
      | exact (outside _ (by decide) (by decide)).trans inv.source
      | exact (outside _ (by decide) (by decide)).trans inv.marks
      | exact (outside _ (by decide) (by decide)).trans inv.leaf
      | exact (outside _ (by decide) (by decide)).trans inv.copy

def walk_api {gs H k ref} (seed : Word) (env : Env gs H k ref) : API gs where
  inv:=Inv H k ref seed
  move:=fun h move=>h.move move
  constants:=fun h=>⟨h.marks,h.leaf,h.one⟩
  mark:=fun inv n h lo hi=>mark_at env inv n h lo hi
  call:=fun inv n w node x pc code=>call_handler env inv n w node x pc code
end CommitGolfCandidate.CapB
