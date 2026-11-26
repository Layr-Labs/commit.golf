import CommitGolfCandidate.StreamCopyMachine
namespace TwoPermutationPrototype.PackedOpening.StreamCopy
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Pack
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg set_byte_read

@[local simp] private theorem op156 : instrAt 156=.BEQ .x22 .x18 48 := rfl
@[local simp] private theorem op157 : instrAt 157=.JAL .x0 4636 := rfl
@[local simp] private theorem op1316 : instrAt 1316=.ADDI .x30 .x20 0 := rfl
@[local simp] private theorem op1317 : instrAt 1317=.ADDI .x24 .x20 0 := rfl
@[local simp] private theorem op1318 : instrAt 1318=.ADDI .x25 .x16 0 := rfl
@[local simp] private theorem op1319 : instrAt 1319=.BEQ .x25 .x0 3860 := rfl
@[local simp] private theorem op2280 : instrAt 2280=.ADDI .x30 .x30 481 := rfl
@[local simp] private theorem op2281 : instrAt 2281=.ADDI .x24 .x24 480 := rfl
@[local simp] private theorem op2282 : instrAt 2282=.ADDI .x25 .x25 4095 := rfl
@[local simp] private theorem op2283 : instrAt 2283=.BNE .x25 .x0 4340 := rfl
@[local simp] private theorem op2284 : instrAt 2284=.SUB .x28 .x26 .x24 := rfl
@[local simp] private theorem op2285 : instrAt 2285=.ANDI .x28 .x28 4088 := rfl
@[local simp] private theorem op2286 : instrAt 2286=.ADD .x28 .x24 .x28 := rfl
@[local simp] private theorem op2287 : instrAt 2287=.BEQ .x24 .x28 80 := rfl
@[local simp] private theorem op2304 : instrAt 2304=.ADDI .x30 .x30 8 := rfl
@[local simp] private theorem op2305 : instrAt 2305=.ADDI .x24 .x24 8 := rfl
@[local simp] private theorem op2306 : instrAt 2306=.BNE .x24 .x28 8120 := rfl
@[local simp] private theorem op2307 : instrAt 2307=.BEQ .x24 .x26 24 := rfl
@[local simp] private theorem op2310 : instrAt 2310=.ADDI .x30 .x30 1 := rfl
@[local simp] private theorem op2311 : instrAt 2311=.ADDI .x24 .x24 1 := rfl
@[local simp] private theorem op2312 : instrAt 2312=.BNE .x24 .x26 8176 := rfl
@[local simp] private theorem op2313 : instrAt 2313=.ADDI .x22 .x18 0 := rfl
@[local simp] private theorem op2314 : instrAt 2314=.JAL .x0 2088520 := rfl
@[local simp] private theorem op264 : instrAt 264=.BEQ .x22 .x18 48 := rfl
@[local simp] private theorem op265 : instrAt 265=.JAL .x0 8200 := rfl
@[local simp] private theorem op2315 : instrAt 2315=.ADDI .x30 .x20 0 := rfl
@[local simp] private theorem op2316 : instrAt 2316=.ADDI .x24 .x20 0 := rfl
@[local simp] private theorem op2317 : instrAt 2317=.ADDI .x25 .x16 0 := rfl
@[local simp] private theorem op2318 : instrAt 2318=.BEQ .x25 .x0 3852 := rfl
@[local simp] private theorem op3277 : instrAt 3277=.ADDI .x30 .x30 480 := rfl
@[local simp] private theorem op3278 : instrAt 3278=.ADDI .x24 .x24 479 := rfl
@[local simp] private theorem op3279 : instrAt 3279=.ADDI .x25 .x25 4095 := rfl
@[local simp] private theorem op3280 : instrAt 3280=.BNE .x25 .x0 4348 := rfl
@[local simp] private theorem op3281 : instrAt 3281=.SUB .x28 .x26 .x24 := rfl
@[local simp] private theorem op3282 : instrAt 3282=.ANDI .x28 .x28 4088 := rfl
@[local simp] private theorem op3283 : instrAt 3283=.ADD .x28 .x24 .x28 := rfl
@[local simp] private theorem op3284 : instrAt 3284=.BEQ .x24 .x28 80 := rfl
@[local simp] private theorem op3301 : instrAt 3301=.ADDI .x30 .x30 8 := rfl
@[local simp] private theorem op3302 : instrAt 3302=.ADDI .x24 .x24 8 := rfl
@[local simp] private theorem op3303 : instrAt 3303=.BNE .x24 .x28 8120 := rfl
@[local simp] private theorem op3304 : instrAt 3304=.BEQ .x24 .x26 24 := rfl
@[local simp] private theorem op3307 : instrAt 3307=.ADDI .x30 .x30 1 := rfl
@[local simp] private theorem op3308 : instrAt 3308=.ADDI .x24 .x24 1 := rfl
@[local simp] private theorem op3309 : instrAt 3309=.BNE .x24 .x26 8176 := rfl
@[local simp] private theorem op3310 : instrAt 3310=.ADDI .x22 .x18 0 := rfl
@[local simp] private theorem op3311 : instrAt 3311=.JAL .x0 2084964 := rfl
@[local simp] private theorem jump156 : pcOf 156+signExtend13 48#13=pcOf 168 := by decide
@[local simp] private theorem jump157 : pcOf 157+signExtend21 4636#21=pcOf 1316 := by decide
@[local simp] private theorem jump1319 : pcOf 1319+signExtend13 3860#13=pcOf 2284 := by decide
@[local simp] private theorem jump2283 : pcOf 2283+signExtend13 4340#13=pcOf 1320 := by decide
@[local simp] private theorem jump2287 : pcOf 2287+signExtend13 80#13=pcOf 2307 := by decide
@[local simp] private theorem jump2306 : pcOf 2306+signExtend13 8120#13=pcOf 2288 := by decide
@[local simp] private theorem jump2307 : pcOf 2307+signExtend13 24#13=pcOf 2313 := by decide
@[local simp] private theorem jump2312 : pcOf 2312+signExtend13 8176#13=pcOf 2308 := by decide
@[local simp] private theorem jump2314 : pcOf 2314+signExtend21 2088520#21=pcOf 156 := by decide
@[local simp] private theorem jump264 : pcOf 264+signExtend13 48#13=pcOf 276 := by decide
@[local simp] private theorem jump265 : pcOf 265+signExtend21 8200#21=pcOf 2315 := by decide
@[local simp] private theorem jump2318 : pcOf 2318+signExtend13 3852#13=pcOf 3281 := by decide
@[local simp] private theorem jump3280 : pcOf 3280+signExtend13 4348#13=pcOf 2319 := by decide
@[local simp] private theorem jump3284 : pcOf 3284+signExtend13 80#13=pcOf 3304 := by decide
@[local simp] private theorem jump3303 : pcOf 3303+signExtend13 8120#13=pcOf 3285 := by decide
@[local simp] private theorem jump3304 : pcOf 3304+signExtend13 24#13=pcOf 3310 := by decide
@[local simp] private theorem jump3309 : pcOf 3309+signExtend13 8176#13=pcOf 3305 := by decide
@[local simp] private theorem jump3311 : pcOf 3311+signExtend21 2084964#21=pcOf 264 := by decide
@[local simp] private theorem immediate481 : signExtend12 481#12=481#64 := by decide
@[local simp] private theorem immediate480 : signExtend12 480#12=480#64 := by decide
@[local simp] private theorem immediate1 : signExtend12 1#12=1#64 := by decide
@[local simp] private theorem immediate8 : signExtend12 8#12=8#64 := by decide
@[local simp] private theorem immediate479 : signExtend12 479#12=479#64 := by decide

inductive Control where | enter | record | prepare | wide | test | byte | finish

def path (h : Bool) : Control → List Nat
 | .enter => [guardWord h,guardWord h+1,origin h,origin h+1,origin h+2,origin h+3]
 | .record => (List.range 4).map fun i=>latch h+i
 | .prepare => (List.range 4).map fun i=>latch h+(4+i)
 | .wide => (List.range 3).map fun i=>latch h+(24+i)
 | .test => [latch h+27]
 | .byte => (List.range 3).map fun i=>latch h+(30+i)
 | .finish => [latch h+33,latch h+34]

def beginAt (h : Bool) : Control → Nat
 | .enter=>guardWord h | .record=>latch h | .prepare=>latch h+4 | .wide=>latch h+24
 | .test=>latch h+27 | .byte=>latch h+30 | .finish=>latch h+33

def bill : Control → Nat | .enter=>6 | .record|.prepare=>4 | .wide|.byte=>3 | .test=>1 | .finish=>2
def after (h : Bool) (c : Control) (s : MachineState) := run s (path h c)

theorem ctrlRun {s : MachineState} (h : Bool) (c : Control) (pc : s.pc=pcOf (beginAt h c))
    (gate : c=.enter → s.getReg .x22≠s.getReg .x18) :
    Runs s (after h c s) (bill c) (bill c) := by
  have ok : PathOK s (path h c) := by
    cases c <;> cases h <;>
      simp_all [path,PathOK,beginAt,latch,width,origin,guardWord,ordinaryInstr,execInstrBr,
        memoryArgumentsValid,memAccess,List.range_succ]
  exact (runs_path _ _ ok).cast (by cases h <;> cases c <;>rfl) (by cases h <;> cases c <;>decide)

theorem ctrlFrame (h : Bool) (c : Control) (s : MachineState) : Frame s (after h c s) := by
  intro r hr
  by_cases z:r=.x0
  · subst r;rfl
  apply run_keeps
  have ne (x : Reg) (hx : x∈([.x22,.x23,.x24,.x25,.x28,.x30] : List Reg)) : x≠r := fun e=>hr (e ▸ hx)
  cases h <;> cases c <;>
    simp [path,writesAny,origin,latch,width,guardWord,List.range_succ,writesReg,
      Ne.symm z,ne .x25 (by decide),ne .x24 (by decide),ne .x30 (by decide),ne .x22 (by decide),ne .x28 (by decide)]

theorem ctrlBytes (h : Bool) (c : Control) (s : MachineState) (q : Word) :
    (after h c s).getByte q=s.getByte q := by
  apply getByte_of_mem
  exact run_mem _ _ (by cases h <;> cases c <;> decide)

@[local simp] private theorem reg_branch (c : Prop) [Decidable c] (s : MachineState) (x y : Word) (r : Reg) :
    (if c then s.setPC x else s.setPC y).getReg r=s.getReg r := by split <;> rfl

theorem entryRegs (h : Bool) (s : MachineState) (base k : Nat) (b : s.getReg .x20=word base)
    (n : s.getReg .x16=word k) (gate:s.getReg .x22≠s.getReg .x18) (bound:k<2^64)
    (pc:s.pc=pcOf (guardWord h)) :
    let t:=after h .enter s
    t.getReg .x30=word base ∧ t.getReg .x24=word base ∧ t.getReg .x25=word k ∧
    t.pc=pcOf (if k=0 then latch h+4 else start h .record) := by
  have zero : word k=0#64 ↔ k=0 := w_inj k 0 bound (by decide)
  cases h <;> by_cases hk:k=0 <;>
    simp_all [after,run,path,latch,start,width,origin,guardWord,execInstrBr]

theorem recordRegs (h : Bool) (s : MachineState) (src dst k : Nat)
    (a:s.getReg .x30=word src) (b:s.getReg .x24=word dst)
    (n:s.getReg .x25=word (k+1)) (bound:k<2^64) (pc:s.pc=pcOf (latch h)) :
    let t:=after h .record s
    t.getReg .x30=word (src+(width h+1)) ∧ t.getReg .x24=word (dst+width h) ∧
    t.getReg .x25=word k ∧ t.pc=pcOf (if k=0 then latch h+4 else start h .record) := by
  have de : word (k+1)+signExtend12 4095#12=word k := by
    unfold word; rw [BitVec.ofNat_add,BitVec.add_assoc,show BitVec.ofNat 64 1+signExtend12 4095#12=0#64 by decide,BitVec.add_zero]
  have zero : word k=0#64 ↔ k=0 := w_inj k 0 bound (by decide)
  cases h <;> by_cases hk:k=0 <;>
    simp_all [after,run,path,latch,start,width,origin,execInstrBr,List.range_succ,w_add]

/-- Clearing the three low bits rounds the unsigned footer length down to its full 8-byte blocks. -/
private theorem roundEight (n : Nat) (small:n<2^64) :
    word n &&& signExtend12 4088#12=word (8*(n/8)) := by
  have mask : signExtend12 4088#12 = ~~~(7#64) := by decide
  rw [mask]
  have eq (x : Word) : x &&& ~~~(7#64) = (x >>> 3) <<< 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]
  rw [eq]
  rw [w_shr n 3 small,w_shl]
  congr 1;omega

theorem prepareRegs (h : Bool) (s : MachineState) (dst n : Nat) (small:dst+n<2^64)
    (b:s.getReg .x24=word dst) (e:s.getReg .x26=word (dst+n))
    (pc:s.pc=pcOf (latch h+4)) :
    let t:=after h .prepare s
    t.getReg .x30=s.getReg .x30 ∧ t.getReg .x24=word dst ∧ t.getReg .x28=word (dst+8*(n/8)) ∧
    t.pc=pcOf (if n/8=0 then latch h+27 else start h .eight) := by
  have diff : word (dst+n)-word dst=word n := by rw [w_sub _ _ (by omega) small];congr 1;omega
  have eq : word dst=word (dst+8*(n/8)) ↔ n/8=0 := by rw [w_inj _ _ (by omega) (by omega)];omega
  by_cases test:n/8=0
  · have hlt : n<8 := by omega
    cases h <;> simp [after,run,path,latch,start,width,origin,execInstrBr,List.range_succ,pc,b,e,diff,
      roundEight n (by omega),w_add,test,hlt]
  · have hn : ¬n<8 := by omega
    have neq : word dst≠BitVec.ofNat 64 (dst+8*(n/8)) := fun he=>test (eq.mp he)
    cases h <;> simp [after,run,path,latch,start,width,origin,execInstrBr,List.range_succ,pc,b,e,diff,
      roundEight n (by omega),w_add,neq,test,hn]

theorem wideRegs (h : Bool) (s : MachineState) (src dst endp : Nat)
    (a:s.getReg .x30=word src) (b:s.getReg .x24=word dst)
    (e:s.getReg .x28=word endp) (small:dst+8≤endp) (room:endp<2^64)
    (pc:s.pc=pcOf (latch h+24)) :
    let t:=after h .wide s
    t.getReg .x30=word (src+8) ∧ t.getReg .x24=word (dst+8) ∧ t.getReg .x28=word endp ∧
    t.pc=pcOf (if dst+8=endp then latch h+27 else start h .eight) := by
  have eq := w_inj (dst+8) endp (by omega) room
  cases h <;> by_cases test:dst+8=endp <;>
    simp_all [after,run,path,latch,start,width,origin,execInstrBr,List.range_succ,w_add]

theorem testRegs (h : Bool) (s : MachineState) (dst endp : Nat)
    (b:s.getReg .x24=word dst) (e:s.getReg .x26=word endp) (small:dst≤endp) (room:endp<2^64)
    (pc:s.pc=pcOf (latch h+27)) :
    let t:=after h .test s
    t.getReg .x30=s.getReg .x30 ∧ t.getReg .x24=word dst ∧
    t.pc=pcOf (if dst=endp then latch h+33 else start h .last) := by
  have eq := w_inj dst endp (by omega) room
  cases h <;> by_cases test:dst=endp <;>
    simp_all [after,run,path,latch,start,width,origin,execInstrBr]

theorem byteRegs (h : Bool) (s : MachineState) (src dst endp : Nat)
    (a:s.getReg .x30=word src) (b:s.getReg .x24=word dst)
    (e:s.getReg .x26=word endp) (small:dst+1≤endp) (room:endp<2^64)
    (pc:s.pc=pcOf (latch h+30)) :
    let t:=after h .byte s
    t.getReg .x30=word (src+1) ∧ t.getReg .x24=word (dst+1) ∧
    t.pc=pcOf (if dst+1=endp then latch h+33 else start h .last) := by
  have eq := w_inj (dst+1) endp (by omega) room
  cases h <;> by_cases test:dst+1=endp <;>
    simp_all [after,run,path,latch,start,width,origin,execInstrBr,List.range_succ,w_add]

theorem finishRegs (h : Bool) (s : MachineState) (pc:s.pc=pcOf (latch h+33)) :
    let t:=after h .finish s
    t.getReg .x22=s.getReg .x18 ∧ t.pc=pcOf (guardWord h) := by
  cases h <;> simp_all [after,run,path,latch,start,width,origin,guardWord,execInstrBr]

end TwoPermutationPrototype.PackedOpening.StreamCopy
