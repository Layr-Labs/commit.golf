import CommitGolfCandidate.ReconstructedCheckRecordAccess

namespace CommitGolfCandidate.Reconstruction.CheckSlotWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CheckRecordAccess LeafModel OpeningOps
open TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
abbrev W:=BitVec.ofNat 64

def reserve (r : Reg) := r≠.x16 ∧ r≠.x17
deriving instance Decidable for reserve

def point (k j : Nat) := wordAddress (capWord k j)

theorem add (k j : Nat) : point k 0 + W (8*j)=point k j := by
  change W (8*(524288+4*k+0))+W (8*j)=W (8*(524288+4*k+j))
  rw [←BitVec.ofNat_add];exact congrArg W (by omega)

def first : List Op := [.reg .x16 (.lui 1024),.reg .x16 (.add .x23 .x16)]

theorem begin (o : Oracle) (s : MachineState) (k : Nat) (pc : s.pc=CommitBlocks.addr 398) (shift : s.getReg .x23=W (32*k)) :
    ∃ t,Segment o 2 s t [] ∧ t.pc=CommitBlocks.addr 400 ∧ t.getReg .x16=point k 0 ∧
      (∀ r,reserve r→t.getReg r=s.getReg r) ∧ Mem s t := by
  let m:=CheckRecordHeader.model s
  obtain ⟨t,run,endPC,fit⟩:=CheckStraight.block o m first 398 (by decide) (CheckRecordOps.image _ _ (by decide))
    (by simp [first,Checked,Op.Valid]) s pc (CheckRecordHeader.fits s)
  refine ⟨t,run,endPC,?_,?_,fit.memory⟩
  · rw [fit.registers];change s.getReg .x23+4194304#64=_;rw [shift]
    change W (32*k)+W 4194304=W (8*(524288+4*k+0));rw [←BitVec.ofNat_add];congr 1;omega
  · intro r h;apply CheckRecordOps.physical first fit (CheckRecordHeader.fits s) r;simpa [first,CheckRecordOps.dest] using h.1

def loadAt (j : Fin 4):=400+2*j.val
def rd (j : Fin 4) : Reg := if j.val=3 then .x16 else .x17
def operand (j : Fin 4) : Reg:=CheckPair.current j
def disp (j : Fin 4) := BitVec.ofNat 12 (8*j.val)
def immediate (j : Fin 4) : BitVec 13 := ![6816,6808,6800,7000] j
def okAt (j : Fin 4) := if j.val=3 then 109 else loadAt j+2
def failAt (j : Fin 4) := if j.val=3 then 408 else 57
def taken (j : Fin 4) := if j.val=3 then 109 else 57
def kind (j : Fin 4) : CheckOrdinary.Cond:=if j.val=3 then .eq else .ne

theorem one (o : Oracle) (s : MachineState) (k : Nat) (j : Fin 4) (room : k<1024)
    (pc : s.pc=CommitBlocks.addr (loadAt j)) (p : s.getReg .x16=point k 0) :
    let eq:=s.getReg (operand j)=s.getMem (point k j)
    ∃ t,Segment o 2 s t [] ∧ t.pc=(if eq then CommitBlocks.addr (okAt j) else CommitBlocks.addr (failAt j)) ∧
      (∀ r,reserve r→t.getReg r=s.getReg r) ∧ Mem s t ∧ (j.val<3→t.getReg .x16=point k 0) := by
  let op : Op:=.ld (rd j) .x16 (disp j) (capWord k j)
  let m:=CheckRecordHeader.model s
  have chk : CheckStraight.Listed (loadAt j) ([op].map Op.instr):= by refine ⟨?_,True.intro⟩;fin_cases j <;> rfl
  have defined : Checked m [op]:=by
    refine ⟨⟨by have lim:=j.isLt;unfold capWord;omega,?_⟩,True.intro⟩
    change s.getReg .x16+signExtend12 (disp j)=point k j;rw [p,(by decide : ∀ z : Fin 4,signExtend12 (disp z)=W (8*z.val)) j,add]
  obtain ⟨u,load,atU,fit⟩:=CheckStraight.block o m [op] (loadAt j) (by unfold loadAt;have:=j.isLt;simp;omega) chk defined s pc (CheckRecordHeader.fits s)
  have control : ∀ z : Fin 4,(loadAt z+1<796 ∧ CheckMemoryOps.word (loadAt z+1)
      (.base (CheckBranch.branch (kind z) (operand z) (rd z) (immediate z)))=true ∧
      CommitBlocks.addr (loadAt z+1)+signExtend13 (immediate z)=CommitBlocks.addr (taken z)):=by decide
  have raw:=control j
  have bits:=raw.2.1;unfold CheckMemoryOps.word at bits;rw [Bool.and_eq_true] at bits
  have dec:=CheckDecode.same_sound bits.2
  have br:=CheckBranch.event o u (loadAt j+1) (taken j) (kind j) (operand j) (rd j) (immediate j) raw.1 atU dec raw.2.2
  have value : u.getReg (rd j)=s.getMem (point k j):=by rw [fit.registers];fin_cases j <;> rfl
  have left : u.getReg (operand j)=s.getReg (operand j):=by rw [fit.registers];fin_cases j <;> rfl
  refine ⟨u.setPC (if CheckOrdinary.Cond.test (kind j) (u.getReg (operand j)) (u.getReg (rd j)) then CommitBlocks.addr (taken j) else CommitBlocks.addr (loadAt j+1+1)),by simpa only [List.nil_append,show [op].length=1 by rfl] using compose load br,?_,?_,fit.memory,?_⟩
  · change (if CheckOrdinary.Cond.test (kind j) (u.getReg (operand j)) (u.getReg (rd j)) then _ else _)=_
    rw [left,value];by_cases last : j.val=3
    · have ident : loadAt j+1+1=408:=by simp [loadAt,last]
      simp only [kind,taken,okAt,failAt,last,ite_true,CheckOrdinary.Cond.test,beq_iff_eq,ident]
    · simp only [kind,taken,okAt,failAt,last,ite_false,CheckOrdinary.Cond.test]
      by_cases same : s.getReg (operand j)=s.getMem (point k j) <;> simp [same]
  · intro r h;change u.getReg r=_;apply CheckRecordOps.physical [op] fit (CheckRecordHeader.fits s) r
    simp only [op,List.flatMap_cons,List.flatMap_nil,List.append_nil,CheckRecordOps.dest,List.mem_singleton];unfold rd;split
    · exact h.1
    · exact h.2
  · intro early;change u.getReg .x16=_
    apply Eq.trans _ p;apply CheckRecordOps.physical [op] fit (CheckRecordHeader.fits s) .x16
    simp [op,CheckRecordOps.dest,rd,show j.val ≠ 3 by omega]

end CommitGolfCandidate.Reconstruction.CheckSlotWords
