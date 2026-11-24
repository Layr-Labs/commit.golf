import CommitGolfCandidate.CapBFlow
import CommitGolfCandidate.CapBWalk
import CommitGolfCandidate.CapBRaw
import CommitGolfCandidate.Layout2Views
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (flushBytes flushPrice)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
def slotWord (p : Nat) := 6680+8*p
def flushCore : Nat → List Instr
  | 2=>[.SH .x21 .x22 0,.ADDI .x21 .x21 2]
  | 4=>[.SW .x21 .x22 0,.ADDI .x21 .x21 4]
  | 6=>[.SW .x21 .x22 0,.SRLI .x22 .x22 32,.SH .x21 .x22 4,.ADDI .x21 .x21 6]
  | 8=>[.SD .x21 .x22 0,.ADDI .x21 .x21 8]
  | _=>[]
def flushOps (p : Nat) :=
  let rs:=flushCore (flushBytes p)
  rs++[Instr.JAL .x0 (jalOffset (slotWord p+rs.length) 6662)]
theorem flushCode : ∀ p : Fin 32,Slice openingImage (slotWord p.val) (flushOps p.val) := by decide +kernel
theorem flushTargets : ∀ p : Fin 32,
    (((32768#64+((pc (startHandler p.val)-pc 6144) >>> (1:Nat)))+signExtend12 2144) &&& ~~~1#64)=pc (slotWord p.val) ∧
    (pc (startHandler p.val)=pc 6144 ↔ p.val=0) ∧
    (let w:=slotWord p.val+(flushCore (flushBytes p.val)).length;pc w+signExtend21 (jalOffset w 6662)=pc 6662) ∧
    (p.val≠0 → flushBytes p.val=2 ∨ flushBytes p.val=4 ∨ flushBytes p.val=6 ∨ flushBytes p.val=8) := by decide +kernel

def patch (n : Nat) (old new : Word) : Word :=
  match n with
  | 2=>replaceHalfword old 0 (new.truncate 16)
  | 4=>replaceWord32 old 0 (new.truncate 32)
  | 6=>replaceHalfword (replaceWord32 old 0 (new.truncate 32)) 2 ((new >>> 32).truncate 16)
  | 8=>new
  | _=>old

/-- A byte of the one dword touched by a phase's final store sequence. -/
theorem patch_byte (n : Nat) (kind : n=2 ∨ n=4 ∨ n=6 ∨ n=8) (old new : Word) (j : Nat) (small : j<8) :
    extractByte (patch n old new) j=(if j<n then extractByte new j else extractByte old j) := by
  rcases kind with rfl | rfl | rfl | rfl <;> interval_cases j <;>
    simp (config := {decide := true}) [patch,extractByte,replaceHalfword,replaceWord32] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;> simp

theorem flushWrites {s t : MachineState} {B n : Nat} {v : Word} (kind : n=2 ∨ n=4 ∨ n=6 ∨ n=8)
    (alg : B%8=0) (room : B+8≤MEMORY_BYTES)
    (mem : t.mem=(s.setMem (addr B) (patch n (gword s B) v)).mem) :
    Layout2.Writes s t B n (extractByte v) := by
  intro q hq
  have lim : MEMORY_BYTES<2^64 := by decide
  change extractByte (t.getMem (alignToDword (addr q))) (byteOffset (addr q))=_
  rw [show t.getMem (alignToDword (addr q))=(s.setMem (addr B) (patch n (gword s B) v)).getMem (alignToDword (addr q)) from congrFun mem _,offset_nat _ (by omega)]
  by_cases atB : alignToDword (addr q)=addr B
  · rw [atB,MachineState.getMem_setMem_eq,patch_byte _ kind _ _ _ (by omega)]
    have a:=congrArg BitVec.toNat atB;rw [align_nat _ (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show B<2^64 by omega)] at a
    have eq : q=B+q%8 := by omega
    have old:=byte_at s B (q%8) alg (by omega) (by omega)
    rw [←eq] at old
    change _=if B≤q ∧ q<B+n then _ else s.getByte (addr q)
    rw [old];split_ifs <;> first | omega | (congr 1 <;> omega) | rfl
  · rw [MachineState.getMem_setMem_ne atB]
    have away : ¬(B≤q ∧ q<B+n) := by
      intro h;apply atB;rw [align_eq q (by omega)];congr 1;rcases kind with rfl|rfl|rfl|rfl <;> omega
    rw [if_neg away];change _=extractByte _ (byteOffset (addr q));rw [offset_nat _ (by omega)]
attribute [local simp] Layout2.mem_pc Layout2.mem_reg Layout2.pc_pc MachineState.getReg_setPC TwoPermutationPrototype.Opening.getReg_setReg
private theorem mem_twice (s : MachineState) (a v u : Word) : ((s.setMem a v).setMem a u).mem=(s.setMem a u).mem := by
  funext k;change ((s.setMem a v).setMem a u).getMem k=(s.setMem a u).getMem k
  by_cases same : k=a
  · subst k;simp only [MachineState.getMem_setMem_eq]
  · simp only [MachineState.getMem_setMem_ne same]

theorem core2 (s : MachineState) (w B : Nat) (v : Word) (here : s.pc=pc w) (small : w<7000)
    (dest : s.getReg .x21=addr B) (carry : s.getReg .x22=v) (alg : B%8=0) (room : B+8≤MEMORY_BYTES)
    (code : CodeAt openingImage w (flushCore 2)) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=pc (w+2) ∧ t.getReg .x21=addr (B+2) ∧
      t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      t.mem=(s.setMem (addr B) (patch 2 (gword s B) v)).mem := by
  have fit : B+8<2^64 := by unfold MEMORY_BYTES at room;omega
  have al : alignToDword (addr B)=addr B := by rw [align_eq _ (by omega),alg,Nat.sub_zero]
  have off : byteOffset (addr B)=0 := (offset_nat _ (by omega)).trans alg
  have al4 : alignToDword (addr (B+4))=addr B := by rw [align_eq _ (by omega)];congr 1;omega
  have off4 : byteOffset (addr (B+4))=4 := by rw [offset_nat _ (by omega)];omega
  let s1:=execInstrBr s (.SH .x21 .x22 0)
  have ins0 : (openingImage.code[(w+0)]?).bind decodeInstruction=some (.base (.SH .x21 .x22 0)) := code ⟨0,by decide⟩
  have ok0 : ordinaryStep s (.base (.SH .x21 .x22 0))=some s1 := by
    have valid:=access_ok B 2 (by omega) (by omega)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,add_addr,valid]
  have r0 : Run openingImage s s1 1 1 := one (by omega) here ins0 ok0
  have p0 : s1.pc=pc (w+1) := (congrArg (fun a : Word=>a+4) here).trans (pc_add _)
  let s2:=execInstrBr s1 (.ADDI .x21 .x21 2)
  have ins1 : (openingImage.code[(w+1)]?).bind decodeInstruction=some (.base (.ADDI .x21 .x21 2)) := code ⟨1,by decide⟩
  have ok1 : ordinaryStep s1 (.base (.ADDI .x21 .x21 2))=some s2 := rfl
  have r1 : Run openingImage s1 s2 1 1 := one (by omega) p0 ins1 ok1
  have p1 : s2.pc=pc (w+2) := (congrArg (fun a : Word=>a+4) p0).trans (pc_add _)
  refine ⟨_,(r0.thenDo r1),p1,?_,?_,?_,?_⟩
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (2#64)=addr 2 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (2#64)=addr 2 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (2#64)=addr 2 from rfl,add_addr]
  · funext q;change s2.getMem q=(s.setMem (addr B) _).getMem q
    by_cases eq : q=addr B <;> simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (2#64)=addr 2 from rfl,add_addr,eq,MachineState.getMem_setPC,MachineState.getMem_setReg,MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem core4 (s : MachineState) (w B : Nat) (v : Word) (here : s.pc=pc w) (small : w<7000)
    (dest : s.getReg .x21=addr B) (carry : s.getReg .x22=v) (alg : B%8=0) (room : B+8≤MEMORY_BYTES)
    (code : CodeAt openingImage w (flushCore 4)) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=pc (w+2) ∧ t.getReg .x21=addr (B+4) ∧
      t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      t.mem=(s.setMem (addr B) (patch 4 (gword s B) v)).mem := by
  have fit : B+8<2^64 := by unfold MEMORY_BYTES at room;omega
  have al : alignToDword (addr B)=addr B := by rw [align_eq _ (by omega),alg,Nat.sub_zero]
  have off : byteOffset (addr B)=0 := (offset_nat _ (by omega)).trans alg
  have al4 : alignToDword (addr (B+4))=addr B := by rw [align_eq _ (by omega)];congr 1;omega
  have off4 : byteOffset (addr (B+4))=4 := by rw [offset_nat _ (by omega)];omega
  let s1:=execInstrBr s (.SW .x21 .x22 0)
  have ins0 : (openingImage.code[(w+0)]?).bind decodeInstruction=some (.base (.SW .x21 .x22 0)) := code ⟨0,by decide⟩
  have ok0 : ordinaryStep s (.base (.SW .x21 .x22 0))=some s1 := by
    have valid:=access_ok B 4 (by omega) (by omega)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,add_addr,valid]
  have r0 : Run openingImage s s1 1 1 := one (by omega) here ins0 ok0
  have p0 : s1.pc=pc (w+1) := (congrArg (fun a : Word=>a+4) here).trans (pc_add _)
  let s2:=execInstrBr s1 (.ADDI .x21 .x21 4)
  have ins1 : (openingImage.code[(w+1)]?).bind decodeInstruction=some (.base (.ADDI .x21 .x21 4)) := code ⟨1,by decide⟩
  have ok1 : ordinaryStep s1 (.base (.ADDI .x21 .x21 4))=some s2 := rfl
  have r1 : Run openingImage s1 s2 1 1 := one (by omega) p0 ins1 ok1
  have p1 : s2.pc=pc (w+2) := (congrArg (fun a : Word=>a+4) p0).trans (pc_add _)
  refine ⟨_,(r0.thenDo r1),p1,?_,?_,?_,?_⟩
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (4#64)=addr 4 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (4#64)=addr 4 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (4#64)=addr 4 from rfl,add_addr]
  · funext q;change s2.getMem q=(s.setMem (addr B) _).getMem q
    by_cases eq : q=addr B <;> simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (4#64)=addr 4 from rfl,add_addr,eq,MachineState.getMem_setPC,MachineState.getMem_setReg,MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem core6 (s : MachineState) (w B : Nat) (v : Word) (here : s.pc=pc w) (small : w<7000)
    (dest : s.getReg .x21=addr B) (carry : s.getReg .x22=v) (alg : B%8=0) (room : B+8≤MEMORY_BYTES)
    (code : CodeAt openingImage w (flushCore 6)) :
    ∃ t, Run openingImage s t 4 4 ∧ t.pc=pc (w+4) ∧ t.getReg .x21=addr (B+6) ∧
      t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      t.mem=(s.setMem (addr B) (patch 6 (gword s B) v)).mem := by
  have fit : B+8<2^64 := by unfold MEMORY_BYTES at room;omega
  have al : alignToDword (addr B)=addr B := by rw [align_eq _ (by omega),alg,Nat.sub_zero]
  have off : byteOffset (addr B)=0 := (offset_nat _ (by omega)).trans alg
  have al4 : alignToDword (addr (B+4))=addr B := by rw [align_eq _ (by omega)];congr 1;omega
  have off4 : byteOffset (addr (B+4))=4 := by rw [offset_nat _ (by omega)];omega
  let s1:=execInstrBr s (.SW .x21 .x22 0)
  have ins0 : (openingImage.code[(w+0)]?).bind decodeInstruction=some (.base (.SW .x21 .x22 0)) := code ⟨0,by decide⟩
  have ok0 : ordinaryStep s (.base (.SW .x21 .x22 0))=some s1 := by
    have valid:=access_ok B 4 (by omega) (by omega)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,add_addr,valid]
  have r0 : Run openingImage s s1 1 1 := one (by omega) here ins0 ok0
  have p0 : s1.pc=pc (w+1) := (congrArg (fun a : Word=>a+4) here).trans (pc_add _)
  let s2:=execInstrBr s1 (.SRLI .x22 .x22 32)
  have ins1 : (openingImage.code[(w+1)]?).bind decodeInstruction=some (.base (.SRLI .x22 .x22 32)) := code ⟨1,by decide⟩
  have ok1 : ordinaryStep s1 (.base (.SRLI .x22 .x22 32))=some s2 := rfl
  have r1 : Run openingImage s1 s2 1 1 := one (by omega) p0 ins1 ok1
  have p1 : s2.pc=pc (w+2) := (congrArg (fun a : Word=>a+4) p0).trans (pc_add _)
  let s3:=execInstrBr s2 (.SH .x21 .x22 4)
  have ins2 : (openingImage.code[(w+2)]?).bind decodeInstruction=some (.base (.SH .x21 .x22 4)) := code ⟨2,by decide⟩
  have ok2 : ordinaryStep s2 (.base (.SH .x21 .x22 4))=some s3 := by
    have valid:=access_ok (B+4) 2 (by omega) (by omega)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,s3,s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,add_addr,valid]
  have r2 : Run openingImage s2 s3 1 1 := one (by omega) p1 ins2 ok2
  have p2 : s3.pc=pc (w+3) := (congrArg (fun a : Word=>a+4) p1).trans (pc_add _)
  let s4:=execInstrBr s3 (.ADDI .x21 .x21 6)
  have ins3 : (openingImage.code[(w+3)]?).bind decodeInstruction=some (.base (.ADDI .x21 .x21 6)) := code ⟨3,by decide⟩
  have ok3 : ordinaryStep s3 (.base (.ADDI .x21 .x21 6))=some s4 := rfl
  have r3 : Run openingImage s3 s4 1 1 := one (by omega) p2 ins3 ok3
  have p3 : s4.pc=pc (w+4) := (congrArg (fun a : Word=>a+4) p2).trans (pc_add _)
  refine ⟨_,(((r0.thenDo r1).thenDo r2).thenDo r3),p3,?_,?_,?_,?_⟩
  · simp [s4,s3,s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (6#64)=addr 6 from rfl,add_addr]
  · simp [s4,s3,s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (6#64)=addr 6 from rfl,add_addr]
  · simp [s4,s3,s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (6#64)=addr 6 from rfl,add_addr]
  · funext q;change s4.getMem q=(s.setMem (addr B) _).getMem q
    by_cases eq : q=addr B <;> simp [s4,s3,s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (6#64)=addr 6 from rfl,add_addr,eq,MachineState.getMem_setPC,MachineState.getMem_setReg,MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem core8 (s : MachineState) (w B : Nat) (v : Word) (here : s.pc=pc w) (small : w<7000)
    (dest : s.getReg .x21=addr B) (carry : s.getReg .x22=v) (alg : B%8=0) (room : B+8≤MEMORY_BYTES)
    (code : CodeAt openingImage w (flushCore 8)) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=pc (w+2) ∧ t.getReg .x21=addr (B+8) ∧
      t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      t.mem=(s.setMem (addr B) (patch 8 (gword s B) v)).mem := by
  have fit : B+8<2^64 := by unfold MEMORY_BYTES at room;omega
  have al : alignToDword (addr B)=addr B := by rw [align_eq _ (by omega),alg,Nat.sub_zero]
  have off : byteOffset (addr B)=0 := (offset_nat _ (by omega)).trans alg
  have al4 : alignToDword (addr (B+4))=addr B := by rw [align_eq _ (by omega)];congr 1;omega
  have off4 : byteOffset (addr (B+4))=4 := by rw [offset_nat _ (by omega)];omega
  let s1:=execInstrBr s (.SD .x21 .x22 0)
  have ins0 : (openingImage.code[(w+0)]?).bind decodeInstruction=some (.base (.SD .x21 .x22 0)) := code ⟨0,by decide⟩
  have ok0 : ordinaryStep s (.base (.SD .x21 .x22 0))=some s1 := by
    have valid:=access_ok B 8 (by omega) (by omega)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,add_addr,valid]
  have r0 : Run openingImage s s1 1 1 := one (by omega) here ins0 ok0
  have p0 : s1.pc=pc (w+1) := (congrArg (fun a : Word=>a+4) here).trans (pc_add _)
  let s2:=execInstrBr s1 (.ADDI .x21 .x21 8)
  have ins1 : (openingImage.code[(w+1)]?).bind decodeInstruction=some (.base (.ADDI .x21 .x21 8)) := code ⟨1,by decide⟩
  have ok1 : ordinaryStep s1 (.base (.ADDI .x21 .x21 8))=some s2 := rfl
  have r1 : Run openingImage s1 s2 1 1 := one (by omega) p0 ins1 ok1
  have p1 : s2.pc=pc (w+2) := (congrArg (fun a : Word=>a+4) p0).trans (pc_add _)
  refine ⟨_,(r0.thenDo r1),p1,?_,?_,?_,?_⟩
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (8#64)=addr 8 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (8#64)=addr 8 from rfl,add_addr]
  · simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (8#64)=addr 8 from rfl,add_addr]
  · funext q;change s2.getMem q=(s.setMem (addr B) _).getMem q
    by_cases eq : q=addr B <;> simp [s2,s1,execInstrBr,MachineState.setHalfword,MachineState.setWord32,TwoPermutationPrototype.Opening.getReg_setMem,dest,carry,al,off,al4,off4,Layout2.mem_pc,Layout2.mem_reg,gword,patch,signExtend12,BitVec.add_zero,show (4#64)=addr 4 from rfl,show (8#64)=addr 8 from rfl,add_addr,eq,MachineState.getMem_setPC,MachineState.getMem_setReg,MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
end CommitGolfCandidate.CapB
