import CommitGolfCandidate.Counting
import CommitGolfCandidate.S5Code
import CommitGolfCandidate.Execution
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem access_ok (base k : Nat) (bound : base+k≤MEMORY_BYTES) (small : base<2^64) (aligned : base%k=0) :
    accessValid (BitVec.ofNat 64 base) k=true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,bound,aligned,decide_true,Bool.true_and]

theorem hash_run (pg : Program) (coins : Bool) (s : MachineState) (fuel : Nat) (src dst : Nat)
    (found : fetch (image pg) s=some (.base .ECALL)) (sel : s.getReg .x5=0)
    (len : s.getReg .x11=96) (kind : s.getReg .x13=0)
    (x : s.getReg .x10=BitVec.ofNat 64 src) (y : s.getReg .x12=BitVec.ofNat 64 dst)
    (rs : src+96≤MEMORY_BYTES) (asrc : src%8=0) (rd : dst+32≤MEMORY_BYTES) (adst : dst%8=0) :
    execute (image pg) (fuel+1) s coins=
      (do let out←Late.hash (readBuffer s src 96); let r←execute (image pg) fuel (writeBits s (BitVec.ofNat 64 dst) out) coins
          return r.charge 8 1) := by
  have xs : src<2^64 := by change src+96≤2^36 at rs;omega
  have ys : dst<2^64 := by change dst+32≤2^36 at rd;omega
  have q : oracleInput s=some (.inl (readBuffer s src 96)) := by
    simp [oracleInput,len,kind,x,y,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,rangeValid,
      Nat.mod_eq_of_lt xs,Nat.mod_eq_of_lt ys,rs,rd,asrc,adst]
    rw [show src%18446744073709551616=src from Nat.mod_eq_of_lt xs,show dst%18446744073709551616=dst from Nat.mod_eq_of_lt ys,kind];simp [rs,rd] <;> rfl
  rw [execute,found,if_pos sel,q]
  simp only [Late.hash,writeOracleAnswer,y,oracleCycles,COMPRESSION_CYCLES];rfl

theorem hash_fixed (pg : Program) (coins : Bool) (o : Oracle) (s : MachineState) (fuel : Nat) (src dst : Nat)
    (found : fetch (image pg) s=some (.base .ECALL)) (sel : s.getReg .x5=0)
    (len : s.getReg .x11=96) (kind : s.getReg .x13=0)
    (x : s.getReg .x10=BitVec.ofNat 64 src) (y : s.getReg .x12=BitVec.ofNat 64 dst)
    (rs : src+96≤MEMORY_BYTES) (asrc : src%8=0) (rd : dst+32≤MEMORY_BYTES) (adst : dst%8=0) :
    o.run (execute (image pg) (fuel+1) s coins)=
      (do let (r,c)←o.run (execute (image pg) fuel (writeBits s (BitVec.ofNat 64 dst) (o.compression (readBuffer s src 96))) coins)
          return (r.charge 8 1,1+c)) := by
  rw [hash_run pg coins s fuel src dst found sel len kind x y rs asrc rd adst]
  unfold Late.hash
  erw [oracle_run_public_bind o (.inl _)]
  simp only [oracle_run_bind,oracle_run_pure,pure_bind,bind_assoc,Nat.add_zero]
  rfl

theorem sd_run {pg : Program} {s : MachineState} {base src : Reg} {imm : BitVec 12} (fuel : Nat) (coins : Bool)
    (found : fetch (image pg) s=some (.base (.SD base src imm)))
    (address : Nat) (toAddr : s.getReg base+signExtend12 imm=BitVec.ofNat 64 address)
    (inside : address+8≤MEMORY_BYTES) (align : address%8=0) :
    execute (image pg) (fuel+1) s coins=
      (do let r←execute (image pg) fuel ((s.setMem (BitVec.ofNat 64 address) (s.getReg src)).setPC (s.pc+4)) coins
          return r.charge 1 0) := by
  have ok:=access_ok address 8 inside (by change address+8≤2^36 at inside;omega) align
  apply execute_ordinary_step (instruction:=.base (.SD base src imm)) <;> try exact found
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,toAddr,ok,cond_true,ite_true]
end CommitGolfCandidate.S5Machine
