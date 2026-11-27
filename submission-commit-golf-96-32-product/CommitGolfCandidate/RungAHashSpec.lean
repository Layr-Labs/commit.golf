import CommitGolfCandidate.RungATypes
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W)
open Late (levelCount pcAt nodeAddress)
structure HashLaw : Prop where
  runHash {o : Oracle} {td ps C s} (g h n p : Nat) (hh:h<4) (hn:n<sizeAt h)
    (real:baseIndex g h+n<levelCount h) (v : View o.compression td ps (frontier C g h n) s)
    (pc:s.pc=pcAt p) (enc:hashSite p h)
    (mode:s.getReg .x5=0) (width:s.getReg .x11=96) (kind:s.getReg .x13=0)
    (inPtr:s.getReg .x10=W (inputAddr h (baseIndex g h+n))) (outPtr:s.getReg .x12=W (nodeAddress h (baseIndex g h+n))) :
    ∃ t,DetRun o image s (hashLength h) t (hashCycles h) 1 ∧ t.pc=pcAt (p+hashLength h) ∧
      (∀ r,t.getReg r=s.getReg r) ∧ View o.compression td ps (frontier C g h (n+1)) t
end CommitGolfCandidate.RungA
