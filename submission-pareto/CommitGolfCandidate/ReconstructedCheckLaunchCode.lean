import CommitGolfCandidate.ReconstructedCheckEpilogue
import CommitGolfCandidate.ReconstructedCheckRecordABI

namespace CommitGolfCandidate.Reconstruction.CheckLaunchCode
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckParentRun CheckLink CommitBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def firstCode : List Op := [.plain (.basic (.arith (.addi .x2 .x2 2064))),
  .plain (.basic (.sd .x2 .x1 2024)),
  .plain (.basic (.sd .x2 .x8 2016)),
  .plain (.basic (.sd .x2 .x9 2008)),
  .plain (.basic (.sd .x2 .x18 2000)),
  .plain (.basic (.sd .x2 .x19 1992)),
  .plain (.basic (.sd .x2 .x20 1984)),
  .plain (.basic (.sd .x2 .x21 1976)),
  .plain (.basic (.sd .x2 .x22 1968)),
  .plain (.basic (.sd .x2 .x23 1960)),
  .plain (.basic (.sd .x2 .x24 1952)),
  .plain (.basic (.sd .x2 .x25 1944)),
  .plain (.basic (.sd .x2 .x26 1936)),
  .plain (.basic (.sd .x2 .x27 1928)),
  .plain (.basic (.arith (.addi .x8 .x2 2032))),
  .plain (.basic (.arith (.addi .x2 .x2 3696))),
  .plain (.basic (.arith (.lui .x12 1))),
  .plain (.basic (.arith (.addiw .x12 .x12 3633))),
  .plain (.basic (.arith (.lui .x13 1))),
  .plain (.subPtr .x13 .x8 .x13),
  .plain (.basic (.sd .x13 .x12 1712))]
def middleCode : List Op := [.plain (.basic (.arith (.lui .x13 1))),
  .plain (.subPtr .x13 .x8 .x13),
  .plain (.basic (.sd .x13 .x11 1672))]
def lastCode : List Op := [.plain (.basic (.arith (.addi .x17 .x0 0))),
  .plain (.basic (.arith (.addi .x24 .x0 0))),
  .plain (.basic (.arith (.addi .x10 .x0 4095))),
  .plain (.basic (.arith (.srli .x10 .x10 32))),
  .plain (.basic (.arith (.lui .x11 1))),
  .plain (.subPtr .x11 .x8 .x11),
  .plain (.basic (.sd .x11 .x10 1728)),
  .plain (.basic (.arith (.addi .x6 .x8 2048))),
  .plain (.basic (.arith (.addi .x6 .x6 3816))),
  .plain (.basic (.arith (.addi .x7 .x8 2048))),
  .plain (.basic (.arith (.addi .x7 .x7 4072))),
  .plain (.basic (.arith (.lui .x10 45056))),
  .plain (.basic (.arith (.addiw .x10 .x10 129))),
  .plain (.basic (.arith (.slli .x10 .x10 5))),
  .plain (.basic (.arith (.lui .x11 1))),
  .plain (.subPtr .x11 .x8 .x11),
  .plain (.basic (.sd .x11 .x10 1704)),
  .plain (.basic (.arith (.lui .x10 78848))),
  .plain (.basic (.arith (.addiw .x19 .x10 131))),
  .plain (.basic (.arith (.slli .x19 .x19 5))),
  .plain (.basic (.arith (.lui .x10 46080))),
  .plain (.basic (.arith (.addiw .x10 .x10 131))),
  .plain (.basic (.arith (.slli .x10 .x10 5))),
  .plain (.basic (.arith (.lui .x11 1))),
  .plain (.subPtr .x11 .x8 .x11),
  .plain (.basic (.sd .x11 .x10 1696)),
  .plain (.basic (.arith (.lui .x10 512))),
  .plain (.basic (.arith (.addi .x10 .x10 8))),
  .plain (.basic (.arith (.addi .x10 .x10 192))),
  .plain (.basic (.arith (.lui .x11 1))),
  .plain (.subPtr .x11 .x8 .x11),
  .plain (.basic (.sd .x11 .x10 1688)),
  .plain (.basic (.arith (.lui .x10 1))),
  .plain (.subPtr .x10 .x8 .x10),
  .plain (.basic (.sd .x10 .x5 1680)),
  .plain (.basic (.jal .x0 56))]

def tab:=CheckRegion.tab 2432
def start : State where
  pc:=addr 29
  regs:=fun r=>match r with | .x1=>.lit (addr 20) | .x2=>ptr 1 2432 | .x10=>.lit (-1) | _=>.reg r
  writes:=[]

def firstRun:=run tab (addr 29) firstCode start
def first:=firstRun.getD start
def sized : State:={first.set .x12 (.answer 0 0) with pc:=addr 53}
def midRun:=run tab (addr 53) middleCode sized
def mid:=midRun.getD sized
def ready : State:={mid with pc:=addr 73}
def endRun:=run tab (addr 73) lastCode ready
def done:=endRun.getD ready

private theorem replay (r : Option State) (s : State) (good : r.isSome=true) : r=some (r.getD s) := by cases r <;> simp_all
theorem first_ok : firstRun=some first := replay firstRun start (by decide +kernel)
theorem mid_ok : midRun=some mid := replay midRun sized (by decide +kernel)
theorem end_ok : endRun=some done := replay endRun ready (by decide +kernel)

theorem entryFacts : first.pc=addr 50 ∧ first.get .x5=.reg .x5 ∧ first.get .x12=.lit 3633 := by decide +kernel

theorem middleFacts : mid.pc=addr 56 ∧ mid.get .x12=.answer 0 0 ∧ mid.get .x11=.reg .x11 ∧
    mid.get .x2=ptr 1 0 ∧ mid.get .x10=.lit (-1) ∧ look tab (loc 1 2424) mid.writes=.lit (addr 20) := by decide +kernel

def slots : List (Nat×Term) := [(8,.reg .x11),(16,.reg .x5),(24,.lit 2097352),
  (32,.lit 6039801952),(40,.lit 5905584160),(48,.lit 3633),(64,.lit 0xffffffff),(2424,.lit (addr 20))]

def registers : List (Reg×Term):=[
  (.x2,ptr 1 0),(.x8,ptr 1 2432),(.x17,.lit 0),(.x24,.lit 0),(.x19,.lit 10334769248),
  (.x6,ptr 1 104),(.x7,ptr 1 360),(.x5,.reg .x5)]

theorem doneFacts : done.pc=addr 122 ∧
    (∀ kv∈registers,done.get kv.1=kv.2) ∧
    (∀ kv∈slots,look tab (loc 1 kv.1) done.writes=kv.2 ∧ tab.allowed (loc 1 kv.1)=true) := by decide +kernel

theorem decodedFirst : Decoded firstCode (addr 29):=CheckDecode.sound _ _ (by decide +kernel)
theorem decodedMiddle : Decoded middleCode (addr 53):=CheckDecode.sound _ _ (by decide +kernel)
theorem decodedLast : Decoded lastCode (addr 73):=CheckDecode.sound _ _ (by decide +kernel)

end CommitGolfCandidate.Reconstruction.CheckLaunchCode

