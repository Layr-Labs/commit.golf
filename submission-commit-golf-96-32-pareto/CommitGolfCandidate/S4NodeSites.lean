import CommitGolfCandidate.S4FullNodes0
import CommitGolfCandidate.S4FullNodes1
import CommitGolfCandidate.S4FullNodes2
import CommitGolfCandidate.S4FullNodes3
import CommitGolfCandidate.S4FullNodes4
import CommitGolfCandidate.S4FullNodes5
import CommitGolfCandidate.S4BatchNodes0
import CommitGolfCandidate.S4BatchNodes1
import CommitGolfCandidate.S4BatchNodes2
import CommitGolfCandidate.S4BatchNodes3
namespace CommitGolfCandidate.S4.Machine
theorem nodeSite (b : Bool) (h : Nat) (bh : h<pathLevels b) : Matches .check (nodePC b h) (nodeCode b h):=by
  cases b with
  | false=>
    change h<24 at bh
    interval_cases h
    · exact fullNode0
    · exact fullNode1
    · exact fullNode2
    · exact fullNode3
    · exact fullNode4
    · exact fullNode5
    · exact fullNode6
    · exact fullNode7
    · exact fullNode8
    · exact fullNode9
    · exact fullNode10
    · exact fullNode11
    · exact fullNode12
    · exact fullNode13
    · exact fullNode14
    · exact fullNode15
    · exact fullNode16
    · exact fullNode17
    · exact fullNode18
    · exact fullNode19
    · exact fullNode20
    · exact fullNode21
    · exact fullNode22
    · exact fullNode23
  | true=>
    change h<15 at bh
    interval_cases h
    · exact batchNode0
    · exact batchNode1
    · exact batchNode2
    · exact batchNode3
    · exact batchNode4
    · exact batchNode5
    · exact batchNode6
    · exact batchNode7
    · exact batchNode8
    · exact batchNode9
    · exact batchNode10
    · exact batchNode11
    · exact batchNode12
    · exact batchNode13
    · exact batchNode14
end CommitGolfCandidate.S4.Machine
