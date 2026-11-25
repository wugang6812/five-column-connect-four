import C4W5.CompactZone.Z10_G2.Check0
import C4W5.CompactZone.Z10_G2.Check1
import C4W5.CompactZone.Z10_G2.Check2
import C4W5.CompactZone.Z10_G2.Check3
import C4W5.CompactZone.Z10_G2.Check4
import C4W5.CompactZone.Z10_G2.Check5
import C4W5.CompactZone.Z10_G2.Check6
import C4W5.CompactZone.Z10_G2.Check7
import C4W5.CompactZone.Z10_G2.Check8
import C4W5.CompactZone.Z10_G2.Check9
import C4W5.CompactZone.Z10_G2.Check10
import C4W5.CompactZone.Z10_G2.Check11
import C4W5.CompactZone.Z10_G2.Check12

namespace C4W5.Z10_G2
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z10_G2
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 10 fmt t) t = true :=
  (all_branch (all_branch (all_branch bank0_ok (all_branch bank1_ok bank2_ok)) (all_branch bank3_ok (all_branch bank4_ok bank5_ok))) (all_branch (all_branch bank6_ok (all_branch bank7_ok bank8_ok)) (all_branch (all_branch bank9_ok bank10_ok) (all_branch bank11_ok bank12_ok))))

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 10 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 3, 1]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 2, 2, 1, 1, 1, 1, 3, 1] ⟨0,26,5,0,0,0,5,3,1,0⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z10_G2.safe

end C4W5.Z10_G2
