import C4W5.CompactZone.Z10_U.Check0
import C4W5.CompactZone.Z10_U.Check1
import C4W5.CompactZone.Z10_U.Check2
import C4W5.CompactZone.Z10_U.Check3
import C4W5.CompactZone.Z10_U.Check4
import C4W5.CompactZone.Z10_U.Check5
import C4W5.CompactZone.Z10_U.Check6
import C4W5.CompactZone.Z10_U.Check7
import C4W5.CompactZone.Z10_U.Check8
import C4W5.CompactZone.Z10_U.Check9
import C4W5.CompactZone.Z10_U.Check10
import C4W5.CompactZone.Z10_U.Check11
import C4W5.CompactZone.Z10_U.Check12
import C4W5.CompactZone.Z10_U.Check13
import C4W5.CompactZone.Z10_U.Check14
import C4W5.CompactZone.Z10_U.Check15
import C4W5.CompactZone.Z10_U.Check16
import C4W5.CompactZone.Z10_U.Check17
import C4W5.CompactZone.Z10_U.Check18
import C4W5.CompactZone.Z10_U.Check19
import C4W5.CompactZone.Z10_U.Check20
import C4W5.CompactZone.Z10_U.Check21
import C4W5.CompactZone.Z10_U.Check22
import C4W5.CompactZone.Z10_U.Check23
import C4W5.CompactZone.Z10_U.Check24
import C4W5.CompactZone.Z10_U.Check25
import C4W5.CompactZone.Z10_U.Check26
import C4W5.CompactZone.Z10_U.Check27
import C4W5.CompactZone.Z10_U.Check28
import C4W5.CompactZone.Z10_U.Check29
import C4W5.CompactZone.Z10_U.Check30
import C4W5.CompactZone.Z10_U.Check31
import C4W5.CompactZone.Z10_U.Check32
import C4W5.CompactZone.Z10_U.Check33
import C4W5.CompactZone.Z10_U.Check34
import C4W5.CompactZone.Z10_U.Check35
import C4W5.CompactZone.Z10_U.Check36
import C4W5.CompactZone.Z10_U.Check37
import C4W5.CompactZone.Z10_U.Check38
import C4W5.CompactZone.Z10_U.Check39
import C4W5.CompactZone.Z10_U.Check40
import C4W5.CompactZone.Z10_U.Check41
import C4W5.CompactZone.Z10_U.Check42
import C4W5.CompactZone.Z10_U.Check43
import C4W5.CompactZone.Z10_U.Check44
import C4W5.CompactZone.Z10_U.Check45
import C4W5.CompactZone.Z10_U.Check46
import C4W5.CompactZone.Z10_U.Check47
import C4W5.CompactZone.Z10_U.Check48
import C4W5.CompactZone.Z10_U.Check49
import C4W5.CompactZone.Z10_U.Check50
import C4W5.CompactZone.Z10_U.Check51
import C4W5.CompactZone.Z10_U.Check52
import C4W5.CompactZone.Z10_U.Check53
import C4W5.CompactZone.Z10_U.Check54
import C4W5.CompactZone.Z10_U.Check55

namespace C4W5.Z10_U
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z10_U
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 10 fmt t) t = true :=
  (all_branch (all_branch (all_branch (all_branch (all_branch bank0_ok (all_branch bank1_ok bank2_ok)) (all_branch (all_branch bank3_ok bank4_ok) (all_branch bank5_ok bank6_ok))) (all_branch (all_branch bank7_ok (all_branch bank8_ok bank9_ok)) (all_branch (all_branch bank10_ok bank11_ok) (all_branch bank12_ok bank13_ok)))) (all_branch (all_branch (all_branch bank14_ok (all_branch bank15_ok bank16_ok)) (all_branch (all_branch bank17_ok bank18_ok) (all_branch bank19_ok bank20_ok))) (all_branch (all_branch bank21_ok (all_branch bank22_ok bank23_ok)) (all_branch (all_branch bank24_ok bank25_ok) (all_branch bank26_ok bank27_ok))))) (all_branch (all_branch (all_branch (all_branch bank28_ok (all_branch bank29_ok bank30_ok)) (all_branch (all_branch bank31_ok bank32_ok) (all_branch bank33_ok bank34_ok))) (all_branch (all_branch bank35_ok (all_branch bank36_ok bank37_ok)) (all_branch (all_branch bank38_ok bank39_ok) (all_branch bank40_ok bank41_ok)))) (all_branch (all_branch (all_branch bank42_ok (all_branch bank43_ok bank44_ok)) (all_branch (all_branch bank45_ok bank46_ok) (all_branch bank47_ok bank48_ok))) (all_branch (all_branch bank49_ok (all_branch bank50_ok bank51_ok)) (all_branch (all_branch bank52_ok bank53_ok) (all_branch bank54_ok bank55_ok))))))

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 10 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 2, 2, 2, 1]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 2, 2, 2, 1] ⟨0,1,5,0,0,0,1,4,0,0⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z10_U.safe

end C4W5.Z10_U
