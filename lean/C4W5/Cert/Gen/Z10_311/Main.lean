import C4W5.CompactZone.Z10_311.Check0
import C4W5.CompactZone.Z10_311.Check1
import C4W5.CompactZone.Z10_311.Check2
import C4W5.CompactZone.Z10_311.Check3
import C4W5.CompactZone.Z10_311.Check4
import C4W5.CompactZone.Z10_311.Check5
import C4W5.CompactZone.Z10_311.Check6
import C4W5.CompactZone.Z10_311.Check7
import C4W5.CompactZone.Z10_311.Check8
import C4W5.CompactZone.Z10_311.Check9
import C4W5.CompactZone.Z10_311.Check10
import C4W5.CompactZone.Z10_311.Check11
import C4W5.CompactZone.Z10_311.Check12
import C4W5.CompactZone.Z10_311.Check13
import C4W5.CompactZone.Z10_311.Check14
import C4W5.CompactZone.Z10_311.Check15
import C4W5.CompactZone.Z10_311.Check16
import C4W5.CompactZone.Z10_311.Check17
import C4W5.CompactZone.Z10_311.Check18
import C4W5.CompactZone.Z10_311.Check19
import C4W5.CompactZone.Z10_311.Check20
import C4W5.CompactZone.Z10_311.Check21
import C4W5.CompactZone.Z10_311.Check22
import C4W5.CompactZone.Z10_311.Check23
import C4W5.CompactZone.Z10_311.Check24
import C4W5.CompactZone.Z10_311.Check25
import C4W5.CompactZone.Z10_311.Check26
import C4W5.CompactZone.Z10_311.Check27
import C4W5.CompactZone.Z10_311.Check28
import C4W5.CompactZone.Z10_311.Check29
import C4W5.CompactZone.Z10_311.Check30
import C4W5.CompactZone.Z10_311.Check31
import C4W5.CompactZone.Z10_311.Check32
import C4W5.CompactZone.Z10_311.Check33
import C4W5.CompactZone.Z10_311.Check34
import C4W5.CompactZone.Z10_311.Check35
import C4W5.CompactZone.Z10_311.Check36
import C4W5.CompactZone.Z10_311.Check37
import C4W5.CompactZone.Z10_311.Check38
import C4W5.CompactZone.Z10_311.Check39
import C4W5.CompactZone.Z10_311.Check40
import C4W5.CompactZone.Z10_311.Check41
import C4W5.CompactZone.Z10_311.Check42
import C4W5.CompactZone.Z10_311.Check43
import C4W5.CompactZone.Z10_311.Check44
import C4W5.CompactZone.Z10_311.Check45
import C4W5.CompactZone.Z10_311.Check46
import C4W5.CompactZone.Z10_311.Check47
import C4W5.CompactZone.Z10_311.Check48
import C4W5.CompactZone.Z10_311.Check49
import C4W5.CompactZone.Z10_311.Check50
import C4W5.CompactZone.Z10_311.Check51
import C4W5.CompactZone.Z10_311.Check52
import C4W5.CompactZone.Z10_311.Check53
import C4W5.CompactZone.Z10_311.Check54
import C4W5.CompactZone.Z10_311.Check55
import C4W5.CompactZone.Z10_311.Check56
import C4W5.CompactZone.Z10_311.Check57
import C4W5.CompactZone.Z10_311.Check58
import C4W5.CompactZone.Z10_311.Check59
import C4W5.CompactZone.Z10_311.Check60
import C4W5.CompactZone.Z10_311.Check61
import C4W5.CompactZone.Z10_311.Check62
import C4W5.CompactZone.Z10_311.Check63
import C4W5.CompactZone.Z10_311.Check64
import C4W5.CompactZone.Z10_311.Check65
import C4W5.CompactZone.Z10_311.Check66
import C4W5.CompactZone.Z10_311.Check67
import C4W5.CompactZone.Z10_311.Check68
import C4W5.CompactZone.Z10_311.Check69

namespace C4W5.Z10_311
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z10_311
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 10 fmt t) t = true :=
  (all_branch (all_branch (all_branch (all_branch (all_branch (all_branch bank0_ok bank1_ok) (all_branch bank2_ok bank3_ok)) (all_branch (all_branch bank4_ok bank5_ok) (all_branch bank6_ok bank7_ok))) (all_branch (all_branch (all_branch bank8_ok bank9_ok) (all_branch bank10_ok bank11_ok)) (all_branch (all_branch bank12_ok bank13_ok) (all_branch bank14_ok (all_branch bank15_ok bank16_ok))))) (all_branch (all_branch (all_branch (all_branch bank17_ok bank18_ok) (all_branch bank19_ok bank20_ok)) (all_branch (all_branch bank21_ok bank22_ok) (all_branch bank23_ok (all_branch bank24_ok bank25_ok)))) (all_branch (all_branch (all_branch bank26_ok bank27_ok) (all_branch bank28_ok bank29_ok)) (all_branch (all_branch bank30_ok bank31_ok) (all_branch bank32_ok (all_branch bank33_ok bank34_ok)))))) (all_branch (all_branch (all_branch (all_branch (all_branch bank35_ok bank36_ok) (all_branch bank37_ok bank38_ok)) (all_branch (all_branch bank39_ok bank40_ok) (all_branch bank41_ok bank42_ok))) (all_branch (all_branch (all_branch bank43_ok bank44_ok) (all_branch bank45_ok bank46_ok)) (all_branch (all_branch bank47_ok bank48_ok) (all_branch bank49_ok (all_branch bank50_ok bank51_ok))))) (all_branch (all_branch (all_branch (all_branch bank52_ok bank53_ok) (all_branch bank54_ok bank55_ok)) (all_branch (all_branch bank56_ok bank57_ok) (all_branch bank58_ok (all_branch bank59_ok bank60_ok)))) (all_branch (all_branch (all_branch bank61_ok bank62_ok) (all_branch bank63_ok bank64_ok)) (all_branch (all_branch bank65_ok bank66_ok) (all_branch bank67_ok (all_branch bank68_ok bank69_ok)))))))

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 10 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 0, 0]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 0, 0] ⟨2,0,1,0,0,2,0,1,0,0⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z10_311.safe

end C4W5.Z10_311
