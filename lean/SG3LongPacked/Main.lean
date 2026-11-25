import SG3CheckedRoot
import SG3LongPacked.K0
import SG3LongPacked.K1
import SG3LongPacked.K2
import SG3LongPacked.K3
import SG3LongPacked.K4
import SG3LongPacked.K5
import SG3LongPacked.K6
import SG3LongPacked.K7
import SG3LongPacked.K8
import SG3LongPacked.K9
import SG3LongPacked.K10
import SG3LongPacked.K11
import SG3LongPacked.K12
import SG3LongPacked.K13
import SG3LongPacked.K14
import SG3LongPacked.K15
import SG3LongPacked.K16
import SG3LongPacked.K17
import SG3LongPacked.K18
import SG3LongPacked.K19
import SG3LongPacked.K20
import SG3LongPacked.K21
import SG3LongPacked.K22
import SG3LongPacked.K23
import SG3LongPacked.K24
import SG3LongPacked.K25
import SG3LongPacked.K26
import SG3LongPacked.K27
import SG3LongPacked.K28
import SG3LongPacked.K29
import SG3LongPacked.K30
import SG3LongPacked.K31
import SG3LongPacked.K32
import SG3LongPacked.K33
import SG3LongPacked.K34
import SG3LongPacked.K35
import SG3LongPacked.K36
import SG3LongPacked.K37
import SG3LongPacked.K38
import SG3LongPacked.K39
import SG3LongPacked.K40
import SG3LongPacked.K41
import SG3LongPacked.K42
import SG3LongPacked.K43
import SG3LongPacked.K44
import SG3LongPacked.K45
import SG3LongPacked.K46
import SG3LongPacked.K47
import SG3LongPacked.K48
import SG3LongPacked.K49
import SG3LongPacked.K50
import SG3LongPacked.K51
import SG3LongPacked.K52
import SG3LongPacked.K53
import SG3LongPacked.K54
import SG3LongPacked.K55
import SG3LongPacked.K56
import SG3LongPacked.K57
import SG3LongPacked.K58
import SG3LongPacked.K59
import SG3LongPacked.K60
import SG3LongPacked.K61
import SG3LongPacked.K62
import SG3LongPacked.K63
import SG3LongPacked.K64
import SG3LongPacked.K65
import SG3LongPacked.K66
import SG3LongPacked.K67
import SG3LongPacked.K68
import SG3LongPacked.K69
import SG3LongPacked.K70
import SG3LongPacked.K71
import SG3LongPacked.K72
import SG3LongPacked.K73
import SG3LongPacked.K74
import SG3LongPacked.K75
import SG3LongPacked.K76
import SG3LongPacked.K77
import SG3LongPacked.K78
import SG3LongPacked.K79
import SG3LongPacked.K80
import SG3LongPacked.K81
import SG3LongPacked.K82
import SG3LongPacked.K83
import SG3LongPacked.K84
import SG3LongPacked.K85
import SG3LongPacked.K86
import SG3LongPacked.K87
import SG3LongPacked.K88
import SG3LongPacked.K89
import SG3LongPacked.K90
import SG3LongPacked.K91

namespace C4W5.SG3LongPacked
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.WindowBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem n0_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n0 = true := all_branch p0_ok p1_ok
theorem n1_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n1 = true := all_branch p2_ok p3_ok
theorem n2_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n2 = true := all_branch n0_ok n1_ok
theorem n3_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n3 = true := all_branch p4_ok p5_ok
theorem n4_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n4 = true := all_branch p6_ok p7_ok
theorem n5_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n5 = true := all_branch n3_ok n4_ok
theorem n6_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n6 = true := all_branch n2_ok n5_ok
theorem n7_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n7 = true := all_branch p8_ok p9_ok
theorem n8_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n8 = true := all_branch p10_ok p11_ok
theorem n9_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n9 = true := all_branch n7_ok n8_ok
theorem n10_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n10 = true := all_branch p12_ok p13_ok
theorem n11_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n11 = true := all_branch p15_ok p16_ok
theorem n12_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n12 = true := all_branch p14_ok n11_ok
theorem n13_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n13 = true := all_branch n10_ok n12_ok
theorem n14_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n14 = true := all_branch n9_ok n13_ok
theorem n15_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n15 = true := all_branch n6_ok n14_ok
theorem n16_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n16 = true := all_branch p17_ok p18_ok
theorem n17_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n17 = true := all_branch p19_ok p20_ok
theorem n18_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n18 = true := all_branch n16_ok n17_ok
theorem n19_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n19 = true := all_branch p21_ok p22_ok
theorem n20_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n20 = true := all_branch p23_ok p24_ok
theorem n21_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n21 = true := all_branch n19_ok n20_ok
theorem n22_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n22 = true := all_branch n18_ok n21_ok
theorem n23_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n23 = true := all_branch p25_ok p26_ok
theorem n24_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n24 = true := all_branch p27_ok p28_ok
theorem n25_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n25 = true := all_branch n23_ok n24_ok
theorem n26_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n26 = true := all_branch p29_ok p30_ok
theorem n27_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n27 = true := all_branch p32_ok p33_ok
theorem n28_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n28 = true := all_branch p31_ok n27_ok
theorem n29_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n29 = true := all_branch n26_ok n28_ok
theorem n30_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n30 = true := all_branch n25_ok n29_ok
theorem n31_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n31 = true := all_branch n22_ok n30_ok
theorem n32_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n32 = true := all_branch n15_ok n31_ok
theorem n33_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n33 = true := all_branch p34_ok p35_ok
theorem n34_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n34 = true := all_branch p36_ok p37_ok
theorem n35_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n35 = true := all_branch n33_ok n34_ok
theorem n36_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n36 = true := all_branch p38_ok p39_ok
theorem n37_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n37 = true := all_branch p40_ok p41_ok
theorem n38_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n38 = true := all_branch n36_ok n37_ok
theorem n39_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n39 = true := all_branch n35_ok n38_ok
theorem n40_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n40 = true := all_branch p42_ok p43_ok
theorem n41_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n41 = true := all_branch p44_ok p45_ok
theorem n42_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n42 = true := all_branch n40_ok n41_ok
theorem n43_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n43 = true := all_branch p46_ok p47_ok
theorem n44_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n44 = true := all_branch p49_ok p50_ok
theorem n45_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n45 = true := all_branch p48_ok n44_ok
theorem n46_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n46 = true := all_branch n43_ok n45_ok
theorem n47_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n47 = true := all_branch n42_ok n46_ok
theorem n48_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n48 = true := all_branch n39_ok n47_ok
theorem n49_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n49 = true := all_branch p51_ok p52_ok
theorem n50_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n50 = true := all_branch p53_ok p54_ok
theorem n51_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n51 = true := all_branch n49_ok n50_ok
theorem n52_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n52 = true := all_branch p55_ok p56_ok
theorem n53_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n53 = true := all_branch p58_ok p59_ok
theorem n54_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n54 = true := all_branch p57_ok n53_ok
theorem n55_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n55 = true := all_branch n52_ok n54_ok
theorem n56_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n56 = true := all_branch n51_ok n55_ok
theorem n57_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n57 = true := all_branch p60_ok p61_ok
theorem n58_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n58 = true := all_branch p62_ok p63_ok
theorem n59_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n59 = true := all_branch n57_ok n58_ok
theorem n60_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n60 = true := all_branch p64_ok p65_ok
theorem n61_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n61 = true := all_branch p67_ok p68_ok
theorem n62_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n62 = true := all_branch p66_ok n61_ok
theorem n63_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n63 = true := all_branch n60_ok n62_ok
theorem n64_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n64 = true := all_branch n59_ok n63_ok
theorem n65_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n65 = true := all_branch n56_ok n64_ok
theorem n66_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n66 = true := all_branch n48_ok n65_ok
theorem n67_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n67 = true := all_branch n32_ok n66_ok
theorem n68_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n68 = true := all_branch p69_ok p70_ok
theorem n69_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n69 = true := all_branch p71_ok p72_ok
theorem n70_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n70 = true := all_branch n68_ok n69_ok
theorem n71_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n71 = true := all_branch p73_ok p74_ok
theorem n72_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n72 = true := all_branch p75_ok p76_ok
theorem n73_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n73 = true := all_branch n71_ok n72_ok
theorem n74_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n74 = true := all_branch n70_ok n73_ok
theorem n75_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n75 = true := all_branch p77_ok p78_ok
theorem n76_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n76 = true := all_branch p79_ok p80_ok
theorem n77_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n77 = true := all_branch n75_ok n76_ok
theorem n78_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n78 = true := all_branch p81_ok p82_ok
theorem n79_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n79 = true := all_branch p84_ok p85_ok
theorem n80_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n80 = true := all_branch p83_ok n79_ok
theorem n81_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n81 = true := all_branch n78_ok n80_ok
theorem n82_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n82 = true := all_branch n77_ok n81_ok
theorem n83_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n83 = true := all_branch n74_ok n82_ok
theorem n84_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n84 = true := all_branch p86_ok p87_ok
theorem n85_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n85 = true := all_branch p88_ok p89_ok
theorem n86_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n86 = true := all_branch n84_ok n85_ok
theorem n87_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n87 = true := all_branch p90_ok p91_ok
theorem n88_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n88 = true := all_branch p92_ok p93_ok
theorem n89_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n89 = true := all_branch n87_ok n88_ok
theorem n90_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n90 = true := all_branch n86_ok n89_ok
theorem n91_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n91 = true := all_branch p94_ok p95_ok
theorem n92_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n92 = true := all_branch p96_ok p97_ok
theorem n93_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n93 = true := all_branch n91_ok n92_ok
theorem n94_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n94 = true := all_branch p98_ok p99_ok
theorem n95_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n95 = true := all_branch p101_ok p102_ok
theorem n96_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n96 = true := all_branch p100_ok n95_ok
theorem n97_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n97 = true := all_branch n94_ok n96_ok
theorem n98_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n98 = true := all_branch n93_ok n97_ok
theorem n99_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n99 = true := all_branch n90_ok n98_ok
theorem n100_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n100 = true := all_branch n83_ok n99_ok
theorem n101_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n101 = true := all_branch p103_ok p104_ok
theorem n102_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n102 = true := all_branch p105_ok p106_ok
theorem n103_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n103 = true := all_branch n101_ok n102_ok
theorem n104_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n104 = true := all_branch p107_ok p108_ok
theorem n105_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n105 = true := all_branch p109_ok p110_ok
theorem n106_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n106 = true := all_branch n104_ok n105_ok
theorem n107_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n107 = true := all_branch n103_ok n106_ok
theorem n108_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n108 = true := all_branch p111_ok p112_ok
theorem n109_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n109 = true := all_branch p113_ok p114_ok
theorem n110_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n110 = true := all_branch n108_ok n109_ok
theorem n111_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n111 = true := all_branch p115_ok p116_ok
theorem n112_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n112 = true := all_branch p118_ok p119_ok
theorem n113_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n113 = true := all_branch p117_ok n112_ok
theorem n114_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n114 = true := all_branch n111_ok n113_ok
theorem n115_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n115 = true := all_branch n110_ok n114_ok
theorem n116_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n116 = true := all_branch n107_ok n115_ok
theorem n117_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n117 = true := all_branch p120_ok p121_ok
theorem n118_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n118 = true := all_branch p122_ok p123_ok
theorem n119_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n119 = true := all_branch n117_ok n118_ok
theorem n120_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n120 = true := all_branch p124_ok p125_ok
theorem n121_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n121 = true := all_branch p127_ok p128_ok
theorem n122_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n122 = true := all_branch p126_ok n121_ok
theorem n123_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n123 = true := all_branch n120_ok n122_ok
theorem n124_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n124 = true := all_branch n119_ok n123_ok
theorem n125_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n125 = true := all_branch p129_ok p130_ok
theorem n126_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n126 = true := all_branch p131_ok p132_ok
theorem n127_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n127 = true := all_branch n125_ok n126_ok
theorem n128_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n128 = true := all_branch p133_ok p134_ok
theorem n129_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n129 = true := all_branch p136_ok p137_ok
theorem n130_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n130 = true := all_branch p135_ok n129_ok
theorem n131_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n131 = true := all_branch n128_ok n130_ok
theorem n132_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n132 = true := all_branch n127_ok n131_ok
theorem n133_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n133 = true := all_branch n124_ok n132_ok
theorem n134_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n134 = true := all_branch n116_ok n133_ok
theorem n135_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n135 = true := all_branch n100_ok n134_ok
theorem n136_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n136 = true := all_branch n67_ok n135_ok
theorem n137_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n137 = true := all_branch p138_ok p139_ok
theorem n138_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n138 = true := all_branch p140_ok p141_ok
theorem n139_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n139 = true := all_branch n137_ok n138_ok
theorem n140_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n140 = true := all_branch p142_ok p143_ok
theorem n141_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n141 = true := all_branch p144_ok p145_ok
theorem n142_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n142 = true := all_branch n140_ok n141_ok
theorem n143_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n143 = true := all_branch n139_ok n142_ok
theorem n144_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n144 = true := all_branch p146_ok p147_ok
theorem n145_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n145 = true := all_branch p148_ok p149_ok
theorem n146_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n146 = true := all_branch n144_ok n145_ok
theorem n147_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n147 = true := all_branch p150_ok p151_ok
theorem n148_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n148 = true := all_branch p153_ok p154_ok
theorem n149_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n149 = true := all_branch p152_ok n148_ok
theorem n150_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n150 = true := all_branch n147_ok n149_ok
theorem n151_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n151 = true := all_branch n146_ok n150_ok
theorem n152_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n152 = true := all_branch n143_ok n151_ok
theorem n153_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n153 = true := all_branch p155_ok p156_ok
theorem n154_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n154 = true := all_branch p157_ok p158_ok
theorem n155_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n155 = true := all_branch n153_ok n154_ok
theorem n156_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n156 = true := all_branch p159_ok p160_ok
theorem n157_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n157 = true := all_branch p161_ok p162_ok
theorem n158_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n158 = true := all_branch n156_ok n157_ok
theorem n159_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n159 = true := all_branch n155_ok n158_ok
theorem n160_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n160 = true := all_branch p163_ok p164_ok
theorem n161_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n161 = true := all_branch p165_ok p166_ok
theorem n162_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n162 = true := all_branch n160_ok n161_ok
theorem n163_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n163 = true := all_branch p167_ok p168_ok
theorem n164_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n164 = true := all_branch p170_ok p171_ok
theorem n165_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n165 = true := all_branch p169_ok n164_ok
theorem n166_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n166 = true := all_branch n163_ok n165_ok
theorem n167_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n167 = true := all_branch n162_ok n166_ok
theorem n168_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n168 = true := all_branch n159_ok n167_ok
theorem n169_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n169 = true := all_branch n152_ok n168_ok
theorem n170_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n170 = true := all_branch p172_ok p173_ok
theorem n171_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n171 = true := all_branch p174_ok p175_ok
theorem n172_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n172 = true := all_branch n170_ok n171_ok
theorem n173_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n173 = true := all_branch p176_ok p177_ok
theorem n174_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n174 = true := all_branch p178_ok p179_ok
theorem n175_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n175 = true := all_branch n173_ok n174_ok
theorem n176_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n176 = true := all_branch n172_ok n175_ok
theorem n177_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n177 = true := all_branch p180_ok p181_ok
theorem n178_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n178 = true := all_branch p182_ok p183_ok
theorem n179_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n179 = true := all_branch n177_ok n178_ok
theorem n180_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n180 = true := all_branch p184_ok p185_ok
theorem n181_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n181 = true := all_branch p187_ok p188_ok
theorem n182_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n182 = true := all_branch p186_ok n181_ok
theorem n183_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n183 = true := all_branch n180_ok n182_ok
theorem n184_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n184 = true := all_branch n179_ok n183_ok
theorem n185_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n185 = true := all_branch n176_ok n184_ok
theorem n186_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n186 = true := all_branch p189_ok p190_ok
theorem n187_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n187 = true := all_branch p191_ok p192_ok
theorem n188_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n188 = true := all_branch n186_ok n187_ok
theorem n189_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n189 = true := all_branch p193_ok p194_ok
theorem n190_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n190 = true := all_branch p196_ok p197_ok
theorem n191_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n191 = true := all_branch p195_ok n190_ok
theorem n192_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n192 = true := all_branch n189_ok n191_ok
theorem n193_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n193 = true := all_branch n188_ok n192_ok
theorem n194_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n194 = true := all_branch p198_ok p199_ok
theorem n195_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n195 = true := all_branch p200_ok p201_ok
theorem n196_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n196 = true := all_branch n194_ok n195_ok
theorem n197_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n197 = true := all_branch p202_ok p203_ok
theorem n198_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n198 = true := all_branch p205_ok p206_ok
theorem n199_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n199 = true := all_branch p204_ok n198_ok
theorem n200_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n200 = true := all_branch n197_ok n199_ok
theorem n201_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n201 = true := all_branch n196_ok n200_ok
theorem n202_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n202 = true := all_branch n193_ok n201_ok
theorem n203_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n203 = true := all_branch n185_ok n202_ok
theorem n204_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n204 = true := all_branch n169_ok n203_ok
theorem n205_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n205 = true := all_branch p207_ok p208_ok
theorem n206_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n206 = true := all_branch p209_ok p210_ok
theorem n207_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n207 = true := all_branch n205_ok n206_ok
theorem n208_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n208 = true := all_branch p211_ok p212_ok
theorem n209_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n209 = true := all_branch p213_ok p214_ok
theorem n210_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n210 = true := all_branch n208_ok n209_ok
theorem n211_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n211 = true := all_branch n207_ok n210_ok
theorem n212_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n212 = true := all_branch p215_ok p216_ok
theorem n213_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n213 = true := all_branch p217_ok p218_ok
theorem n214_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n214 = true := all_branch n212_ok n213_ok
theorem n215_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n215 = true := all_branch p219_ok p220_ok
theorem n216_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n216 = true := all_branch p222_ok p223_ok
theorem n217_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n217 = true := all_branch p221_ok n216_ok
theorem n218_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n218 = true := all_branch n215_ok n217_ok
theorem n219_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n219 = true := all_branch n214_ok n218_ok
theorem n220_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n220 = true := all_branch n211_ok n219_ok
theorem n221_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n221 = true := all_branch p224_ok p225_ok
theorem n222_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n222 = true := all_branch p226_ok p227_ok
theorem n223_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n223 = true := all_branch n221_ok n222_ok
theorem n224_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n224 = true := all_branch p228_ok p229_ok
theorem n225_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n225 = true := all_branch p230_ok p231_ok
theorem n226_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n226 = true := all_branch n224_ok n225_ok
theorem n227_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n227 = true := all_branch n223_ok n226_ok
theorem n228_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n228 = true := all_branch p232_ok p233_ok
theorem n229_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n229 = true := all_branch p234_ok p235_ok
theorem n230_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n230 = true := all_branch n228_ok n229_ok
theorem n231_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n231 = true := all_branch p236_ok p237_ok
theorem n232_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n232 = true := all_branch p239_ok p240_ok
theorem n233_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n233 = true := all_branch p238_ok n232_ok
theorem n234_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n234 = true := all_branch n231_ok n233_ok
theorem n235_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n235 = true := all_branch n230_ok n234_ok
theorem n236_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n236 = true := all_branch n227_ok n235_ok
theorem n237_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n237 = true := all_branch n220_ok n236_ok
theorem n238_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n238 = true := all_branch p241_ok p242_ok
theorem n239_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n239 = true := all_branch p243_ok p244_ok
theorem n240_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n240 = true := all_branch n238_ok n239_ok
theorem n241_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n241 = true := all_branch p245_ok p246_ok
theorem n242_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n242 = true := all_branch p247_ok p248_ok
theorem n243_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n243 = true := all_branch n241_ok n242_ok
theorem n244_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n244 = true := all_branch n240_ok n243_ok
theorem n245_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n245 = true := all_branch p249_ok p250_ok
theorem n246_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n246 = true := all_branch p251_ok p252_ok
theorem n247_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n247 = true := all_branch n245_ok n246_ok
theorem n248_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n248 = true := all_branch p253_ok p254_ok
theorem n249_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n249 = true := all_branch p256_ok p257_ok
theorem n250_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n250 = true := all_branch p255_ok n249_ok
theorem n251_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n251 = true := all_branch n248_ok n250_ok
theorem n252_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n252 = true := all_branch n247_ok n251_ok
theorem n253_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n253 = true := all_branch n244_ok n252_ok
theorem n254_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n254 = true := all_branch p258_ok p259_ok
theorem n255_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n255 = true := all_branch p260_ok p261_ok
theorem n256_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n256 = true := all_branch n254_ok n255_ok
theorem n257_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n257 = true := all_branch p262_ok p263_ok
theorem n258_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n258 = true := all_branch p265_ok p266_ok
theorem n259_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n259 = true := all_branch p264_ok n258_ok
theorem n260_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n260 = true := all_branch n257_ok n259_ok
theorem n261_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n261 = true := all_branch n256_ok n260_ok
theorem n262_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n262 = true := all_branch p267_ok p268_ok
theorem n263_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n263 = true := all_branch p269_ok p270_ok
theorem n264_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n264 = true := all_branch n262_ok n263_ok
theorem n265_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n265 = true := all_branch p271_ok p272_ok
theorem n266_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n266 = true := all_branch p274_ok p275_ok
theorem n267_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n267 = true := all_branch p273_ok n266_ok
theorem n268_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n268 = true := all_branch n265_ok n267_ok
theorem n269_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n269 = true := all_branch n264_ok n268_ok
theorem n270_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n270 = true := all_branch n261_ok n269_ok
theorem n271_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n271 = true := all_branch n253_ok n270_ok
theorem n272_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n272 = true := all_branch n237_ok n271_ok
theorem n273_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n273 = true := all_branch n204_ok n272_ok
theorem n274_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) n274 = true := all_branch n136_ok n273_ok
theorem checked : all fmt.radix (scheckExtraRow 2 fmt t longGate) t = true := n274_ok
theorem rootEntry : smem fmt t 14 g3p = true := by decide +kernel

/-- Original G(3) family, every even H >= 14. -/
theorem g3_all (m : Nat) (hm : 7 ≤ m) : Safe (2*m) (G 3) :=
  g3_of_extra_window_bank fmt t longGate longGate_sound longGate_lift checked rootEntry m hm
#print axioms g3_all

end C4W5.SG3LongPacked
