import WindowFast

namespace C4W5.CompactSGZ
open C4W5.WindowBank
def colHeight (x : Nat) : Nat := (if x < 1073741824 then (if x < 32768 then (if x < 128 then (if x < 8 then (if x < 2 then 0 else (if x < 4 then 1 else 2)) else (if x < 32 then (if x < 16 then 3 else 4) else (if x < 64 then 5 else 6))) else (if x < 2048 then (if x < 512 then (if x < 256 then 7 else 8) else (if x < 1024 then 9 else 10)) else (if x < 8192 then (if x < 4096 then 11 else 12) else (if x < 16384 then 13 else 14)))) else (if x < 4194304 then (if x < 262144 then (if x < 65536 then 15 else (if x < 131072 then 16 else 17)) else (if x < 1048576 then (if x < 524288 then 18 else 19) else (if x < 2097152 then 20 else 21))) else (if x < 67108864 then (if x < 16777216 then (if x < 8388608 then 22 else 23) else (if x < 33554432 then 24 else 25)) else (if x < 268435456 then (if x < 134217728 then 26 else 27) else (if x < 536870912 then 28 else 29))))) else (if x < 35184372088832 then (if x < 137438953472 then (if x < 8589934592 then (if x < 2147483648 then 30 else (if x < 4294967296 then 31 else 32)) else (if x < 34359738368 then (if x < 17179869184 then 33 else 34) else (if x < 68719476736 then 35 else 36))) else (if x < 2199023255552 then (if x < 549755813888 then (if x < 274877906944 then 37 else 38) else (if x < 1099511627776 then 39 else 40)) else (if x < 8796093022208 then (if x < 4398046511104 then 41 else 42) else (if x < 17592186044416 then 43 else 44)))) else (if x < 9007199254740992 then (if x < 562949953421312 then (if x < 140737488355328 then (if x < 70368744177664 then 45 else 46) else (if x < 281474976710656 then 47 else 48)) else (if x < 2251799813685248 then (if x < 1125899906842624 then 49 else 50) else (if x < 4503599627370496 then 51 else 52))) else (if x < 144115188075855872 then (if x < 36028797018963968 then (if x < 18014398509481984 then 53 else 54) else (if x < 72057594037927936 then 55 else 56)) else (if x < 576460752303423488 then (if x < 288230376151711744 then 57 else 58) else (if x < 1152921504606846976 then 59 else 60))))))
def withColumn {α : Sort _} (v : Nat) (f : Nat → Nat → α) : α :=
  force (v+1) fun x => force (colHeight x) fun h => f (x - 2^h) h
def packedPos (w : Nat) : Pos :=
  force (w / 9765625 / 243 / 31) fun k4 =>
  force (k4 / 2305843009213693951) fun k3 =>
  force (k3 / 2305843009213693951) fun k2 =>
  force (k2 / 9007199254740991) fun k1 =>
  force (k1 / 2305843009213693951) fun k0 =>
  withColumn k0 fun b0 h0 =>
  withColumn (k1 % 2305843009213693951) fun b1 h1 =>
  withColumn (k2 % 9007199254740991) fun b2 h2 =>
  withColumn (k3 % 2305843009213693951) fun b3 h3 =>
  withColumn (k4 % 2305843009213693951) fun b4 h4 =>
  ⟨b0,b1,b2,b3,b4,h0,h1,h2,h3,h4⟩
def cw (p : Pos) (c : Nat) : Nat := 2 ^ (p.ht c) - 1 + p.bm c
def packedKey (k : Nat) (p : Pos) (l : Lab5) : Nat := (((((cw p 0 * 2305843009213693951 + cw p 1) * 9007199254740991 + cw p 2) * 2305843009213693951 + cw p 3) * 2305843009213693951 + cw p 4) * 31 + k/2) * 243 + l.l0 + 3*l.l1 + 9*l.l2 + 27*l.l3 + 81*l.l4
def fmt : SZFormat := ⟨1,9765625,packedKey,(fun w => 2*(w / 9765625 / 243 % 31)),packedPos,(fun w => unpackL (w / 9765625 % 243))⟩

end C4W5.CompactSGZ
