import WindowStretch

namespace C4W5.STopLongPacked
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.WindowBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def colHeight (x : Nat) : Nat := (if x < 67108864 then (if x < 8192 then (if x < 64 then (if x < 8 then (if x < 2 then 0 else (if x < 4 then 1 else 2)) else (if x < 16 then 3 else (if x < 32 then 4 else 5))) else (if x < 512 then (if x < 128 then 6 else (if x < 256 then 7 else 8)) else (if x < 2048 then (if x < 1024 then 9 else 10) else (if x < 4096 then 11 else 12)))) else (if x < 524288 then (if x < 65536 then (if x < 16384 then 13 else (if x < 32768 then 14 else 15)) else (if x < 131072 then 16 else (if x < 262144 then 17 else 18))) else (if x < 4194304 then (if x < 1048576 then 19 else (if x < 2097152 then 20 else 21)) else (if x < 16777216 then (if x < 8388608 then 22 else 23) else (if x < 33554432 then 24 else 25))))) else (if x < 549755813888 then (if x < 4294967296 then (if x < 536870912 then (if x < 134217728 then 26 else (if x < 268435456 then 27 else 28)) else (if x < 1073741824 then 29 else (if x < 2147483648 then 30 else 31))) else (if x < 34359738368 then (if x < 8589934592 then 32 else (if x < 17179869184 then 33 else 34)) else (if x < 137438953472 then (if x < 68719476736 then 35 else 36) else (if x < 274877906944 then 37 else 38)))) else (if x < 70368744177664 then (if x < 4398046511104 then (if x < 1099511627776 then 39 else (if x < 2199023255552 then 40 else 41)) else (if x < 17592186044416 then (if x < 8796093022208 then 42 else 43) else (if x < 35184372088832 then 44 else 45))) else (if x < 562949953421312 then (if x < 140737488355328 then 46 else (if x < 281474976710656 then 47 else 48)) else (if x < 2251799813685248 then (if x < 1125899906842624 then 49 else 50) else (if x < 4503599627370496 then 51 else 52))))))
def withColumn {α : Sort _} (v : Nat) (f : Nat → Nat → α) : α :=
  force (v+1) fun x => force (colHeight x) fun h => f (x - 2^h) h
def packedPos (w : Nat) : Pos :=
  force (w / 9765625 / 27) fun k4 =>
  force (k4 / 35184372088831) fun k3 =>
  force (k3 / 35184372088831) fun k2 =>
  force (k2 / 8796093022207) fun k1 =>
  force (k1 / 9007199254740991) fun k0 =>
  withColumn k0 fun b0 h0 =>
  withColumn (k1 % 9007199254740991) fun b1 h1 =>
  withColumn (k2 % 8796093022207) fun b2 h2 =>
  withColumn (k3 % 35184372088831) fun b3 h3 =>
  withColumn (k4 % 35184372088831) fun b4 h4 =>
  ⟨b0,b1,b2,b3,b4,h0,h1,h2,h3,h4⟩
def cw (p : Pos) (c : Nat) : Nat := 2 ^ (p.ht c) - 1 + p.bm c
def packedKey (k : Nat) (p : Pos) : Nat := ((((cw p 0 * 9007199254740991 + cw p 1) * 8796093022207 + cw p 2) * 35184372088831 + cw p 3) * 35184372088831 + cw p 4) * 27 + k/2
def fmt : SFormat := ⟨1,9765625,packedKey,(fun w => 2*(w / 9765625 % 27)),packedPos⟩

end C4W5.STopLongPacked
