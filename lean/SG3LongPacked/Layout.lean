import WindowStretch

namespace C4W5.SG3LongPacked
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.WindowBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def colHeight (x : Nat) : Nat := (if x < 1048576 then (if x < 1024 then (if x < 32 then (if x < 4 then (if x < 2 then 0 else 1) else (if x < 8 then 2 else (if x < 16 then 3 else 4))) else (if x < 128 then (if x < 64 then 5 else 6) else (if x < 256 then 7 else (if x < 512 then 8 else 9)))) else (if x < 32768 then (if x < 4096 then (if x < 2048 then 10 else 11) else (if x < 8192 then 12 else (if x < 16384 then 13 else 14))) else (if x < 131072 then (if x < 65536 then 15 else 16) else (if x < 262144 then 17 else (if x < 524288 then 18 else 19))))) else (if x < 1073741824 then (if x < 33554432 then (if x < 4194304 then (if x < 2097152 then 20 else 21) else (if x < 8388608 then 22 else (if x < 16777216 then 23 else 24))) else (if x < 134217728 then (if x < 67108864 then 25 else 26) else (if x < 268435456 then 27 else (if x < 536870912 then 28 else 29)))) else (if x < 34359738368 then (if x < 4294967296 then (if x < 2147483648 then 30 else 31) else (if x < 8589934592 then 32 else (if x < 17179869184 then 33 else 34))) else (if x < 274877906944 then (if x < 68719476736 then 35 else (if x < 137438953472 then 36 else 37)) else (if x < 549755813888 then 38 else (if x < 1099511627776 then 39 else 40))))))
def withColumn {α : Sort _} (v : Nat) (f : Nat → Nat → α) : α :=
  force (v+1) fun x => force (colHeight x) fun h => f (x - 2^h) h
def packedPos (w : Nat) : Pos :=
  force (w / 9765625 / 21) fun k4 =>
  force (k4 / 2199023255551) fun k3 =>
  force (k3 / 2199023255551) fun k2 =>
  force (k2 / 2199023255551) fun k1 =>
  force (k1 / 2199023255551) fun k0 =>
  withColumn k0 fun b0 h0 =>
  withColumn (k1 % 2199023255551) fun b1 h1 =>
  withColumn (k2 % 2199023255551) fun b2 h2 =>
  withColumn (k3 % 2199023255551) fun b3 h3 =>
  withColumn (k4 % 2199023255551) fun b4 h4 =>
  ⟨b0,b1,b2,b3,b4,h0,h1,h2,h3,h4⟩
def cw (p : Pos) (c : Nat) : Nat := 2 ^ (p.ht c) - 1 + p.bm c
def packedKey (k : Nat) (p : Pos) : Nat := ((((cw p 0 * 2199023255551 + cw p 1) * 2199023255551 + cw p 2) * 2199023255551 + cw p 3) * 2199023255551 + cw p 4) * 21 + k/2
def fmt : SFormat := ⟨1,9765625,packedKey,(fun w => 2*(w / 9765625 % 21)),packedPos⟩

end C4W5.SG3LongPacked
