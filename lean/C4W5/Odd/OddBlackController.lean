import C4W5.Odd.ZoneFastGen

/-!
# 4-Line Zero-Table Closed-Form Strategy for Odd-Height Black & Specialized Cert Wrappers

Defines the explicit closed-form reply controller for Black on odd-height `5 × (2m+1)` boards:
1. Open in 1-based column 2 (`0`-based index `1`).
2. Take any immediate Black four-in-a-row.
3. On every non-capping White move in column `c`, cover in the same column (`e = c`, budget `B = 0`).
4. On a capping White move in column `c`, follow the 4-line closed-form priority rule `oddBlackCap4Line`
   preserving the `{col 2 (WEven), col 4 (WOdd)}` distance-2 diagonal/horizontal parity lock.

Also provides monomorphic, zero-higher-order-unification wrapper functions and theorems for
generated certificate modules.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

def pickFirst (avail : Nat → Bool) : List Nat → Nat
  | [] => 0
  | e :: es => if avail e then e else pickFirst avail es

/-- 4-line closed-form cap transfer rule (`0`-based columns `0..4` = `1`-based `{1..5}`):
    - `c = 4` (`5`) → `[2, 0, 1, 3]`
    - `c = 2` (`3`) → `1` if `early25` (`|R(2)| ≤ 3 ∧ |R(5)| ≤ 2`) and `avail 1`, else `[4, 0, 1, 3]`
    - `c = 0` (`1`) → `[2, 1, 4, 3]`
    - `c = 3` (`4`) → `[0, 2, 4, 1, 3]` -/
def oddBlackCap4Line (early25 : Bool) (avail : Nat → Bool) (c : Nat) : Nat :=
  if c == 4 then pickFirst avail [2, 0, 1, 3]
  else if c == 2 then
    if early25 && avail 1 then 1 else pickFirst avail [4, 0, 1, 3]
  else if c == 0 then pickFirst avail [2, 1, 4, 3]
  else pickFirst avail [0, 2, 4, 1, 3]

def realWinAt (h : Nat) (p1 : Pos) (e : Nat) : Bool :=
  Nat.blt (p1.ht e) h && (forceP (p1.push e .black) fun p2 => p2.hasFourQ .black)

def oddBlackRealReply (h : Nat) (p1 : Pos) (c : Nat) : Nat :=
  if realWinAt h p1 0 then 0
  else if realWinAt h p1 1 then 1
  else if realWinAt h p1 2 then 2
  else if realWinAt h p1 3 then 3
  else if realWinAt h p1 4 then 4
  else if Nat.blt (p1.ht c) h then c
  else oddBlackCap4Line (Nat.ble p1.h1 3 && Nat.ble p1.h4 2) (fun e => Nat.blt (p1.ht e) h) c

def oddBlackZoneLowReply (K : Nat) (p1 : Pos) (l : Lab5) (c : Nat) : Nat :=
  if zWinG K .black p1 l 0 then 0
  else if zWinG K .black p1 l 1 then 1
  else if zWinG K .black p1 l 2 then 2
  else if zWinG K .black p1 l 3 then 3
  else if zWinG K .black p1 l 4 then 4
  else c

def zoneAvail (K : Nat) (p : Pos) (l1 : Lab5) (e : Nat) : Bool :=
  (l1.get e == 0 && Nat.ble (p.ht e) K) || l1.get e == 1

def oddBlackZoneCapReply (K : Nat) (p : Pos) (l1 : Lab5) (c : Nat) : Nat :=
  if zWinG K .black p l1 0 then 0
  else if zWinG K .black p l1 1 then 1
  else if zWinG K .black p l1 2 then 2
  else if zWinG K .black p l1 3 then 3
  else if zWinG K .black p l1 4 then 4
  else
    let early25 := l1.l1 == 0 && Nat.ble p.h1 3 && l1.l4 == 0 && Nat.ble p.h4 2
    oddBlackCap4Line early25 (zoneAvail K p l1) c

/-! ## Monomorphic Wrappers for Generated Modules (Zero Higher-Order Unification) -/

def checkRealBlack (h : Nat) (t : CTree) : Nat → Bool :=
  realCheckW h .black t (fastEven .black h)

theorem safe_real_even_black {h : Nat} (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (hall : treeAllOK (checkRealBlack h t) t = true)
    (hq : rmem t q = true) :
    SafeP h .black (playList (emptyBoard 5) .black ms) :=
  safeP_of_real_tree (claimEven_realLeafSound h .black)
    (leafB := fastEven .black h) (fun _ hf => fastEven_sound hf) t ms q hr hall hq

def checkRealWhite (h : Nat) (t : CTree) : Nat → Bool :=
  realCheckW h .white t (fastOdd .white h)

theorem safe_real_odd_white {h : Nat} (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (hall : treeAllOK (checkRealWhite h t) t = true)
    (hq : rmem t q = true) :
    SafeP h .white (playList (emptyBoard 5) .black ms) :=
  safeP_of_real_tree (claimOdd_realLeafSound h .white)
    (leafB := fastOdd .white h) (fun _ hf => fastOdd_sound hf) t ms q hr hall hq

def checkRealExplicitBlack (h : Nat) (t : CTree) : Nat → Bool :=
  realUCheckW h .black t (fastEven .black h) (oddBlackRealReply h)

theorem safe_real_explicit_black {h : Nat} (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (hall : treeAllOK (checkRealExplicitBlack h t) t = true)
    (hq : rumem t q = true) :
    SafeP h .black (playList (emptyBoard 5) .black ms) :=
  safeP_of_explicit_real_tree (claimEven_realLeafSound h .black)
    (leafB := fastEven .black h) (fun _ hf => fastEven_sound hf)
    (oddBlackRealReply h) t ms q hr hall hq

def checkZoneWhite (K : Nat) (t : CTree) : Nat → Bool :=
  zoneCheckW K .white t (fastOdd .white K)

theorem safe_zone_odd_white {K H : Nat} (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : treeAllOK (checkZoneWhite K t) t = true)
    (ht : q.total % 2 = 0)
    (hd : discBG .black K q = true)
    (hmem : zmemG t q ⟨0, 0, 0, 0, 0⟩ = true) :
    SafeP H .white (playList (emptyBoard 5) .black ms) :=
  zone_safeP_of_tree hpar hKH
    (Leaf := fun k board => ∃ column : Fin 5, ClaimOddHyp .white k board column)
    (claimOdd_zoneLeafSound .white)
    (leafB := fastOdd .white K) (fun _ hf => fastOdd_sound hf) t ms q hr hall ht hd hmem

def checkZoneExplicitBlack (K : Nat) (t : CTree) : Nat → Bool :=
  zoneUCheckW K .black t (fastEven .black K) (oddBlackZoneLowReply K) (oddBlackZoneCapReply K)

theorem safe_zone_explicit_black {K H : Nat} (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : treeAllOK (checkZoneExplicitBlack K t) t = true)
    (ht : q.total % 2 = 1)
    (hd : discBG .white K q = true)
    (hmem : zumemG t q ⟨0, 0, 0, 0, 0⟩ = true) :
    SafeP H .black (playList (emptyBoard 5) .black ms) :=
  zone_safeP_of_explicit_tree hpar hKH
    (Leaf := ClaimEvenHyp .black) (claimEven_zoneLeafSound .black)
    (leafB := fastEven .black K) (fun _ hf => fastEven_sound hf)
    (oddBlackZoneLowReply K) (oddBlackZoneCapReply K) t ms q hr hall ht hd hmem

end C4W5Gen
