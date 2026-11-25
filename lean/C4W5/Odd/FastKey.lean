import C4W5.Cert.Tree

/-!
# Compact 64-Bit-Scale Odd-Base Keys & O(log N) BST Range Lookup (`FastKey`)

Provides unified O(log N) GMP integer-range lookup (`raw`) and universal node verification
(`treeAllOK`) over `C4W5.CTree` for heights/zones `≤ 9` (`bm < 513`, `ht < 11`), supporting:
1. Labeled real-board certificate trees (`rmem`, `w = key9 p * 3125 + rep`)
2. Unlabeled real-board reachable-state sets (`rumem`, `w = key9 p`, 0 reply bytes)
3. Labeled zone-game certificate trees (`zmemG`, `w = keyZ9 p lb * 3125 + rep`)
4. Unlabeled zone-game reachable-state sets (`zumemG`, `w = keyZ9 p lb`, 0 reply bytes)

All radices (`513`, `11`, `243`, `3125`) are odd so kernel `force` evaluation never hits
trailing-zero-bit pathology. Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

private theorem digitDiv {b y : Nat} (x : Nat) (hb : 0 < b) (hy : y < b) :
    (x * b + y) / b = x := by
  rw [Nat.mul_comm x b, Nat.mul_add_div hb, Nat.div_eq_of_lt hy, Nat.add_zero]

private theorem digitMod {b y : Nat} (x : Nat) (hy : y < b) :
    (x * b + y) % b = y := by
  rw [Nat.mul_comm x b, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]

/-- Bounds check for compact encoding (`b1..b4 < 513`, `h0..h4 < 11`, covering all `H, K ≤ 9`). -/
def fits9 (p : Pos) : Bool :=
  Nat.blt p.b1 513 && Nat.blt p.b2 513 && Nat.blt p.b3 513 && Nat.blt p.b4 513 &&
  Nat.blt p.h0 11 && Nat.blt p.h1 11 && Nat.blt p.h2 11 && Nat.blt p.h3 11 && Nat.blt p.h4 11

/-- Compact position key with odd radices `513` (`> 2^9`) and `11` (`> 9`). -/
def key9 (p : Pos) : Nat :=
  ((((((((p.b0 * 513 + p.b1) * 513 + p.b2) * 513 + p.b3) * 513 + p.b4) * 11 +
    p.h0) * 11 + p.h1) * 11 + p.h2) * 11 + p.h3) * 11 + p.h4

/-- Sequential forced decoder matching `key9` in reverse order without repeated divisions. -/
def withUnpack9 {α : Sort _} (k : Nat) (f : Pos → α) : α :=
  force (k % 11) fun h4 => force (k / 11) fun k1 =>
  force (k1 % 11) fun h3 => force (k1 / 11) fun k2 =>
  force (k2 % 11) fun h2 => force (k2 / 11) fun k3 =>
  force (k3 % 11) fun h1 => force (k3 / 11) fun k4 =>
  force (k4 % 11) fun h0 => force (k4 / 11) fun k5 =>
  force (k5 % 513) fun b4 => force (k5 / 513) fun k6 =>
  force (k6 % 513) fun b3 => force (k6 / 513) fun k7 =>
  force (k7 % 513) fun b2 => force (k7 / 513) fun k8 =>
  force (k8 % 513) fun b1 => force (k8 / 513) fun b0 =>
  f ⟨b0, b1, b2, b3, b4, h0, h1, h2, h3, h4⟩

def unpack9 (k : Nat) : Pos := withUnpack9 k (fun p => p)

@[simp] theorem withUnpack9_eq {α : Sort _} (k : Nat) (f : Pos → α) :
    withUnpack9 k f = f (unpack9 k) := by
  simp only [withUnpack9, unpack9, force_eq]

theorem unpack9_key9 {p : Pos} (hf : fits9 p = true) : unpack9 (key9 p) = p := by
  rcases p with ⟨b0, b1, b2, b3, b4, h0, h1, h2, h3, h4⟩
  simp only [fits9, Bool.and_eq_true, Nat.blt_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hh0⟩, hh1⟩, hh2⟩, hh3⟩, hh4⟩ := hf
  have p11 : 0 < 11 := by decide
  have p513 : 0 < 513 := by decide
  simp only [unpack9, withUnpack9, force_eq, key9,
    digitMod _ hh4, digitDiv _ p11 hh4,
    digitMod _ hh3, digitDiv _ p11 hh3,
    digitMod _ hh2, digitDiv _ p11 hh2,
    digitMod _ hh1, digitDiv _ p11 hh1,
    digitMod _ hh0, digitDiv _ p11 hh0,
    digitMod _ hb4, digitDiv _ p513 hb4,
    digitMod _ hb3, digitDiv _ p513 hb3,
    digitMod _ hb2, digitDiv _ p513 hb2,
    digitMod _ hb1, digitDiv _ p513 hb1]

/-! ## Compact 5-Column Zone Labels -/

/-- Five column zone labels: `0 = low`, `1 = odd`, `2 = dead`. -/
structure Lab5 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  deriving DecidableEq

def Lab5.get (l : Lab5) : Nat → Nat
  | 0 => l.l0
  | 1 => l.l1
  | 2 => l.l2
  | 3 => l.l3
  | _ => l.l4

def Lab5.set (l : Lab5) (c v : Nat) : Lab5 :=
  match c with
  | 0 => { l with l0 := v }
  | 1 => { l with l1 := v }
  | 2 => { l with l2 := v }
  | 3 => { l with l3 := v }
  | _ => { l with l4 := v }

def Lab5.allDead (l : Lab5) : Bool :=
  Nat.ble 2 l.l0 && Nat.ble 2 l.l1 && Nat.ble 2 l.l2 && Nat.ble 2 l.l3 && Nat.ble 2 l.l4

def fitsL (lb : Lab5) : Bool :=
  Nat.blt lb.l0 3 && Nat.blt lb.l1 3 && Nat.blt lb.l2 3 && Nat.blt lb.l3 3 && Nat.blt lb.l4 3

def codeL (lb : Lab5) : Nat :=
  lb.l0 + 3 * lb.l1 + 9 * lb.l2 + 27 * lb.l3 + 81 * lb.l4

def unpackL (n : Nat) : Lab5 :=
  ⟨n % 3, n / 3 % 3, n / 9 % 3, n / 27 % 3, n / 81 % 3⟩

def keyZ9 (p : Pos) (lb : Lab5) : Nat :=
  key9 p * 243 + codeL lb

theorem decodeZ9 {p : Pos} {lb : Lab5} (hp : fits9 p = true) (hl : fitsL lb = true) :
    unpack9 (keyZ9 p lb / 243) = p ∧ unpackL (keyZ9 p lb % 243) = lb := by
  have hc : codeL lb < 243 := by
    rcases lb with ⟨l0, l1, l2, l3, l4⟩
    simp only [fitsL, Bool.and_eq_true, Nat.blt_eq] at hl
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hl
    simp only [codeL]; omega
  have hdiv : keyZ9 p lb / 243 = key9 p := digitDiv (key9 p) (by decide) hc
  have hmod : keyZ9 p lb % 243 = codeL lb := digitMod (key9 p) hc
  rw [hdiv, hmod]
  refine ⟨unpack9_key9 hp, ?_⟩
  rcases lb with ⟨l0, l1, l2, l3, l4⟩
  simp only [fitsL, Bool.and_eq_true, Nat.blt_eq] at hl
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hl
  simp only [unpackL, codeL, Lab5.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## Generic BST Membership & Universal Node Verification -/

/-- A match in the half-open response block decodes to its unique board key. -/
private theorem responseBlockKey {w k : Nat}
    (lo : k * 3125 ≤ w) (hi : w < k * 3125 + 3125) :
    w / 3125 = k := by omega

/-- An unlabeled reachability lookup uses a singleton block. -/
private theorem singletonBlockKey {w k : Nat}
    (lo : k ≤ w) (hi : w < k + 1) : w = k := by omega

inductive TIn : CTree → Nat → Prop
  | here (l w r) : TIn (.node l w r) w
  | left (l w r) {x} : TIn l x → TIn (.node l w r) x
  | right (l w r) {x} : TIn r x → TIn (.node l w r) x

def raw (lo hi : Nat) : CTree → Bool
  | .leaf => false
  | .node left w right =>
    if Nat.blt w lo then raw lo hi right
    else if Nat.blt w hi then true
    else raw lo hi left

theorem raw_sound {lo hi : Nat} : ∀ {t : CTree}, raw lo hi t = true → ∃ w, TIn t w ∧ lo ≤ w ∧ w < hi
  | .leaf, h => by simp [raw] at h
  | .node l w r, h => by
    unfold raw at h
    by_cases h1 : Nat.blt w lo = true
    · rw [if_pos h1] at h
      obtain ⟨x, hx, hlo, hhi⟩ := raw_sound h
      exact ⟨x, .right l w r hx, hlo, hhi⟩
    · rw [if_neg h1] at h
      by_cases h2 : Nat.blt w hi = true
      · rw [Nat.blt_eq] at h1 h2
        exact ⟨w, .here l w r, by omega, h2⟩
      · rw [if_neg h2] at h
        obtain ⟨x, hx, hlo, hhi⟩ := raw_sound h
        exact ⟨x, .left l w r hx, hlo, hhi⟩

def treeAllOK (checkW : Nat → Bool) : CTree → Bool
  | .leaf => true
  | .node l w r => checkW w && treeAllOK checkW l && treeAllOK checkW r

theorem treeAllOK_sound {checkW : Nat → Bool} :
    ∀ {t : CTree}, treeAllOK checkW t = true → ∀ {w}, TIn t w → checkW w = true
  | .leaf, _, _, hin => by cases hin
  | .node l w r, hall, _, hin => by
    simp only [treeAllOK, Bool.and_eq_true] at hall
    cases hin with
    | here => exact hall.1.1
    | left _ _ _ hl => exact treeAllOK_sound hall.1.2 hl
    | right _ _ _ hr => exact treeAllOK_sound hall.2 hr

theorem treeAllOK_node {checkW : Nat → Bool} {l r : CTree} {w : Nat}
    (hw : checkW w = true) (hl : treeAllOK checkW l = true) (hr : treeAllOK checkW r = true) :
    treeAllOK checkW (.node l w r) = true := by
  simp [treeAllOK, hw, hl, hr]

/-- Labeled real-board lookup (`w = key9 p * 3125 + rep`). -/
def rmem (t : CTree) (p : Pos) : Bool :=
  fits9 p && (force (key9 p * 3125) fun lo => force (lo + 3125) fun hi => raw lo hi t)

theorem rmem_sound {t : CTree} {p : Pos} (h : rmem t p = true) :
    ∃ w, TIn t w ∧ unpack9 (w / 3125) = p := by
  simp only [rmem, force_eq, Bool.and_eq_true] at h
  obtain ⟨w, hin, hlo, hhi⟩ := raw_sound h.2
  refine ⟨w, hin, ?_⟩
  rw [responseBlockKey hlo hhi]
  exact unpack9_key9 h.1

/-- Unlabeled real-board lookup (`w = key9 p`, zero reply bytes). -/
def rumem (t : CTree) (p : Pos) : Bool :=
  fits9 p && (force (key9 p) fun lo => force (lo + 1) fun hi => raw lo hi t)

theorem rumem_sound {t : CTree} {p : Pos} (h : rumem t p = true) :
    ∃ w, TIn t w ∧ unpack9 w = p := by
  simp only [rumem, force_eq, Bool.and_eq_true] at h
  obtain ⟨w, hin, hlo, hhi⟩ := raw_sound h.2
  refine ⟨w, hin, ?_⟩
  rw [singletonBlockKey hlo hhi]
  exact unpack9_key9 h.1

/-- Labeled zone-game lookup (`w = keyZ9 p lb * 3125 + rep`). -/
def zmemG (t : CTree) (p : Pos) (lb : Lab5) : Bool :=
  fits9 p && fitsL lb &&
    (force (keyZ9 p lb * 3125) fun lo => force (lo + 3125) fun hi => raw lo hi t)

theorem zmemG_sound {t : CTree} {p : Pos} {lb : Lab5} (h : zmemG t p lb = true) :
    ∃ w, TIn t w ∧ unpack9 (w / 3125 / 243) = p ∧ unpackL (w / 3125 % 243) = lb := by
  simp only [zmemG, force_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hl⟩, hr⟩ := h
  obtain ⟨w, hin, hlo, hhi⟩ := raw_sound hr
  refine ⟨w, hin, ?_⟩
  rw [responseBlockKey hlo hhi]
  exact decodeZ9 hp hl

/-- Unlabeled zone-game lookup (`w = keyZ9 p lb`, zero reply bytes). -/
def zumemG (t : CTree) (p : Pos) (lb : Lab5) : Bool :=
  fits9 p && fitsL lb &&
    (force (keyZ9 p lb) fun lo => force (lo + 1) fun hi => raw lo hi t)

theorem zumemG_sound {t : CTree} {p : Pos} {lb : Lab5} (h : zumemG t p lb = true) :
    ∃ w, TIn t w ∧ unpack9 (w / 243) = p ∧ unpackL (w % 243) = lb := by
  simp only [zumemG, force_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hl⟩, hr⟩ := h
  obtain ⟨w, hin, hlo, hhi⟩ := raw_sound hr
  refine ⟨w, hin, ?_⟩
  rw [singletonBlockKey hlo hhi]
  exact decodeZ9 hp hl

#print axioms rmem_sound
#print axioms zmemG_sound

end C4W5Gen
