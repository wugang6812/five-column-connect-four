import C4W5.Theory.Zone
import C4W5.Cert.Tree

/-!
# Kernel-checkable certificates for the zone game `G_K`
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- Five labels: 0 = low, 1 = odd, 2 (or more) = dead. -/
structure Lab5 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat

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

def natLab (n : Nat) : Lab := if n = 0 then .low else if n = 1 then .odd else .dead

def Lab5.fn (l : Lab5) : Fin 5 → Lab := fun c => natLab (l.get c.val)

theorem Lab5.fn_set (l : Lab5) (c : Fin 5) (v : Nat) :
    (l.set c.val v).fn = Function.update l.fn c (natLab v) := by
  funext d
  fin_cases c <;> fin_cases d <;> simp [Lab5.fn, Lab5.set, Lab5.get, Function.update]

def Lab5.beq (a b : Lab5) : Bool :=
  a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3 && a.l4 == b.l4

theorem Lab5.eq_of_beq {a b : Lab5} (h : a.beq b = true) : a = b := by
  unfold Lab5.beq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩ := h
  cases a; cases b; simp_all

def Lab5.allDead (l : Lab5) : Bool :=
  Nat.ble 2 l.l0 && Nat.ble 2 l.l1 && Nat.ble 2 l.l2 && Nat.ble 2 l.l3 && Nat.ble 2 l.l4

theorem natLab_dead {n : Nat} (h : 2 ≤ n) : natLab n = .dead := by
  unfold natLab; rw [if_neg (by omega), if_neg (by omega)]

theorem Lab5.allDead_sound {l : Lab5} (h : l.allDead = true) (d : Fin 5) : l.fn d = .dead := by
  unfold Lab5.allDead at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩ := h
  fin_cases d <;> exact natLab_dead (by assumption)

/-! ## The checker -/

/-- Black's non-winning reply `e` leads to a certified state. -/
def zOut (K : Nat) (memf : Pos → Lab5 → Bool) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  force (l.get e) fun le =>
  if le = 0 then
    (if p.ht e < K then forceP (p.push e .black) fun p2 => memf p2 l else memf p (l.set e 1))
  else if le = 1 then memf p (l.set e 2) else false

/-- Black's reply `e` wins at once. -/
def zWin (K : Nat) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  if l.get e = 0 then
    (if p.ht e < K then forceP (p.push e .black) fun p2 => p2.hasFourQ .black else false)
  else false

def zCol (K : Nat) (memf : Pos → Lab5 → Bool) (p : Pos) (l : Lab5) (rep c : Nat) : Bool :=
  force (l.get c) fun lc =>
  if lc = 0 then
    (if p.ht c < K then
      forceP (p.push c .white) fun p1 =>
        !p1.hasFourQ .white &&
        (force (replyOf rep c) fun e =>
          zWin K p1 l e || ((e == c || Nat.ble (p.ht c + 5) K) && zOut K memf p1 l e))
    else memf p (l.set c 2))
  else if lc = 1 then
    ((l.set c 2).allDead ||
      (force (replyOf rep c) fun e => zWin K p (l.set c 2) e || zOut K memf p (l.set c 2) e))
  else true

def stepOKZ (K : Nat) (memf : Pos → Lab5 → Bool) (p : Pos) (l : Lab5) (rep : Nat) : Bool :=
  p.wfB K && zCol K memf p l rep 0 && zCol K memf p l rep 1 && zCol K memf p l rep 2 &&
  zCol K memf p l rep 3 && zCol K memf p l rep 4

/-! ## Soundness -/

section
variable {K : Nat} {I : Board 5 → (Fin 5 → Lab) → Prop} {memf : Pos → Lab5 → Bool}

theorem zOut_sound (hm : ∀ q l', memf q l' = true → I q.toBoard l'.fn) {p : Pos} (hw : p.WF K)
    {l : Lab5} {e : Fin 5} (h : zOut K memf p l e.val = true) : BlackOut K I p.toBoard l.fn e := by
  unfold zOut at h
  rw [force_eq] at h
  have hht := (hw e.val).2
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    have hl : l.fn e = .low := by simp [Lab5.fn, natLab, h0]
    by_cases hlt : p.ht e.val < K
    · rw [if_pos hlt, forceP_eq] at h
      have := hm _ _ h
      rw [Pos.toBoard_push hw] at this
      exact Or.inl ⟨hl, by rw [Pos.height]; exact hlt, this⟩
    · rw [if_neg hlt] at h
      have := hm _ _ h
      rw [Lab5.fn_set] at this
      exact Or.inr (Or.inl ⟨hl, by rw [Pos.height]; omega, this⟩)
  · rw [if_neg h0] at h
    by_cases h1 : l.get e.val = 1
    · rw [if_pos h1] at h
      have hl : l.fn e = .odd := by simp [Lab5.fn, natLab, h1]
      have := hm _ _ h
      rw [Lab5.fn_set] at this
      exact Or.inr (Or.inr ⟨hl, this⟩)
    · rw [if_neg h1] at h; exact Bool.noConfusion h

theorem zWin_sound {p : Pos} (hw : p.WF K) {l : Lab5} {e : Fin 5} (h : zWin K p l e.val = true) :
    BlackWin K p.toBoard l.fn := by
  unfold zWin at h
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    by_cases hlt : p.ht e.val < K
    · rw [if_pos hlt, forceP_eq, Pos.hasFourQ_eq] at h
      refine ⟨e, by simp [Lab5.fn, natLab, h0], by rw [Pos.height]; exact hlt, ?_⟩
      rw [← Pos.toBoard_push hw]
      exact (hasFourF_iff (Pos.WF_push hw e .black hlt) _).mp h
    · rw [if_neg hlt] at h; exact Bool.noConfusion h
  · rw [if_neg h0] at h; exact Bool.noConfusion h

def replyFin (rep c : Nat) : Fin 5 := ⟨replyOf rep c, Nat.mod_lt _ (by decide)⟩

/-- One column of the closure condition. -/
theorem zCol_sound (hm : ∀ q l', memf q l' = true → I q.toBoard l'.fn) {p : Pos} (hw : p.WF K)
    {l : Lab5} {rep : Nat} (c : Fin 5) (h : zCol K memf p l rep c.val = true) :
    (l.fn c = .low → (p.toBoard c).length < K →
      ¬ HasFour K (play p.toBoard c .white) .white ∧
      (BlackWin K (play p.toBoard c .white) l.fn ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ K) ∧ BlackOut K I (play p.toBoard c .white) l.fn e)) ∧
    (l.fn c = .low → (p.toBoard c).length = K → I p.toBoard (Function.update l.fn c .dead)) ∧
    (l.fn c = .odd → (∀ d, Function.update l.fn c .dead d = .dead) ∨
      BlackWin K p.toBoard (Function.update l.fn c .dead) ∨
      ∃ e, BlackOut K I p.toBoard (Function.update l.fn c .dead) e) := by
  unfold zCol at h
  rw [force_eq] at h
  have hfn : l.fn c = natLab (l.get c.val) := rfl
  have hupd : (l.set c.val 2).fn = Function.update l.fn c .dead := by rw [Lab5.fn_set]; rfl
  by_cases h0 : l.get c.val = 0
  · rw [if_pos h0] at h
    refine ⟨fun _ hlt => ?_, fun _ heq => ?_, fun hodd => ?_⟩
    · rw [Pos.height] at hlt
      rw [if_pos hlt, forceP_eq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', force_eq, Bool.or_eq_true, Pos.hasFourQ_eq] at h
      obtain ⟨hnf, hrest⟩ := h
      have hw1 := Pos.WF_push hw c .white hlt
      have hb1 := Pos.toBoard_push hw c .white
      refine ⟨?_, ?_⟩
      · intro hf
        rw [← hb1, ← hasFourF_iff hw1, hnf] at hf
        exact Bool.noConfusion hf
      · rw [← hb1]
        rcases hrest with hwin | ⟨hmust, hout⟩
        · exact Or.inl (zWin_sound hw1 (e := replyFin rep c.val) hwin)
        · refine Or.inr ⟨replyFin rep c.val, ?_, zOut_sound hm hw1 hout⟩
          rw [Pos.height]
          rcases hmust with he | hle
          · left; apply Fin.ext; show replyOf rep c.val = c.val; simpa using he
          · right; simpa using hle
    · rw [Pos.height] at heq
      rw [if_neg (by omega)] at h
      have := hm _ _ h
      rwa [hupd] at this
    · rw [hfn, h0] at hodd; simp [natLab] at hodd
  · rw [if_neg h0] at h
    refine ⟨fun hlow => ?_, fun hlow => ?_, fun _ => ?_⟩
    · rw [hfn] at hlow; unfold natLab at hlow; rw [if_neg h0] at hlow; split at hlow <;> cases hlow
    · rw [hfn] at hlow; unfold natLab at hlow; rw [if_neg h0] at hlow; split at hlow <;> cases hlow
    · by_cases h1 : l.get c.val = 1
      · rw [if_pos h1] at h
        simp only [Bool.or_eq_true, force_eq] at h
        rw [← hupd]
        rcases h with hall | hwin | hout
        · exact Or.inl (Lab5.allDead_sound hall)
        · exact Or.inr (Or.inl (zWin_sound hw (e := replyFin rep c.val) hwin))
        · exact Or.inr (Or.inr ⟨replyFin rep c.val, zOut_sound hm hw hout⟩)
      · exfalso
        rename_i hodd
        rw [hfn] at hodd; unfold natLab at hodd; rw [if_neg h0, if_neg h1] at hodd; cases hodd

theorem stepOKZ_sound (hm : ∀ q l', memf q l' = true → I q.toBoard l'.fn) {p : Pos} {l : Lab5}
    {rep : Nat} (h : stepOKZ K memf p l rep = true) (c : Fin 5) :
    (l.fn c = .low → (p.toBoard c).length < K →
      ¬ HasFour K (play p.toBoard c .white) .white ∧
      (BlackWin K (play p.toBoard c .white) l.fn ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ K) ∧ BlackOut K I (play p.toBoard c .white) l.fn e)) ∧
    (l.fn c = .low → (p.toBoard c).length = K → I p.toBoard (Function.update l.fn c .dead)) ∧
    (l.fn c = .odd → (∀ d, Function.update l.fn c .dead d = .dead) ∨
      BlackWin K p.toBoard (Function.update l.fn c .dead) ∨
      ∃ e, BlackOut K I p.toBoard (Function.update l.fn c .dead) e) := by
  unfold stepOKZ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hwf, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  have hw := Pos.wfB_sound hwf
  fin_cases c
  · exact zCol_sound hm hw 0 h0
  · exact zCol_sound hm hw 1 h1
  · exact zCol_sound hm hw 2 h2
  · exact zCol_sound hm hw 3 h3
  · exact zCol_sound hm hw 4 h4

end

/-! ## Certificate trees for zone states -/

def unpackL (n : Nat) : Lab5 := ⟨n % 3, n / 3 % 3, n / 9 % 3, n / 27 % 3, n / 81 % 3⟩

def keyZ (p : Pos) (l : Lab5) : Nat :=
  keyOf p * 243 + (l.l0 + 3 * l.l1 + 9 * l.l2 + 27 * l.l3 + 81 * l.l4)

/-- Entries are `w = (keyOf p * 243 + labels) * 3125 + rep`. -/
inductive ZIn : CTree → Pos → Lab5 → Nat → Prop
  | here (l w r) : ZIn (.node l w r) (unpack (w / 3125 / 243)) (unpackL (w / 3125 % 243)) (w % 3125)
  | left (l w r) {p lb q} : ZIn l p lb q → ZIn (.node l w r) p lb q
  | right (l w r) {p lb q} : ZIn r p lb q → ZIn (.node l w r) p lb q

def zmemK : CTree → Nat → Pos → Lab5 → Bool
  | .leaf, _, _, _ => false
  | .node l w r, k, p, lb =>
    force (w / 3125) fun kq =>
    if k = kq then (withUnpack (kq / 243) fun q => q.beq p) && (unpackL (kq % 243)).beq lb
    else if k < kq then zmemK l k p lb else zmemK r k p lb

def zmemB (t : CTree) (p : Pos) (lb : Lab5) : Bool := force (keyZ p lb) fun k => zmemK t k p lb

theorem zmemK_sound : ∀ (t : CTree) (k : Nat) (p : Pos) (lb : Lab5), zmemK t k p lb = true →
    ∃ rep, ZIn t p lb rep
  | .leaf, _, _, _, h => by simp [zmemK] at h
  | .node l w r, k, p, lb, h => by
    unfold zmemK at h
    rw [force_eq] at h
    by_cases h1 : k = w / 3125
    · rw [if_pos h1, withUnpack_eq, Bool.and_eq_true] at h
      have e1 := Pos.eq_of_beq h.1
      have e2 := Lab5.eq_of_beq h.2
      subst e1; subst e2
      exact ⟨w % 3125, .here l w r⟩
    · rw [if_neg h1] at h
      by_cases h2 : k < w / 3125
      · rw [if_pos h2] at h
        obtain ⟨q, hq⟩ := zmemK_sound l k p lb h
        exact ⟨q, .left l w r hq⟩
      · rw [if_neg h2] at h
        obtain ⟨q, hq⟩ := zmemK_sound r k p lb h
        exact ⟨q, .right l w r hq⟩

theorem zmemB_sound (t : CTree) (p : Pos) (lb : Lab5) (h : zmemB t p lb = true) : ∃ rep, ZIn t p lb rep := by
  unfold zmemB at h; rw [force_eq] at h; exact zmemK_sound t _ p lb h

def zallOK (K : Nat) (memf : Pos → Lab5 → Bool) : CTree → Bool
  | .leaf => true
  | .node l w r =>
    (withUnpack (w / 3125 / 243) fun pos => stepOKZ K memf pos (unpackL (w / 3125 % 243)) (w % 3125)) &&
      zallOK K memf l && zallOK K memf r

theorem zallOK_sound {K : Nat} {memf : Pos → Lab5 → Bool} :
    ∀ (t : CTree), zallOK K memf t = true → ∀ p lb rep, ZIn t p lb rep → stepOKZ K memf p lb rep = true
  | .leaf, _, _, _, _, hin => by cases hin
  | .node l w r, hall, p, lb, q, hin => by
    unfold zallOK at hall
    simp only [Bool.and_eq_true, withUnpack_eq] at hall
    cases hin with
    | here => exact hall.1.1
    | left _ _ _ hl => exact zallOK_sound l hall.1.2 p lb q hl
    | right _ _ _ hr => exact zallOK_sound r hall.2 p lb q hr

theorem zallOK_node {K : Nat} {memf : Pos → Lab5 → Bool} {l r : CTree} {w : Nat}
    (h1 : stepOKZ K memf (unpack (w / 3125 / 243)) (unpackL (w / 3125 % 243)) (w % 3125) = true)
    (h2 : zallOK K memf l = true) (h3 : zallOK K memf r = true) :
    zallOK K memf (CTree.node l w r) = true := by
  unfold zallOK; rw [withUnpack_eq, h1, h2, h3]; rfl

/-- The abstract positions held by a tree. -/
def ZI (t : CTree) (L : Board 5) (ℓ : Fin 5 → Lab) : Prop :=
  ∃ p lb rep, ZIn t p lb rep ∧ L = p.toBoard ∧ ℓ = lb.fn

theorem zoneCert_of_tree {K : Nat} (t : CTree) (hall : zallOK K (zmemB t) t = true) :
    ZoneCert K (ZI t) := by
  rintro L ℓ ⟨p, lb, rep, hin, rfl, rfl⟩ c
  refine stepOKZ_sound (I := ZI t) (fun q l' hq => ?_) (zallOK_sound t hall p lb rep hin) c
  obtain ⟨rep', hin'⟩ := zmemB_sound t q l' hq
  exact ⟨q, l', rep', hin', rfl, rfl⟩

/-! ## Roots: the discipline of a starting position -/

def colDisc (K b h : Nat) : Bool :=
  Nat.blt (maskOf .white b h &&& (maskOf .white b h <<< 1 ||| 2 ^ 0)) (2 ^ (K - 3)) &&
  ((!(h == 0) && b.testBit (h - 1)) || Nat.ble (h + 4) K)

def Pos.discB (K : Nat) (p : Pos) : Bool :=
  Nat.ble 4 K && colDisc K p.b0 p.h0 && colDisc K p.b1 p.h1 && colDisc K p.b2 p.h2 &&
  colDisc K p.b3 p.h3 && colDisc K p.b4 p.h4

theorem colDisc_sound {K b h : Nat} (hK : 4 ≤ K) (hb : b < 2 ^ h) (hd : colDisc K b h = true) :
    (∀ r, stone (decC h b) r = some .white → (r = 0 ∨ stone (decC h b) (r - 1) = some .white) →
      r + 4 ≤ K) ∧
    ((h = 0 ∨ stone (decC h b) (h - 1) = some .white) → h + 4 ≤ K) := by
  unfold colDisc at hd
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Nat.ble_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hd
  obtain ⟨hexc, htop⟩ := hd
  constructor
  · intro r h1 h2
    by_contra hcon
    have hbit : (maskOf .white b h &&& (maskOf .white b h <<< 1 ||| 2 ^ 0)).testBit r = true := by
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow,
        (testBit_maskOf hb .white r).mpr h1]
      rcases h2 with h2 | h2
      · simp [h2]
      · by_cases hr0 : r = 0
        · simp [hr0]
        · simp [(testBit_maskOf hb .white (r - 1)).mpr h2, show 1 ≤ r by omega]
    have := testBit_false_of_lt hexc (show K - 3 ≤ r by omega)
    rw [this] at hbit; exact Bool.noConfusion hbit
  · intro h1
    rcases htop with ⟨hne, hbit⟩ | hle
    · exfalso
      rcases h1 with h0 | hw
      · exact hne h0
      · rw [stone_decC, if_pos (by omega), hbit] at hw
        simp [bitP] at hw
    · exact hle

theorem Pos.discB_sound {K H : Nat} {p : Pos} (hw : p.WF K) (hd : p.discB K = true) :
    DiscE K p.toBoard ∧ ∀ c, TCol K H p.toBoard c := by
  unfold Pos.discB at hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hd
  obtain ⟨⟨⟨⟨⟨hK, d0⟩, d1⟩, d2⟩, d3⟩, d4⟩ := hd
  have hcol : ∀ c : Fin 5, colDisc K (p.bm c.val) (p.ht c.val) = true := by
    intro c; fin_cases c <;> assumption
  constructor
  · intro c r hexc
    exact (colDisc_sound hK (hw c.val).1 (hcol c)).1 r hexc.1 hexc.2
  · intro c _ htop
    have := (colDisc_sound hK (hw c.val).1 (hcol c)).2
    simp only [Pos.toBoard, decC_length] at htop
    rw [Pos.height]; exact this htop

theorem Pos.WF_mono {K H : Nat} {p : Pos} (hw : p.WF K) (hKH : K ≤ H) : p.WF H :=
  fun c => ⟨(hw c).1, le_trans (hw c).2 hKH⟩

/-- **Zone certificates prove safety for every even height `H ≥ K + 2`.** -/
theorem zone_tree_safe {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H) (t : CTree)
    (hall : zallOK K (zmemB t) t = true) (q : Pos) (hwf : q.WF K) (hodd : q.total % 2 = 1)
    (hnw : ¬ HasFour K q.toBoard .white) (hnb : ¬ HasFour K q.toBoard .black)
    (hd : q.discB K = true) (hmem : zmemB t q ⟨0, 0, 0, 0, 0⟩ = true) : Safe H q.toBoard := by
  have hwH := Pos.WF_mono hwf (show K ≤ H by omega)
  obtain ⟨hE, hT⟩ := Pos.discB_sound (H := H) hwf hd
  have htrunc : trunc K q.toBoard = q.toBoard := by
    funext c
    simp only [trunc]
    exact List.take_of_length_le (by rw [Pos.height]; exact (hwf c.val).2)
  have hfourK : ∀ pl, HasFour H q.toBoard pl → HasFour K q.toBoard pl := by
    intro pl hf
    rw [← hasFourF_iff hwH] at hf
    exact (hasFourF_iff hwf pl).mp hf
  apply zone_safe hK hH hKH (zoneCert_of_tree t hall)
  exact
    { tm := by unfold toMove; rw [Pos.totalStones_eq, if_neg (by omega)]
      nw := fun hf => hnw (hfourK _ hf)
      nb := fun hf => hnb (hfourK _ hf)
      dE := hE
      dT := hT
      valid := fun c => by rw [Pos.height]; exact (hwH c.val).2
      abs := Or.inl (by
        rw [htrunc]
        obtain ⟨rep, hin⟩ := zmemB_sound t q _ hmem
        refine ⟨q, _, rep, hin, rfl, ?_⟩
        funext c
        simp only [labs, labOf, Lab5.fn]
        rw [if_pos (by rw [Pos.height]; exact (hwf c.val).2)]
        fin_cases c <;> rfl) }

/-- The form used by generated certificate files: root given by a move list. -/
theorem zone_safe_of_tree {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H) (t : CTree)
    (ms : List (Fin 5)) (q : Pos) (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : zallOK K (zmemB t) t = true) (hodd : q.total % 2 = 1) (hd : q.discB K = true)
    (hmem : zmemB t q ⟨0, 0, 0, 0, 0⟩ = true) : Safe H (playList (emptyBoard 5) .black ms) := by
  obtain ⟨e, hnw, hnb, hwf⟩ := root_of_run' hr
  rw [← e]
  exact zone_tree_safe hK hH hKH t hall q hwf hodd hnw hnb hd hmem

#print axioms zone_safe_of_tree

end C4W5
