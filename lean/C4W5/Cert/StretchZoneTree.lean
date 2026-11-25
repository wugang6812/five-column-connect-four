import C4W5.Cert.StretchZoneC

/-!
# Certificate trees for the zone game modulo stretching

Entries are `w = (skeyOf k p * 243 + labels) * 5^10 + rep`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

def szkeyOf (k : Nat) (p : Pos) (l : Lab5) : Nat :=
  skeyOf k p * 243 + (l.l0 + 3 * l.l1 + 9 * l.l2 + 27 * l.l3 + 81 * l.l4)

inductive CTree.SZIn : CTree → Nat → Pos → Lab5 → Nat → Prop
  | here (l w r) : CTree.SZIn (.node l w r) (sunpack (w / SR / 243)).1 (sunpack (w / SR / 243)).2
      (unpackL (w / SR % 243)) (w % SR)
  | left (l w r) {k p lb q} : CTree.SZIn l k p lb q → CTree.SZIn (.node l w r) k p lb q
  | right (l w r) {k p lb q} : CTree.SZIn r k p lb q → CTree.SZIn (.node l w r) k p lb q

def CTree.szmemK : CTree → Nat → Nat → Pos → Lab5 → Bool
  | .leaf, _, _, _, _ => false
  | .node l w r, key, k, p, lb =>
    force (w / SR) fun kq =>
    if key == kq then
      (withSUnpack (kq / 243) fun k' q => k' == k && q.beq p) && (unpackL (kq % 243)).beq lb
    else if key < kq then l.szmemK key k p lb else r.szmemK key k p lb

def CTree.szmemB (t : CTree) (k : Nat) (p : Pos) (lb : Lab5) : Bool :=
  force (szkeyOf k p lb) fun key => t.szmemK key k p lb

theorem CTree.szmemK_sound : ∀ (t : CTree) (key k : Nat) (p : Pos) (lb : Lab5),
    t.szmemK key k p lb = true → ∃ rep, t.SZIn k p lb rep
  | .leaf, _, _, _, _, h => by simp [CTree.szmemK] at h
  | .node l w r, key, k, p, lb, h => by
    unfold CTree.szmemK at h
    rw [force_eq] at h
    by_cases h1 : (key == w / SR) = true
    · rw [if_pos h1, withSUnpack_eq, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hk, hp⟩, hl⟩ := h
      have e1 := Pos.eq_of_beq hp
      have e2 := Lab5.eq_of_beq hl
      subst e1; subst e2; subst hk
      exact ⟨w % SR, .here l w r⟩
    · rw [if_neg h1] at h
      by_cases h2 : key < w / SR
      · rw [if_pos h2] at h
        obtain ⟨q, hq⟩ := CTree.szmemK_sound l key k p lb h
        exact ⟨q, .left l w r hq⟩
      · rw [if_neg h2] at h
        obtain ⟨q, hq⟩ := CTree.szmemK_sound r key k p lb h
        exact ⟨q, .right l w r hq⟩

theorem CTree.szmemB_sound (t : CTree) (k : Nat) (p : Pos) (lb : Lab5)
    (h : t.szmemB k p lb = true) : ∃ rep, t.SZIn k p lb rep := by
  unfold CTree.szmemB at h; rw [force_eq] at h; exact CTree.szmemK_sound t _ k p lb h

def CTree.szallOK (D : Nat) (memf : Nat → Pos → Lab5 → Bool) : CTree → Bool
  | .leaf => true
  | .node l w r =>
    (withSUnpack (w / SR / 243) fun k pos => stepOKSZ D memf k pos (unpackL (w / SR % 243)) (w % SR)) &&
      l.szallOK D memf && r.szallOK D memf

theorem CTree.szallOK_sound {D : Nat} {memf : Nat → Pos → Lab5 → Bool} :
    ∀ (t : CTree), t.szallOK D memf = true → ∀ k p lb rep, t.SZIn k p lb rep →
      stepOKSZ D memf k p lb rep = true
  | .leaf, _, _, _, _, _, hin => by cases hin
  | .node l w r, hall, k, p, lb, q, hin => by
    unfold CTree.szallOK at hall
    simp only [Bool.and_eq_true, withSUnpack_eq] at hall
    cases hin with
    | here => exact hall.1.1
    | left _ _ _ hl => exact CTree.szallOK_sound l hall.1.2 k p lb q hl
    | right _ _ _ hr => exact CTree.szallOK_sound r hall.2 k p lb q hr

theorem szallOK_node {D : Nat} {memf : Nat → Pos → Lab5 → Bool} {l r : CTree} {w : Nat}
    (h1 : stepOKSZ D memf (sunpack (w / SR / 243)).1 (sunpack (w / SR / 243)).2
      (unpackL (w / SR % 243)) (w % SR) = true)
    (h2 : l.szallOK D memf = true) (h3 : r.szallOK D memf = true) :
    (CTree.node l w r).szallOK D memf = true := by
  unfold CTree.szallOK; rw [withSUnpack_eq, h1, h2, h3]; rfl

/-- The abstract zone states held by a tree. -/
def CTree.SZSet (t : CTree) (k : Nat) (A : Board 5) (ℓ : Fin 5 → Lab) : Prop :=
  ∃ p lb rep, t.SZIn k p lb rep ∧ A = p.toBoard ∧ ℓ = lb.fn

theorem szCert_of_tree {D : Nat} (hD : 2 ≤ D) (t : CTree) (hall : t.szallOK D t.szmemB = true) :
    SZCert D t.SZSet := by
  rintro k A ℓ ⟨p, lb, rep, hin, rfl, rfl⟩
  refine stepOKSZ_sound hD (J := t.SZSet) (fun k q l' hq => ?_) (CTree.szallOK_sound t hall k p lb rep hin)
  obtain ⟨rep', hin'⟩ := t.szmemB_sound k q l' hq
  exact ⟨q, l', rep', hin', rfl, rfl⟩

/-- **Zone-on-stretch certificates.** -/
theorem sz_safe_of_tree {D : Nat} (hD : 2 ≤ D) (t : CTree) (hall : t.szallOK D t.szmemB = true)
    {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H) {R : Board 5}
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hE : DiscE K R) (hT : ∀ c, TCol K H R c) (hv : Valid H R)
    {k : Nat} {q : Pos} {lb : Lab5} (hq : t.szmemB k q lb = true) (hl : lb.fn = labs H K R)
    (s : SEq D k q.toBoard K (trunc K R)) : Safe H R := by
  obtain ⟨rep, hin⟩ := t.szmemB_sound k q lb hq
  exact sz_safe hD (szCert_of_tree hD t hall) hK hH hKH htm hnw hnb hE hT hv
    (hl ▸ ⟨q, lb, rep, hin, rfl, rfl⟩) s

#print axioms sz_safe_of_tree

end C4W5
