import C4W5.Cert.StretchC

/-!
# Stretch-game certificates: step soundness and the certificate tree

Entries are `w = key * 5^10 + rep`, `key = (((b0·M + … + b4)·131 + h0)·131 + … + h4)·131 + H`
with `M = 2^89 − 1` (odd multipliers, see `Cert/Tree.lean`).  The reply word has ten base-5 digits:
digit `2c` for White's plain move in column `c`, digit `2c+1` for the stretched variant.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

theorem stepOKS_sound {D : Nat} {I : Nat → Board 5 → Prop} {memf : Nat → Pos → Bool} (hD : 2 ≤ D)
    (hm : ∀ h q, memf h q = true → I h q.toBoard) {H : Nat} {p : Pos} {rep : Nat}
    (hok : stepOKS D memf H p rep = true) :
    ∀ c, Legal H p.toBoard c → ∀ h₁ A₁, Variant D H p.toBoard c .white h₁ A₁ →
    ¬ HasFour h₁ A₁ .white ∧
    (BoardFull h₁ A₁ ∨ ∃ e, Legal h₁ A₁ e ∧ ∀ h₂ A₂, Variant D h₁ A₁ e .black h₂ A₂ →
      HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, (I h₃ A₃ ∨ CL h₃ A₃) ∧ SEq D h₃ A₃ h₂ A₂) := by
  unfold stepOKS at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hwf, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  have hw := Pos.wfB_sound hwf
  intro c hl h₁ A₁ hv
  have : whiteOK D memf H p rep c.val = true := by
    fin_cases c
    exacts [h0, h1, h2, h3, h4]
  exact whiteOK_sound hD hm hw c this hl hv

/-! ## The tree -/

def SM : Nat := 618970019642690137449562111

def skeyOf (H : Nat) (p : Pos) : Nat :=
  (((((((((p.b0 * SM + p.b1) * SM + p.b2) * SM + p.b3) * SM + p.b4) * 131 +
    p.h0) * 131 + p.h1) * 131 + p.h2) * 131 + p.h3) * 131 + p.h4) * 131 + H

/-- Decode a key (no inverse property is needed). -/
def sunpack (k : Nat) : Nat × Pos :=
  let k0 := k / 131
  let k1 := k0 / 131
  let k2 := k1 / 131
  let k3 := k2 / 131
  let k4 := k3 / 131
  let k5 := k4 / 131
  let k6 := k5 / SM
  let k7 := k6 / SM
  let k8 := k7 / SM
  let k9 := k8 / SM
  (k % 131, ⟨k9, k8 % SM, k7 % SM, k6 % SM, k5 % SM, k4 % 131, k3 % 131, k2 % 131, k1 % 131, k0 % 131⟩)

def withSUnpack {α : Sort _} (k : Nat) (f : Nat → Pos → α) : α :=
  force (k / 131) fun k0 => force (k0 / 131) fun k1 => force (k1 / 131) fun k2 =>
  force (k2 / 131) fun k3 => force (k3 / 131) fun k4 => force (k4 / 131) fun k5 =>
  force (k5 / SM) fun k6 => force (k6 / SM) fun k7 => force (k7 / SM) fun k8 => force (k8 / SM) fun k9 =>
  force (k % 131) fun H =>
  forceP ⟨k9, k8 % SM, k7 % SM, k6 % SM, k5 % SM, k4 % 131, k3 % 131, k2 % 131, k1 % 131, k0 % 131⟩ fun p =>
  f H p

@[simp] theorem withSUnpack_eq {α : Sort _} (k : Nat) (f : Nat → Pos → α) :
    withSUnpack k f = f (sunpack k).1 (sunpack k).2 := by
  simp [withSUnpack, sunpack]

def SR : Nat := 9765625

/-- `SIn t H p rep`: the tree holds the abstract position `(H, p)` with reply word `rep`. -/
inductive CTree.SIn : CTree → Nat → Pos → Nat → Prop
  | here (l w r) : CTree.SIn (.node l w r) (sunpack (w / SR)).1 (sunpack (w / SR)).2 (w % SR)
  | left (l w r) {H p q} : CTree.SIn l H p q → CTree.SIn (.node l w r) H p q
  | right (l w r) {H p q} : CTree.SIn r H p q → CTree.SIn (.node l w r) H p q

def CTree.smemK : CTree → Nat → Nat → Pos → Bool
  | .leaf, _, _, _ => false
  | .node l w r, k, H, p =>
    force (w / SR) fun kq =>
    if k == kq then withSUnpack kq fun H' q => H' == H && q.beq p
    else if k < kq then l.smemK k H p else r.smemK k H p

def CTree.smemB (t : CTree) (H : Nat) (p : Pos) : Bool := force (skeyOf H p) fun k => t.smemK k H p

theorem CTree.smemK_sound : ∀ (t : CTree) (k H : Nat) (p : Pos), t.smemK k H p = true →
    ∃ rep, t.SIn H p rep
  | .leaf, _, _, _, h => by simp [CTree.smemK] at h
  | .node l w r, k, H, p, h => by
    unfold CTree.smemK at h
    rw [force_eq] at h
    by_cases h1 : (k == w / SR) = true
    · rw [if_pos h1, withSUnpack_eq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hH, hp⟩ := h
      have := Pos.eq_of_beq hp
      subst this; subst hH
      exact ⟨w % SR, .here l w r⟩
    · rw [if_neg h1] at h
      by_cases h2 : k < w / SR
      · rw [if_pos h2] at h
        obtain ⟨q, hq⟩ := CTree.smemK_sound l k H p h
        exact ⟨q, .left l w r hq⟩
      · rw [if_neg h2] at h
        obtain ⟨q, hq⟩ := CTree.smemK_sound r k H p h
        exact ⟨q, .right l w r hq⟩

theorem CTree.smemB_sound (t : CTree) (H : Nat) (p : Pos) (h : t.smemB H p = true) :
    ∃ rep, t.SIn H p rep := by
  unfold CTree.smemB at h; rw [force_eq] at h; exact CTree.smemK_sound t _ H p h

def CTree.sallOK (D : Nat) (memf : Nat → Pos → Bool) : CTree → Bool
  | .leaf => true
  | .node l w r => (withSUnpack (w / SR) fun H pos => stepOKS D memf H pos (w % SR)) &&
      l.sallOK D memf && r.sallOK D memf

theorem CTree.sallOK_sound {D : Nat} {memf : Nat → Pos → Bool} :
    ∀ (t : CTree), t.sallOK D memf = true → ∀ H p rep, t.SIn H p rep → stepOKS D memf H p rep = true
  | .leaf, _, _, _, _, hin => by cases hin
  | .node l w r, hall, H, p, q, hin => by
    unfold CTree.sallOK at hall
    simp only [Bool.and_eq_true, withSUnpack_eq] at hall
    cases hin with
    | here => exact hall.1.1
    | left _ _ _ hl => exact CTree.sallOK_sound l hall.1.2 H p q hl
    | right _ _ _ hr => exact CTree.sallOK_sound r hall.2 H p q hr

theorem sallOK_node {D : Nat} {memf : Nat → Pos → Bool} {l r : CTree} {w : Nat}
    (h1 : stepOKS D memf (sunpack (w / SR)).1 (sunpack (w / SR)).2 (w % SR) = true)
    (h2 : l.sallOK D memf = true) (h3 : r.sallOK D memf = true) :
    (CTree.node l w r).sallOK D memf = true := by
  unfold CTree.sallOK; rw [withSUnpack_eq, h1, h2, h3]; rfl

/-- The set of abstract positions held by a tree. -/
def CTree.SSet (t : CTree) (h : Nat) (A : Board 5) : Prop := ∃ p rep, t.SIn h p rep ∧ A = p.toBoard

theorem stretchCert_of_tree {D : Nat} (hD : 2 ≤ D) (t : CTree) (hall : t.sallOK D t.smemB = true) :
    StretchCertL D CL t.SSet := by
  rintro h A ⟨p, rep, hin, rfl⟩ c hl h₁ A₁ hv
  have hm : ∀ h q, t.smemB h q = true → t.SSet h q.toBoard := fun h q hq => by
    obtain ⟨rep, hr⟩ := t.smemB_sound h q hq
    exact ⟨q, rep, hr, rfl⟩
  exact stepOKS_sound hD hm (CTree.sallOK_sound t hall h p rep hin) c hl h₁ A₁ hv

/-- **Stretch certificates.**  A real board that is a stretch of a root held by a checked tree is safe
for Black. -/
theorem stretch_safe_of_tree {D : Nat} (hD : 2 ≤ D) (t : CTree) (hall : t.sallOK D t.smemB = true)
    {h : Nat} {q : Pos} (hq : t.smemB h q = true) {H : Nat} {R : Board 5} (htm : toMove R = .white)
    (hnw : ¬ HasFour H R .white) (hs : SEq D h q.toBoard H R) : Safe H R := by
  obtain ⟨rep, hr⟩ := t.smemB_sound h q hq
  exact stretch_safeL hD (claim_leafSound hD) (stretchCert_of_tree hD t hall) htm hnw ⟨q, rep, hr, rfl⟩ hs

#print axioms stretch_safe_of_tree

end C4W5
