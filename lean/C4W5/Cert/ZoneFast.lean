import C4W5.Cert.ClaimBits
import C4W5.Cert.QuickNorm

namespace C4W5.ZoneFast
open C4W5
abbrev Mem := Nat → Pos → Lab5 → Bool

def terminalMem (f : Mem) (k : Nat) (p : Pos) (l : Lab5) : Bool := f k p l || ClaimBits.fast k p

private theorem terminal_eq (f : Mem) (k : Nat) (p : Pos) (l : Lab5) :
    (terminalMem f k p l || claimB k p) = (f k p l || claimB k p) := by
  unfold terminalMem
  cases he : ClaimBits.fast k p with
  | false => simp
  | true => simp [ClaimBits.fast_sound he]

private theorem out_eq (D : Nat) (f : Mem) (k : Nat) (p : Pos) (l : Lab5) (e : Nat) :
    szOut D (terminalMem f) k p l e = szOut D f k p l e := by
  simp only [szOut,szBlackLow,szTarget,force_eq,forceP_eq,withNorm_eq,terminal_eq]

def blackLow (D : Nat) (f : Mem) (k : Nat) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  (varsF D k p e .black).all fun v => forceP v.2 fun b => b.hasFourQ .black ||
    QuickNorm.checked D v.1 b e (fun j q => terminalMem f j q l)

def out (D : Nat) (f : Mem) (k : Nat) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  force (l.get e) fun le =>
  if le = 0 then
    if p.ht e < k then blackLow D f k p l e else terminalMem f k p (l.set e 1)
  else if le = 1 then terminalMem f k p (l.set e 2) else false

private theorem target_sound {f : Mem} {k : Nat} {p : Pos} {l : Lab5}
    (h : terminalMem f k p l = true) : szTarget f k p l = true := by
  unfold szTarget; rw [← terminal_eq]; simp [h]

private theorem out_sound {D : Nat} {f : Mem} {k : Nat} {p : Pos} {l : Lab5} {e : Nat}
    (h : out D f k p l e = true) : szOut D f k p l e = true := by
  unfold out at h; unfold szOut
  simp only [force_eq] at *
  split at h <;> rename_i he <;> simp only [he,if_true,if_false] at *
  · split at h <;> rename_i hk <;> simp only [hk,if_true,if_false] at *
    · unfold blackLow at h; unfold szBlackLow
      simp only [List.all_eq_true, forceP_eq, QuickNorm.checked_eq, withNorm_eq, Bool.or_eq_true] at *
      intro v hv; rcases h v hv with hf | ht
      · exact Or.inl hf
      · exact Or.inr (by simpa only [szTarget, Bool.or_eq_true] using target_sound ht)
    · exact target_sound h
  · split at h <;> rename_i hl <;> simp only [hl,if_true,if_false] at *
    · exact target_sound h
    · exact h

def checkV (D : Nat) (f : Mem) (l : Lab5) (free : Bool) (c e : Nat) (v : Nat × Pos) :=
  forceP v.2 fun p => !p.hasFourQ .white && QuickNorm.checked D v.1 p c fun k n =>
    if e == c || free then out D f k n l e else szWin D k n l e

private theorem checkV_sound {D : Nat} {f : Mem} {l : Lab5} {free : Bool} {c e : Nat} {v : Nat × Pos}
    (hv : checkV D f l free c e v = true) : szCheckV D f l free c e v = true := by
  unfold checkV at hv; unfold szCheckV
  simp only [forceP_eq, QuickNorm.checked_eq, withNorm_eq, Bool.and_eq_true] at *
  refine ⟨hv.1, ?_⟩
  cases he : (e == c || free) with
  | false => simpa [he] using hv.2
  | true => simp only [he, Bool.true_and, if_true] at *; simp [out_sound hv.2]

def col (D : Nat) (f : Mem) (k : Nat) (p : Pos) (l : Lab5) (rep c lm : Nat) :=
  force (l.get c) fun lc =>
  if lc = 0 then
    if p.ht c < k then
      checkV D f l (Nat.ble (p.ht c+5) k) c (replyOf rep (2*c)) (k,p.push c .white) &&
        (if clearM D k lm (p.ht c+D+1) && !clearM D k lm (p.ht c+D+2) then
          checkV D f l (Nat.ble (p.ht c+5) k) c (replyOf rep (2*c+1))
            (k+2,(stretchPos p (p.ht c+D+1)).push c .white) else true)
    else terminalMem f k p (l.set c 2)
  else if lc = 1 then (l.set c 2).allDead || out D f k p (l.set c 2) (replyOf rep (2*c))
  else true

private theorem col_sound {D : Nat} {f : Mem} {k : Nat} {p : Pos} {l : Lab5} {rep c : Nat}
    (hc : col D f k p l rep c (p.LM k) = true) : szCol D f k p l rep c = true := by
  unfold col at hc; unfold szCol
  simp only [force_eq] at *
  split at hc <;> rename_i hl <;> simp only [hl,if_true,if_false] at *
  · split at hc <;> rename_i hh <;> simp only [hh,if_true,if_false] at *
    · rw [Bool.and_eq_true] at hc ⊢
      refine ⟨checkV_sound hc.1, ?_⟩
      split <;> rename_i hv <;> simp only [hv,if_true,if_false] at hc
      · exact checkV_sound hc.2
      · rfl
    · unfold szTarget; rw [← terminal_eq]; simp [hc]
  · split at hc <;> rename_i ho <;> simp only [ho,if_true,if_false] at *
    · rw [Bool.or_eq_true] at hc
      rcases hc with hd | hout
      · simp [hd]
      · simp [out_sound hout]

def step (D : Nat) (f : Mem) (k : Nat) (p : Pos) (l : Lab5) (rep : Nat) :=
  p.wfB k && (force (p.LM k) fun lm => col D f k p l rep 0 lm && col D f k p l rep 1 lm &&
    col D f k p l rep 2 lm && col D f k p l rep 3 lm && col D f k p l rep 4 lm)

theorem step_sound {D : Nat} {f : Mem} {k : Nat} {p : Pos} {l : Lab5} {rep : Nat}
    (h : step D f k p l rep = true) : stepOKSZ D f k p l rep = true := by
  unfold step at h; unfold stepOKSZ
  simp only [force_eq, Bool.and_eq_true] at *
  obtain ⟨hw, ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩⟩ := h
  exact ⟨⟨⟨⟨⟨hw,col_sound h0⟩, col_sound h1⟩, col_sound h2⟩, col_sound h3⟩, col_sound h4⟩

def tree (D : Nat) (f : Mem) : CTree → Bool
  | .leaf => true
  | .node left w right => (withSUnpack (w / SR / 243) fun k p => step D f k p (unpackL (w / SR % 243)) (w % SR)) &&
      tree D f left && tree D f right

theorem tree_sound {D : Nat} {f : Mem} {t : CTree} (h : tree D f t = true) : t.szallOK D f = true := by
  induction t with
  | leaf => rfl
  | node l w r il ir =>
    simp only [tree, withSUnpack_eq, Bool.and_eq_true] at h
    exact szallOK_node (step_sound h.1.1) (il h.1.2) (ir h.2)

#print axioms tree_sound
end C4W5.ZoneFast
