import C4W5.Cert.ZoneC

/-! Fixed-size packed blocks indexed by a decision tree. A lookup hit carries a
semantic witness derived from the bytes, not from correctness of the routing keys. -/
namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

inductive Bank where
  | block (count payload : Nat)
  | window (count localRadix bias payload : Nat)
  | branch (cut : Nat) (left right : Bank)

def rowAt (radix payload i : Nat) : Nat := (payload / radix ^ i) % radix

inductive Contains (radix : Nat) : Bank → Nat → Prop where
  | atRow (n payload i : Nat) (hi : i < n) :
      Contains radix (.block n payload) (rowAt radix payload i)
  | atWindow (n localRadix bias payload i : Nat) (hi : i < n) :
      Contains radix (.window n localRadix bias payload) (bias + rowAt localRadix payload i)
  | left (cut : Nat) (l r : Bank) (w : Nat) (hw : Contains radix l w) :
      Contains radix (.branch cut l r) w
  | right (cut : Nat) (l r : Bank) (w : Nat) (hw : Contains radix r w) :
      Contains radix (.branch cut l r) w

def seek (get : Nat → Nat) (repBase key : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, lo, hi =>
    if lo < hi then
      force (lo + (hi - lo) / 2) fun mid =>
      force (get mid) fun w =>
        if w / repBase = key then some w
        else if key < w / repBase then seek get repBase key fuel lo mid
        else seek get repBase key fuel (mid+1) hi
    else none

theorem seek_sound {get : Nat → Nat} {r key f lo hi w : Nat}
    (h : seek get r key f lo hi = some w) :
    ∃ i, lo ≤ i ∧ i < hi ∧ get i = w := by
  induction f generalizing lo hi with
  | zero => simp [seek] at h
  | succ f ih =>
      simp only [seek, force_eq] at h
      split at h
      next hlen =>
        have hlo : lo ≤ lo + (hi - lo) / 2 := by omega
        have hhi : lo + (hi - lo) / 2 < hi := by omega
        split at h
        next =>
          exact ⟨_, hlo, hhi, Option.some.inj h⟩
        next =>
          split at h
          next =>
            obtain ⟨i, a, b, e⟩ := ih h
            exact ⟨i, a, by omega, e⟩
          next =>
            obtain ⟨i, a, b, e⟩ := ih h
            exact ⟨i, by omega, b, e⟩
      next => cases h

def find (radix repBase key : Nat) : Bank → Option Nat
  | .block n p => seek (rowAt radix p) repBase key 8 0 n
  | .window n a b p => seek (fun i => b + rowAt a p i) repBase key 8 0 n
  | .branch cut l r =>
    if key < cut then find radix repBase key l else find radix repBase key r

theorem find_sound {a r k : Nat} {bank : Bank} {w : Nat} (h : find a r k bank = some w) :
    Contains a bank w := by
  induction bank with
  | block n p =>
      obtain ⟨i, _, hi, e⟩ := seek_sound h
      rw [← e]
      exact .atRow n p i hi
  | window n a' b p =>
      obtain ⟨i, _, hi, e⟩ := seek_sound h
      rw [← e]
      exact .atWindow n a' b p i hi
  | branch cut l r hl hr =>
      simp only [find] at h
      split at h
      · exact .left cut l r w (hl h)
      · exact .right cut l r w (hr h)

def all (radix : Nat) (test : Nat → Bool) : Bank → Bool
  | .block n payload => (List.range n).all fun i => test (rowAt radix payload i)
  | .window n a b payload => (List.range n).all fun i => test (b + rowAt a payload i)
  | .branch _ l r => all radix test l && all radix test r

theorem all_sound {radix : Nat} {test : Nat → Bool} {bank : Bank} {w : Nat}
    (h : all radix test bank = true) (hw : Contains radix bank w) : test w = true := by
  induction hw with
  | atRow n p i hi =>
      simp only [all, List.all_eq_true] at h
      exact h _ (List.mem_range.mpr hi)
  | atWindow n a b p i hi =>
      simp only [all, List.all_eq_true] at h
      exact h _ (List.mem_range.mpr hi)
  | left cut l r w hw ih =>
      simp only [all, Bool.and_eq_true] at h
      exact ih h.1
  | right cut l r w hw ih =>
      simp only [all, Bool.and_eq_true] at h
      exact ih h.2

theorem all_branch {radix cut : Nat} {test : Nat → Bool} {l r : Bank}
    (hl : all radix test l = true) (hr : all radix test r = true) :
    all radix test (.branch cut l r) = true := by
  simp [all, hl, hr]

structure ZFormat where
  radix : Nat
  repBase : Nat
  key : Pos → Lab5 → Nat
  pos : Nat → Pos
  labels : Nat → Lab5

def zrel (F : ZFormat) (t : Bank) (A : Board 5) (ls : Fin 5 → Lab) : Prop :=
  ∃ w, Contains F.radix t w ∧ A = (F.pos w).toBoard ∧ ls = (F.labels w).fn

def zmem (F : ZFormat) (t : Bank) (pos : Pos) (ls : Lab5) : Bool :=
  force (F.key pos ls) fun key =>
    match find F.radix F.repBase key t with
    | none => false
    | some w => (F.pos w).beq pos && (F.labels w).beq ls

theorem zmem_sound {F : ZFormat} {t : Bank} {p : Pos} {ls : Lab5} (h : zmem F t p ls = true) :
    zrel F t p.toBoard ls.fn := by
  simp only [zmem, force_eq] at h
  split at h
  · cases h
  next w ew =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨hp, hl⟩ := h
    have ep := Pos.eq_of_beq hp
    have el := Lab5.eq_of_beq hl
    exact ⟨w, find_sound ew, congrArg Pos.toBoard ep.symm, congrArg Lab5.fn el.symm⟩

def zcheckRow (K : Nat) (F : ZFormat) (t : Bank) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    stepOKZ K (zmem F t) p (F.labels w) (w % F.repBase)

theorem zoneCert_of_bank {K : Nat} (F : ZFormat) (t : Bank)
    (hall : all F.radix (zcheckRow K F t) t = true) : ZoneCert K (zrel F t) := by
  rintro A l ⟨w, hw, rfl, rfl⟩ c
  have hh := all_sound hall hw
  simp only [zcheckRow, force_eq, forceP_eq] at hh
  exact stepOKZ_sound (I := zrel F t) (fun _ _ h => zmem_sound h) hh c

theorem zone_bank_safe {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    (F : ZFormat) (t : Bank) (hall : all F.radix (zcheckRow K F t) t = true)
    (q : Pos) (hwf : q.WF K) (hodd : q.total % 2 = 1)
    (hnw : ¬ HasFour K q.toBoard .white) (hnb : ¬ HasFour K q.toBoard .black)
    (hd : q.discB K = true) (hmem : zmem F t q ⟨0, 0, 0, 0, 0⟩ = true) : Safe H q.toBoard := by
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
  have hrel := zmem_sound hmem
  apply zone_safe hK hH hKH (zoneCert_of_bank F t hall)
  exact
    { tm := by unfold toMove; rw [Pos.totalStones_eq, if_neg (by omega)]
      nw := fun hf => hnw (hfourK _ hf)
      nb := fun hf => hnb (hfourK _ hf)
      dE := hE
      dT := hT
      valid := fun c => by rw [Pos.height]; exact (hwH c.val).2
      abs := Or.inl (by
        rw [htrunc]
        have heq : labs H K q.toBoard = (⟨0, 0, 0, 0, 0⟩ : Lab5).fn := by
          funext c
          simp only [labs, labOf, Lab5.fn]
          rw [if_pos (by rw [Pos.height]; exact (hwf c.val).2)]
          fin_cases c <;> rfl
        rw [heq]
        exact hrel) }

theorem zone_safe_of_bank {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    (F : ZFormat) (t : Bank) (ms : List (Fin 5)) (q : Pos) (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : all F.radix (zcheckRow K F t) t = true) (hodd : q.total % 2 = 1) (hd : q.discB K = true)
    (hmem : zmem F t q ⟨0, 0, 0, 0, 0⟩ = true) : Safe H (playList (emptyBoard 5) .black ms) := by
  obtain ⟨e, hnw, hnb, hwf⟩ := root_of_run' hr
  rw [← e]
  exact zone_bank_safe hK hH hKH F t hall q hwf hodd hnw hnb hd hmem

#print axioms zone_safe_of_bank

end C4W5.WindowBank
