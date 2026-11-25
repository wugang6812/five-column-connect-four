import LongThreatCheck
import C4W5.Cert.ClaimBits

namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5.ClaimBits
set_option maxHeartbeats 1500000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private theorem alt_bit' : ∀ n : Fin 64, alt.testBit n.val = decide (n.val % 2 = 0) := by
  decide +kernel

def protectionM (t rho mask : Nat) (p : Pos) (c : Nat) : Nat :=
  (if c = t ∨ mask.testBit c = true then alt <<< (p.ht c + 1) else 0) |||
  (if c = t then (2^64 - 1) <<< rho else 0)

def openMask (h : Nat) (p : Pos) (t rho mask c : Nat) : Nat :=
  (2^h - 1) ^^^ ((p.bm c ||| protectionM t rho mask p c) % 2^h)

def scan (h : Nat) (p : Pos) (t rho mask : Nat) : Bool :=
  force (openMask h p t rho mask 0) fun a => force (openMask h p t rho mask 1) fun b => force (openMask h p t rho mask 2) fun c =>
  force (openMask h p t rho mask 3) fun e => force (openMask h p t rho mask 4) fun f =>
  force (exceptionM h p 0) fun u => force (exceptionM h p 1) fun v => force (exceptionM h p 2) fun w =>
  force (exceptionM h p 3) fun z => force (exceptionM h p 4) fun z4 =>
  three a b c e u v w z && three b c e f v w z z4

private theorem window_contra {f g : Nat → Nat} {d x k i : Nat} (hi : i < 4)
    (hf : ∀ j : Fin 4, (f (x+j.val)).testBit (k+off d j.val) = true)
    (hg : (g (x+i)).testBit (k+off d i) = true)
    (hw : checkWindow d (f x) (f (x+1)) (f (x+2)) (f (x+3))
      (g x) (g (x+1)) (g (x+2)) (g (x+3)) = true) : False := by
  unfold checkWindow at hw
  have eq := beq_iff_eq.mp hw
  have no := congrArg (fun n : Nat => n.testBit k) eq
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  change (f x).testBit (k+off d 0) = true at h0
  change (f (x+1)).testBit (k+off d 1) = true at h1
  change (f (x+2)).testBit (k+off d 2) = true at h2
  change (f (x+3)).testBit (k+off d 3) = true at h3
  rw [Nat.add_comm k] at h0 h1 h2 h3 hg
  rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl | rfl | rfl | rfl <;>
    simp [live,hit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,h0,h1,h2,h3,hg, Nat.add_zero] at no <;> simp_all

private theorem window_at {h : Nat} {p : Pos} {t rho mask x d : Nat} (hx : x ≤ 1) (hd : d ≤ 2)
    (hscan : scan h p t rho mask = true) :
    let f := openMask h p t rho mask; let g := exceptionM h p
    checkWindow d (f x) (f (x+1)) (f (x+2)) (f (x+3)) (g x) (g (x+1)) (g (x+2)) (g (x+3)) = true := by
  simp only [scan, force_eq, three, Bool.and_eq_true] at hscan
  rcases (by omega : x=0 ∨ x=1) with rfl | rfl <;>
    rcases (by omega : d=0 ∨ d=1 ∨ d=2) with rfl | rfl | rfl
  exacts [hscan.1.1.1,hscan.1.1.2,hscan.1.2,hscan.2.1.1,hscan.2.1.2,hscan.2.2]


private theorem protect_sound {p : Pos} {t c : Fin 5} {rho mask y : Nat} (hy : y < 64)
    (hb : (protectionM t.val rho mask p c.val).testBit y = true) :
    Guard t rho (selected mask) (fun q => p.ht q.val) c.val y := by
  rw [protectionM, Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · by_cases hp : c.val = t.val ∨ mask.testBit c.val = true
    · rw [if_pos hp, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨hle,hbit⟩ := hb
      have hi : y - (p.ht c.val + 1) < 64 := by omega
      have ha := alt_bit' ⟨_,hi⟩
      change alt.testBit (y - (p.ht c.val + 1)) = _ at ha
      rw [ha, decide_eq_true_eq] at hbit
      change (y - (p.ht c.val + 1)) % 2 = 0 at hbit
      exact Or.inl ⟨c,hp.imp Fin.ext id,rfl,by dsimp; omega,by dsimp; omega⟩
    · simp [hp] at hb
  · by_cases he : c.val = t.val
    · rw [if_pos he, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
      exact Or.inr ⟨by omega,by omega⟩
    · simp [he] at hb

private theorem open_of_clear {h : Nat} {p : Pos} (hw : p.WF h) {t c : Fin 5} {rho mask y : Nat}
    (hy : y < h) (hh : h ≤ 64)
    (hn : ¬ (cellAtInt h p.toBoard c.val y = some .black ∨
      Guard t rho (selected mask) (fun q => p.ht q.val) c.val y)) :
    (openMask h p t.val rho mask c.val).testBit y = true := by
  have hbb : (p.bm c.val).testBit y = false := by
    cases hb : (p.bm c.val).testBit y with
    | false => rfl
    | true =>
      exfalso; apply hn; left; apply cellBlack_sound hw
      simp [cellBlack, hb, c.isLt, hy]
  have hgg : (protectionM t.val rho mask p c.val).testBit y = false := by
    cases hg : (protectionM t.val rho mask p c.val).testBit y with
    | false => rfl
    | true => exact (hn (Or.inr (protect_sound (by omega) hg))).elim
  simp [openMask, Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,
    Nat.testBit_or,hy,hbb,hgg]

theorem scan_sound {h : Nat} {p : Pos} (hw : p.WF h) (hh : h ≤ 64)
    {t c : Fin 5} {rho mask r : Nat}
    (hs : scan h p t.val rho mask = true)
    (he : (excB p c.val r || potB h p c.val r) = true) :
    deadCheck h p t rho mask c r := by
  intro d i
  by_contra hn
  have bad (j : Fin 4) :
      let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
      let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
      ¬ (cellAtInt h p.toBoard x y = some .black ∨
        Guard t rho (selected mask) (fun q => p.ht q.val) x y ∨
        ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (h : Int))) := by dsimp only; intro hj; exact hn ⟨j,hj⟩
  have coord (j : Fin 4) :
      let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
      let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
      0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (h : Int) := by
    by_contra hb; exact bad j (Or.inr (Or.inr hb))
  have h0 := coord 0
  have h3 := coord 3
  dsimp only at h0 h3
  simp only [Fin.val_zero, Fin.val_natCast, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at h0 h3
  have hi := i.isLt
  have hd := d.isLt
  have hic : i.val ≤ c.val := by omega
  have hx : c.val - i.val ≤ 1 := by omega
  have ds : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by omega
  have hr : off d.val i.val ≤ r := by
    rcases ds with h | h | h <;> simp [off,dyOf,h] at * <;> omega
  apply window_contra (f := openMask h p t.val rho mask) (g := exceptionM h p) (k := r-off d.val i.val)
    (i := i.val) hi _ _ (window_at (d := d.val) hx (by omega) hs)
  · intro j
    have hj := j.isLt
    have cj : c.val - i.val + j.val < 5 := by omega
    let z : Fin 5 := ⟨c.val - i.val + j.val,cj⟩
    let y := r-off d.val i.val + off d.val j.val
    have ex : (z.val : Int) = (c.val : Int) - (i : Int) * 1 + (j : Int) * 1 := by dsimp [z]; omega
    have ey : (y : Int) = (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val := by
      dsimp [y]; rcases ds with h | h | h <;> simp [off,dyOf,h] at * <;> omega
    have b := bad j
    have v := coord j
    dsimp only at b v
    have hy : y < h := by omega
    apply open_of_clear (t := t) (c := z) hw hy hh
    intro hh'
    rw [ex,ey] at hh'
    exact b (hh'.imp id Or.inl)
  · have e1 : c.val-i.val+i.val = c.val := by omega
    have e2 : r-off d.val i.val + off d.val i.val = r := by omega
    simpa only [e1,e2] using exc_bit (h := h) he


def BitBase (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) : Prop :=
  H ≤ 64 ∧ H % 2 = 0 ∧ p.wfB H = true ∧ ¬ selected mask t ∧
  (H - p.ht t.val) % 2 = 1 ∧
  (∀ q : Fin 5, selected mask q → (H - p.ht q.val) % 2 = 0) ∧
  p.ht t.val < rho ∧ rho < H ∧ (rho - p.ht t.val) % 2 = 1 ∧
  ∀ c : Fin 5, ntrB H p c.val = true

instance (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) :
    Decidable (BitBase H p t rho mask) := by unfold BitBase; infer_instance

def tripleBits (H : Nat) (p : Pos) (t : Fin 5) (rho : Nat) (d : Fin 3) (i : Fin 4) : Bool :=
  decide (∀ j : Fin 4, j ≠ i →
    cellBlack H p ((t.val : Int) - (i : Int) * 1 + (j : Int) * 1)
      ((rho : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val) = true)

def checkBits (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (d : Fin 3) (i : Fin 4) : Bool :=
  decide (BitBase H p t rho mask) && tripleBits H p t rho d i && scan H p t.val rho mask

theorem ntrB_sound' {H : Nat} {p : Pos} {c : Fin 5} (hn : ntrB H p c.val = true)
    (hl : p.ht c.val < H) : ¬ TopThree p.toBoard c := by
  intro ht
  unfold ntrB at hn
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hn
  obtain ⟨t0,t1,t2,t3⟩ := ht
  rw [Pos.height] at t0 t1 t2 t3
  have b1 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t1).2
  have b2 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t2).2
  have b3 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t3).2
  rcases hn with hn | hn
  · rw [show (p.ht c.val).blt H = true from Nat.blt_eq.mpr hl] at hn
    cases hn
  · rw [show Nat.ble 3 (p.ht c.val) = true from Nat.ble_eq.mpr t0,b1,b2,b3] at hn
    cases hn

theorem checkBits_reference {H : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat} {d : Fin 3} {i : Fin 4}
    (h : checkBits H p t rho mask d i = true) : check H p t rho mask d i = true := by
  simp only [checkBits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hh,he,hw,hn,ho,hq,hg,hl,hp,ht⟩,htr⟩,hs⟩ := h
  have hW := Pos.wfB_sound hw
  have ht' : tripleCheck H p t rho d i := by
    have hb := of_decide_eq_true htr
    intro j hj; exact cellBlack_sound hW (hb j hj)
  apply decide_eq_true
  exact ⟨he,hw,hn,ho,hq,hg,hl,hp,fun c hc => ntrB_sound' (ht c) hc,ht',
    fun c r hr => scan_sound hW hh hs (by rw [Bool.or_eq_true]; exact hr)⟩

theorem checkBits_sound {H : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat} {d : Fin 3} {i : Fin 4}
    (h : checkBits H p t rho mask d i = true) : Hyp H p.toBoard t rho (selected mask) :=
  check_sound (checkBits_reference h)

theorem exampleBitsChecked : checkBits 10 examplePos 4 8 1 0 3 = true := by decide +kernel
#print axioms checkBits_sound
#print axioms exampleBitsChecked
end C4W5.LongThreat
