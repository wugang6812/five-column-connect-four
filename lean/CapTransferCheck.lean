import CapTransferStretch
import LongThreatCheck

/-! Bounded reference gate draft, source-only. Requires Lean elaboration before
    use. Fast packed-mask integration is deliberately outside this module. -/
namespace C4W5.CapTransfer
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5.LongThreat (selected tripleCheck tripleCheck_sound)
set_option linter.deprecated false

instance (t : Fin 5) (mask : Nat) : DecidablePred (protect t (selected mask)) := by
  intro q; unfold protect; infer_instance

def GateGuard (phaseB : Bool) (p : Pos) (t s : Fin 5) (a b mask : Nat) (x y : Int) : Prop :=
  if phaseB then PostGuard t s a b (selected mask) (fun q => p.ht q.val) x y
  else LongThreat.Guard s a (protect t (selected mask)) (fun q => p.ht q.val) x y

instance (phaseB : Bool) (p : Pos) (t s : Fin 5) (a b mask : Nat) (x y : Int) :
    Decidable (GateGuard phaseB p t s a b mask x y) := by
  cases phaseB <;> dsimp [GateGuard,PostGuard,LongThreat.Guard] <;> infer_instance

def WindowCheck (phaseB : Bool) (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat)
    (c : Fin 5) (r : Nat) : Prop :=
  ∀ d : Fin 3, ∀ i : Fin 4, ∃ j : Fin 4,
    let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
    let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
    cellAtInt H p.toBoard x y = some .black ∨ GateGuard phaseB p t s a b mask x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int))

instance (phaseB : Bool) (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat) (c : Fin 5) (r : Nat) :
    Decidable (WindowCheck phaseB H p t s a b mask c r) := by
  unfold WindowCheck; infer_instance

private theorem dy_coverage {dy : Int} (hh : dy ∈ ([0,1,-1] : List Int)) :
    ∃ d : Fin 3, dyOf d.val = dy := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

theorem window_a_sound {H : Nat} {p : Pos} {t s c : Fin 5} {a b mask r : Nat}
    (h : WindowCheck false H p t s a b mask c r) :
    LongThreat.Dead H p.toBoard s a (protect t (selected mask))
      (fun q => (p.toBoard q).length) c r := by
  intro dy hdy i
  obtain ⟨d,hd⟩ := dy_coverage hdy
  have hp : (fun q => (p.toBoard q).length) = (fun q : Fin 5 => p.ht q.val) := by
    funext q; exact Pos.height p q
  rw [hp, ← hd]
  exact h d i

theorem window_b_sound {H : Nat} {p : Pos} {t s c : Fin 5} {a b mask r : Nat}
    (h : WindowCheck true H p t s a b mask c r) :
    PostDead H p.toBoard t s a b (selected mask) (fun q => (p.toBoard q).length) c r := by
  intro dy hdy i
  obtain ⟨d,hd⟩ := dy_coverage hdy
  have hp : (fun q => (p.toBoard q).length) = (fun q : Fin 5 => p.ht q.val) := by
    funext q; exact Pos.height p q
  rw [hp, ← hd]
  exact h d i

def CheckProp (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat)
    (dA dB : Fin 3) (iA iB : Fin 4) : Prop :=
  H % 2 = 0 ∧ p.wfB H = true ∧ s ≠ t ∧
  ¬ selected mask t ∧ ¬ selected mask s ∧
  p.ht t.val % 2 = 1 ∧ p.ht s.val % 2 = 0 ∧
  (∀ q : Fin 5, selected mask q → p.ht q.val % 2 = 0) ∧
  p.ht s.val < a ∧ a < b ∧ b < H ∧
  (a - p.ht s.val) % 2 = 1 ∧ b % 2 = p.ht s.val % 2 ∧
  (∀ c : Fin 5, p.ht c.val < H → ¬ TopThree p.toBoard c) ∧
  tripleCheck H p s a dA iA ∧ tripleCheck H p s b dB iB ∧
  (∀ c : Fin 5, ∀ r : Fin (H+1),
    excB p c.val r.val = true ∨ potB H p c.val r.val = true →
      WindowCheck false H p t s a b mask c r.val ∧ WindowCheck true H p t s a b mask c r.val)

instance (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat)
    (dA dB : Fin 3) (iA iB : Fin 4) :
    Decidable (CheckProp H p t s a b mask dA dB iA iB) := by
  unfold CheckProp; infer_instance

def check (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat)
    (dA dB : Fin 3) (iA iB : Fin 4) : Bool :=
  decide (CheckProp H p t s a b mask dA dB iA iB)

theorem check_sound {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4}
    (h : check H p t s a b mask dA dB iA iB = true) :
    Hyp H p.toBoard t s a b (selected mask) := by
  have hh : CheckProp H p t s a b mask dA dB iA iB := of_decide_eq_true h
  obtain ⟨he,hwf,hne,hnotT,hnotS,ot,es,hQ,ha,hab,hb,haO,hbe,hntr,hA,hB,hscan⟩ := hh
  have hw := Pos.wfB_sound hwf
  have scanAt (c : Fin 5) (r : Nat) (hx : Exceptional p.toBoard c r ∨ PotExc H p.toBoard c r) :
      WindowCheck false H p t s a b mask c r ∧ WindowCheck true H p t s a b mask c r := by
    have hr : r < H+1 := by
      rcases hx with hx | hx
      · have hlt := stone_bound _ _ _ hx.1
        rw [Pos.height] at hlt
        have := (hw c.val).2
        omega
      · obtain ⟨rfl,hlt,_⟩ := hx
        omega
    apply hscan c ⟨r,hr⟩
    exact hx.imp excB_complete potB_complete
  refine ⟨he,?_,hne,hnotT,hnotS,?_,?_,?_,?_,hab,hb,?_,?_,?_,
    tripleCheck_sound hA,tripleCheck_sound hB,?_,?_⟩
  · intro c; rw [Pos.height]; exact (hw c.val).2
  · simpa only [Pos.height] using ot
  · simpa only [Pos.height] using es
  · intro q hq; simpa only [Pos.height] using hQ q hq
  · simpa only [Pos.height] using ha
  · simpa only [Pos.height] using haO
  · simpa only [Pos.height] using hbe
  · intro c hlt
    exact hntr c (by simpa only [Legal,Pos.height] using hlt)
  · intro c r hex
    exact window_a_sound (scanAt c r hex).1
  · intro c r hex
    exact window_b_sound (scanAt c r hex).2

theorem check_leaf {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4}
    (h : check H p t s a b mask dA dB iA iB = true) : L H p.toBoard :=
  ⟨t,s,a,b,selected mask,check_sound h⟩

#print axioms check_leaf

end C4W5.CapTransfer
