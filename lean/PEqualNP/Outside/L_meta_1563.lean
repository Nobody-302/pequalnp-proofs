import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563_aux

-- The inputs on 13 wires, numbered 0 to 8191 (wire i is binary digit i).
def E : Fin 8192 ≃ (Fin 13 → Bool) :=
  (finFunctionFinEquiv (m := 2) (n := 13)).symm.trans (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv)

theorem forall_E (R : (Fin 13 → Bool) → Prop) : (∀ x, R x) ↔ ∀ n, R (E n) := by
  constructor
  · intro h n
    exact h _
  · intro h x
    have := h (E.symm x)
    rwa [Equiv.apply_symm_apply] at this

theorem card_E (R : (Fin 13 → Bool) → Prop) [DecidablePred R] :
    (Finset.univ.filter R).card = (Finset.univ.filter (fun n => R (E n))).card := by
  refine Finset.card_bij (fun x _ => E.symm x) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro a _ b _ h
    exact E.symm.injective h
  · intro n hn
    exact ⟨E n, by simpa using hn, by simp⟩

theorem forall_of_card (R : Fin 8192 → Prop) [DecidablePred R]
    (h : (Finset.univ.filter (fun n => ¬ R n)).card = 0) : ∀ n, R n := by
  intro n
  by_contra hn
  have hmem : n ∈ Finset.univ.filter (fun n => ¬ R n) := by simp [hn]
  rw [Finset.card_eq_zero] at h
  simp [h] at hmem

end PEqualNP.Outside.L_meta_1563_aux

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have hL' : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  subst hL'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr fun v hv => hxy _ (h v hv))
  · rw [PEqualNP.Outside.L_meta_1563_aux.card_E]
    decide +kernel
  · decide +kernel
  · rw [PEqualNP.Outside.L_meta_1563_aux.card_E]
    decide +kernel
  · rw [PEqualNP.Outside.L_meta_1563_aux.forall_E]
    apply PEqualNP.Outside.L_meta_1563_aux.forall_of_card
    decide +kernel
