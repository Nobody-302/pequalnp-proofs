import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of a circuit: append the value of the next gate.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_start : ∀ (gs : List Gate) (w : List Bool),
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_start gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    show List.foldl step (step w g) gs = w ++ (g.op.eval (g.inputs.map fun i => w.getD i false) :: t)
    rw [ht]
    simp [step]

theorem fold_getD (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_start gs w
  rw [ht, List.length_append, hl]

-- Where the ten inputs of the small circuit go among the fourteen inputs.
def tbl : List ℕ := [0, 1, 2, 3, 5, 6, 7, 8, 9, 12]

-- The wire renaming: inputs through the table, gate wires up by four.
def rm (w : ℕ) : ℕ := if w < 10 then tbl.getD w 0 else w + 4

theorem rm_small (w : ℕ) (h : w < 10) : rm w < 14 := by
  unfold rm
  rw [if_pos h]
  interval_cases w <;> simp [tbl]

theorem rm_big (w : ℕ) (h : ¬ w < 10) : rm w = w + 4 := by
  unfold rm
  rw [if_neg h]

theorem rm_lt (w k : ℕ) (h : w < 10 + k) : rm w < 14 + k := by
  by_cases hw : w < 10
  · have := rm_small w hw
    omega
  · rw [rm_big w hw]
    omega

theorem rm_inj : Function.Injective rm := by
  intro a b hab
  by_cases ha : a < 10 <;> by_cases hb : b < 10
  · unfold rm at hab
    rw [if_pos ha, if_pos hb] at hab
    interval_cases a <;> interval_cases b <;> simp_all [tbl]
  · have := rm_small a ha
    rw [rm_big b hb] at hab
    omega
  · have := rm_small b hb
    rw [rm_big a ha] at hab
    omega
  · rw [rm_big a ha, rm_big b hb] at hab
    omega

def sh (g : Gate) : Gate := ⟨g.op, g.inputs.map rm⟩

theorem shift_fold : ∀ (gs : List Gate) (k : ℕ) (w1 w4 : List Bool),
    w1.length = 10 + k → w4.length = 14 + k →
    (∀ w < 10 + k, w4.getD (rm w) false = w1.getD w false) →
    (∀ i < gs.length, ∀ a ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, a < 10 + k + i) →
    ∀ w < 10 + k + gs.length,
      ((gs.map sh).foldl step w4).getD (rm w) false = (gs.foldl step w1).getD w false
  | [], k, w1, w4, _, _, h, _ => by
    intro w hw
    simp only [List.map_nil, List.foldl_nil]
    exact h w (by simpa using hw)
  | g :: gs, k, w1, w4, h1, h4, h, hr => by
    have hg : ∀ a ∈ g.inputs, a < 10 + k := by
      intro a ha
      have := hr 0 (by simp) a (by simpa using ha)
      omega
    have hv : (g.inputs.map rm).map (fun i => w4.getD i false) =
        g.inputs.map (fun i => w1.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact h a (hg a ha)
    have key := shift_fold gs (k + 1) (step w1 g) (step w4 (sh g))
      (by simp [step, h1]; omega) (by simp [step, h4]; omega)
      (by
        intro w hw
        by_cases hlt : w < 10 + k
        · have hr4 := rm_lt w k hlt
          simp only [step]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact h w hlt
        · have hwe : w = 10 + k := by omega
          subst hwe
          rw [rm_big _ (by omega)]
          simp only [step, sh]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          rw [show 10 + k + 4 - w4.length = 0 by omega, show 10 + k - w1.length = 0 by omega]
          simp only [List.getD_cons_zero]
          rw [hv])
      (by
        intro i hi a ha
        have := hr (i + 1) (by simp; omega) a (by simpa using ha)
        omega)
    intro w hw
    simp only [List.map_cons, List.foldl_cons]
    exact key w (by simp at hw; omega)

-- Three stars: centre 10 on 0, 4, 5; centre 11 on 3, 4, 6; centre 13 on 1, 2, 4; then two ORs.
def stars (L : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [L, 5]⟩, ⟨GateOp.and, [10, L + 1]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [L + 3, 6]⟩, ⟨GateOp.and, [11, L + 4]⟩,
   ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [L + 6, 4]⟩, ⟨GateOp.and, [13, L + 7]⟩,
   ⟨GateOp.or, [L + 2, L + 5]⟩, ⟨GateOp.or, [L + 9, L + 8]⟩]

theorem stars_length (L : ℕ) : (stars L).length = 11 := rfl

theorem app_lt (W t : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ t).getD i false = W.getD i false := List.getD_append _ _ _ _ h

theorem app_len (W t : List Bool) (j : ℕ) : (W ++ t).getD (W.length + j) false = t.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem app_len0 (W t : List Bool) : (W ++ t).getD W.length false = t.getD 0 false := by
  simpa using app_len W t 0

theorem stars_val (W : List Bool) (h14 : 14 ≤ W.length) :
    ((stars W.length).foldl step W).getD (W.length + 10) false =
      (((W.getD 10 false && ((W.getD 0 false || W.getD 4 false) || W.getD 5 false)) ||
        (W.getD 11 false && ((W.getD 3 false || W.getD 4 false) || W.getD 6 false))) ||
        (W.getD 13 false && ((W.getD 1 false || W.getD 2 false) || W.getD 4 false))) := by
  have h0 : 0 < W.length := by omega
  have h1 : 1 < W.length := by omega
  have h2 : 2 < W.length := by omega
  have h3 : 3 < W.length := by omega
  have h4 : 4 < W.length := by omega
  have h5 : 5 < W.length := by omega
  have h6 : 6 < W.length := by omega
  have h10 : 10 < W.length := by omega
  have h11 : 11 < W.length := by omega
  have h13 : 13 < W.length := by omega
  simp only [stars, List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
    GateOp.eval, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    app_len, app_len0, app_lt _ _ _ h0, app_lt _ _ _ h1, app_lt _ _ _ h2, app_lt _ _ _ h3,
    app_lt _ _ _ h4, app_lt _ _ _ h5, app_lt _ _ _ h6, app_lt _ _ _ h10, app_lt _ _ _ h11,
    app_lt _ _ _ h13, List.getD_cons_zero, List.getD_cons_succ, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true]

theorem edges_eq (x : Fin 14 → Bool) :
    (((x 10 && ((x 0 || x 4) || x 5)) || (x 11 && ((x 3 || x 4) || x 6))) ||
        (x 13 && ((x 1 || x 2) || x 4))) =
      decide (∃ (a : Fin 14) (b : Fin 14), ((a : ℕ), (b : ℕ)) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)),
        ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)),
        ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x a = true ∧ x b = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨h10, (h0 | h4) | h5⟩ | ⟨h11, (h3 | h4) | h6⟩) | ⟨h13, (h1 | h2) | h4⟩)
    · exact ⟨0, 10, by decide, h0, h10⟩
    · exact ⟨4, 10, by decide, h4, h10⟩
    · exact ⟨5, 10, by decide, h5, h10⟩
    · exact ⟨3, 11, by decide, h3, h11⟩
    · exact ⟨4, 11, by decide, h4, h11⟩
    · exact ⟨6, 11, by decide, h6, h11⟩
    · exact ⟨1, 13, by decide, h1, h13⟩
    · exact ⟨2, 13, by decide, h2, h13⟩
    · exact ⟨4, 13, by decide, h4, h13⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hm, hxa, hxb⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all


theorem stars_mem (L : ℕ) (g : Gate) (hg : g ∈ stars L) :
    g = ⟨GateOp.or, [0, 4]⟩ ∨ g = ⟨GateOp.or, [L, 5]⟩ ∨ g = ⟨GateOp.and, [10, L + 1]⟩ ∨
    g = ⟨GateOp.or, [3, 4]⟩ ∨ g = ⟨GateOp.or, [L + 3, 6]⟩ ∨ g = ⟨GateOp.and, [11, L + 4]⟩ ∨
    g = ⟨GateOp.or, [1, 2]⟩ ∨ g = ⟨GateOp.or, [L + 6, 4]⟩ ∨ g = ⟨GateOp.and, [13, L + 7]⟩ ∨
    g = ⟨GateOp.or, [L + 2, L + 5]⟩ ∨ g = ⟨GateOp.or, [L + 9, L + 8]⟩ := by
  simpa [stars] using hg

theorem stars_ops (L : ℕ) : ∀ g ∈ stars L, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  rcases stars_mem L g hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem stars_len (L : ℕ) : ∀ g ∈ stars L, g.inputs.length = 2 := by
  intro g hg
  rcases stars_mem L g hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem stars_nodup (L : ℕ) (hL : 14 ≤ L) : ∀ g ∈ stars L, g.inputs.Nodup := by
  intro g hg
  rcases stars_mem L g hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp <;> omega

theorem stars_reads (L : ℕ) (hL : 14 ≤ L) :
    ∀ k < 11, ∀ i ∈ ((stars L).getD k ⟨GateOp.or, []⟩).inputs, i < L + k := by
  intro k hk i hi
  interval_cases k <;> simp [stars] at hi <;> omega

theorem wires_fold (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem ofFn_getD (x : Fin 14 → Bool) (i : Fin 14) : (List.ofFn x).getD (i : ℕ) false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem base_map (x5 : Fin 14 → Bool) : ∀ w < 10 + 0,
    (List.ofFn x5).getD (rm w) false =
      (List.ofFn fun (x6 : Fin 10) => x5 ([(0 : Fin 14), (1 : Fin 14), (2 : Fin 14), (3 : Fin 14),
        (5 : Fin 14), (6 : Fin 14), (7 : Fin 14), (8 : Fin 14), (9 : Fin 14), (12 : Fin 14)].getD ↑x6
        (0 : Fin 14))).getD w false := by
  intro w hw
  interval_cases w <;> simp [rm, tbl, List.getD_eq_getElem?_getD]

theorem gates_getD_lt (A B : List Gate) (j : ℕ) (h : j < A.length) :
    (A ++ B).getD j ⟨GateOp.or, []⟩ = A.getD j ⟨GateOp.or, []⟩ :=
  List.getD_append _ _ _ _ h

theorem gates_getD_ge (A B : List Gate) (j : ℕ) (h : A.length ≤ j) :
    (A ++ B).getD j ⟨GateOp.or, []⟩ = B.getD (j - A.length) ⟨GateOp.or, []⟩ :=
  List.getD_append_right _ _ _ _ h

theorem sh_getD (gs : List Gate) (j : ℕ) (h : j < gs.length) :
    (gs.map sh).getD j ⟨GateOp.or, []⟩ = sh (gs.getD j ⟨GateOp.or, []⟩) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

-- The shifted copy reads only earlier wires.
theorem sh_reads (x1 : Circuit) (hrb : NestedCover.ReadsBack 10 x1) (j : ℕ) (hj : j < x1.gates.length) :
    ∀ i ∈ (sh (x1.gates.getD j ⟨GateOp.or, []⟩)).inputs, i < 14 + j := by
  intro i hi
  simp only [sh, List.mem_map] at hi
  obtain ⟨a, ha, rfl⟩ := hi
  exact rm_lt a j (hrb j hj a ha)

end PEqualNP.Outside.L_meta_3517_aux

theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro x1 hAO hnd
  obtain ⟨hops, hrb, hlen⟩ := hAO
  have hrb' : ∀ i < x1.gates.length, ∀ a ∈ (x1.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, a < 10 + 0 + i := by
    intro i hi a ha
    have := hrb i hi a ha
    omega
  by_cases ho : x1.output < 10 + x1.gates.length
  · refine ⟨⟨x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh ++ PEqualNP.Outside.L_meta_3517_aux.stars (14 + x1.gates.length) ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14 + x1.gates.length + 10, PEqualNP.Outside.L_meta_3517_aux.rm x1.output]⟩],
      14 + x1.gates.length + 11⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
      rcases hg with (⟨g', hg', rfl⟩ | hg) | rfl
      · exact hops g' hg'
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_ops _ g hg
      · simp
    · intro j hj i hi
      simp only [List.length_append, List.length_map,
        PEqualNP.Outside.L_meta_3517_aux.stars_length, List.length_singleton] at hj
      have hs := PEqualNP.Outside.L_meta_3517_aux.stars_length (14 + x1.gates.length)
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
      simp only at hi
      by_cases h1 : j < x1.gates.length
      · rw [PEqualNP.Outside.L_meta_3517_aux.gates_getD_lt _ _ _ (by simp [hs]; omega),
          PEqualNP.Outside.L_meta_3517_aux.gates_getD_lt _ _ _ (by simpa using h1),
          PEqualNP.Outside.L_meta_3517_aux.sh_getD _ _ h1] at hi
        exact PEqualNP.Outside.L_meta_3517_aux.sh_reads x1 hrb j h1 i hi
      · by_cases h2 : j < x1.gates.length + 11
        · rw [PEqualNP.Outside.L_meta_3517_aux.gates_getD_lt _ _ _ (by simp [hs]; omega),
            PEqualNP.Outside.L_meta_3517_aux.gates_getD_ge _ _ _ (by simp; omega)] at hi
          have := PEqualNP.Outside.L_meta_3517_aux.stars_reads (14 + x1.gates.length) (by omega)
            (j - (x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh).length) (by simp; omega) i hi
          simp at this
          omega
        · rw [PEqualNP.Outside.L_meta_3517_aux.gates_getD_ge _ _ _ (by simp [hs]; omega)] at hi
          have hj' : j - (x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh ++
              PEqualNP.Outside.L_meta_3517_aux.stars (14 + x1.gates.length)).length = 0 := by
            simp [hs]; omega
          rw [hj'] at hi
          simp at hi
          have := PEqualNP.Outside.L_meta_3517_aux.rm_lt x1.output x1.gates.length ho
          omega
    · intro g hg
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
      rcases hg with (⟨g', hg', rfl⟩ | hg) | rfl
      · simpa [PEqualNP.Outside.L_meta_3517_aux.sh] using hlen g' hg'
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_len _ g hg
      · simp
    · intro g hg
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
      rcases hg with (⟨g', hg', rfl⟩ | hg) | rfl
      · exact (hnd g' hg').map PEqualNP.Outside.L_meta_3517_aux.rm_inj
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_nodup _ (by omega) g hg
      · have := PEqualNP.Outside.L_meta_3517_aux.rm_lt x1.output x1.gates.length ho
        simp
        omega
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_3517_aux.stars_length]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_3517_aux.stars_length]
    · intro x5
      set ys := (List.ofFn fun (x6 : Fin 10) => x5 ([(0 : Fin 14), (1 : Fin 14), (2 : Fin 14), (3 : Fin 14),
        (5 : Fin 14), (6 : Fin 14), (7 : Fin 14), (8 : Fin 14), (9 : Fin 14), (12 : Fin 14)].getD ↑x6
        (0 : Fin 14))) with hys
      have hpre := PEqualNP.Outside.L_meta_3517_aux.shift_fold x1.gates 0 ys (List.ofFn x5)
        (by simp [hys]) (by simp) (PEqualNP.Outside.L_meta_3517_aux.base_map x5) hrb'
      set W := (x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh).foldl PEqualNP.Outside.L_meta_3517_aux.step (List.ofFn x5) with hW
      have hWl : W.length = 14 + x1.gates.length := by
        rw [hW, PEqualNP.Outside.L_meta_3517_aux.fold_length]; simp
      set V := (PEqualNP.Outside.L_meta_3517_aux.stars (14 + x1.gates.length)).foldl PEqualNP.Outside.L_meta_3517_aux.step W with hV
      have hVl : V.length = 14 + x1.gates.length + 11 := by
        rw [hV, PEqualNP.Outside.L_meta_3517_aux.fold_length, hWl, PEqualNP.Outside.L_meta_3517_aux.stars_length]
      have hV10 := PEqualNP.Outside.L_meta_3517_aux.stars_val W (by omega)
      rw [hWl] at hV10
      have hin : ∀ i : Fin 14, W.getD (i : ℕ) false = x5 i := by
        intro i
        rw [hW, PEqualNP.Outside.L_meta_3517_aux.fold_getD _ _ _ (by simp)]
        exact PEqualNP.Outside.L_meta_3517_aux.ofFn_getD x5 i
      have hro : V.getD (PEqualNP.Outside.L_meta_3517_aux.rm x1.output) false =
          x1.eval ys := by
        have := PEqualNP.Outside.L_meta_3517_aux.rm_lt x1.output x1.gates.length ho
        rw [hV, PEqualNP.Outside.L_meta_3517_aux.fold_getD _ _ _ (by omega), hW,
          hpre x1.output (by omega)]
        rfl
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3517_aux.wires_fold]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [← hW, ← hV]
      simp only [PEqualNP.Outside.L_meta_3517_aux.step]
      rw [List.getD_append_right _ _ _ _ (by omega), show 14 + x1.gates.length + 11 - V.length = 0 by omega]
      simp only [List.getD_cons_zero, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval]
      rw [hro]
      simp only [List.any_cons, List.any_nil, id, Bool.or_false]
      rw [hV10]
      have h0 := hin 0
      have h1 := hin 1
      have h2 := hin 2
      have h3 := hin 3
      have h4 := hin 4
      have h5 := hin 5
      have h6 := hin 6
      have h10 := hin 10
      have h11 := hin 11
      have h13 := hin 13
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
      rw [show ((3 : Fin 14) : ℕ) = 3 from rfl] at h3
      rw [show ((4 : Fin 14) : ℕ) = 4 from rfl] at h4
      rw [show ((5 : Fin 14) : ℕ) = 5 from rfl] at h5
      rw [show ((6 : Fin 14) : ℕ) = 6 from rfl] at h6
      rw [show ((10 : Fin 14) : ℕ) = 10 from rfl] at h10
      rw [show ((11 : Fin 14) : ℕ) = 11 from rfl] at h11
      rw [show ((13 : Fin 14) : ℕ) = 13 from rfl] at h13
      rw [h0, h1, h2, h3, h4, h5, h6, h10, h11, h13, PEqualNP.Outside.L_meta_3517_aux.edges_eq x5, Bool.or_comm]
      rfl
  · refine ⟨⟨x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh ++ PEqualNP.Outside.L_meta_3517_aux.stars (14 + x1.gates.length),
      14 + x1.gates.length + 10⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩ | hg
      · exact hops g' hg'
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_ops _ g hg
    · intro j hj i hi
      simp only [List.length_append, List.length_map,
        PEqualNP.Outside.L_meta_3517_aux.stars_length] at hj
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
      simp only at hi
      by_cases h1 : j < x1.gates.length
      · rw [PEqualNP.Outside.L_meta_3517_aux.gates_getD_lt _ _ _ (by simpa using h1),
          PEqualNP.Outside.L_meta_3517_aux.sh_getD _ _ h1] at hi
        exact PEqualNP.Outside.L_meta_3517_aux.sh_reads x1 hrb j h1 i hi
      · rw [PEqualNP.Outside.L_meta_3517_aux.gates_getD_ge _ _ _ (by simp; omega)] at hi
        have := PEqualNP.Outside.L_meta_3517_aux.stars_reads (14 + x1.gates.length) (by omega)
          (j - (x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh).length) (by simp; omega) i hi
        simp at this
        omega
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩ | hg
      · simpa [PEqualNP.Outside.L_meta_3517_aux.sh] using hlen g' hg'
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_len _ g hg
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩ | hg
      · exact (hnd g' hg').map PEqualNP.Outside.L_meta_3517_aux.rm_inj
      · exact PEqualNP.Outside.L_meta_3517_aux.stars_nodup _ (by omega) g hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_3517_aux.stars_length]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_3517_aux.stars_length]
    · intro x5
      set W := (x1.gates.map PEqualNP.Outside.L_meta_3517_aux.sh).foldl PEqualNP.Outside.L_meta_3517_aux.step (List.ofFn x5) with hW
      have hWl : W.length = 14 + x1.gates.length := by
        rw [hW, PEqualNP.Outside.L_meta_3517_aux.fold_length]; simp
      have hV10 := PEqualNP.Outside.L_meta_3517_aux.stars_val W (by omega)
      rw [hWl] at hV10
      have hin : ∀ i : Fin 14, W.getD (i : ℕ) false = x5 i := by
        intro i
        rw [hW, PEqualNP.Outside.L_meta_3517_aux.fold_getD _ _ _ (by simp)]
        exact PEqualNP.Outside.L_meta_3517_aux.ofFn_getD x5 i
      have hx1 : ∀ y : List Bool, y.length = 10 → x1.eval y = false := by
        intro y hy
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [PEqualNP.Outside.L_meta_3517_aux.wires_fold]
        apply List.getD_eq_default
        rw [PEqualNP.Outside.L_meta_3517_aux.fold_length]
        omega
      rw [hx1 _ (by simp), Bool.false_or]
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3517_aux.wires_fold]
      simp only [List.foldl_append]
      rw [← hW, hV10]
      have h0 := hin 0
      have h1 := hin 1
      have h2 := hin 2
      have h3 := hin 3
      have h4 := hin 4
      have h5 := hin 5
      have h6 := hin 6
      have h10 := hin 10
      have h11 := hin 11
      have h13 := hin 13
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
      rw [show ((3 : Fin 14) : ℕ) = 3 from rfl] at h3
      rw [show ((4 : Fin 14) : ℕ) = 4 from rfl] at h4
      rw [show ((5 : Fin 14) : ℕ) = 5 from rfl] at h5
      rw [show ((6 : Fin 14) : ℕ) = 6 from rfl] at h6
      rw [show ((10 : Fin 14) : ℕ) = 10 from rfl] at h10
      rw [show ((11 : Fin 14) : ℕ) = 11 from rfl] at h11
      rw [show ((13 : Fin 14) : ℕ) = 13 from rfl] at h13
      rw [h0, h1, h2, h3, h4, h5, h6, h10, h11, h13, PEqualNP.Outside.L_meta_3517_aux.edges_eq x5]
