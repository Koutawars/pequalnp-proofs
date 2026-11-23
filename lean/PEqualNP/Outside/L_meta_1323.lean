import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1323_aux

open PEqualNP.CircuitLowerBounds

namespace Evaluation

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_step {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hop : let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 at hop
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans (g.inputs.toFinset_card_le.trans hop.2),
    fun _ hr => (Finset.mem_filter.mp hr).2, ?_⟩
  intro x y hxy hx
  have formula (z : Fin n → Bool) : value C z w =
      g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) := gate_value C z w hn hw
  have hread (r : ℕ) (hr : r ∈ g.inputs) :
      (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
    by_cases h : r < w
    · simpa only [ite_eq_left h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
    · simp [h]
  rw [formula x] at hx
  rw [formula y]
  rcases hop.1 with h | h
  · rw [h] at hx ⊢
    simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map] at hx ⊢
    rintro b ⟨r, hr, rfl⟩
    exact hread r hr (hx _ ⟨r, hr, rfl⟩)
  · rw [h] at hx ⊢
    simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at hx ⊢
    obtain ⟨b, ⟨r, hr, rfl⟩, hb⟩ := hx
    exact ⟨_, ⟨r, hr, rfl⟩, hread r hr hb⟩

private def wiresFrom := run

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, run, List.foldl_append]

private lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := run_length gs w

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := run_getD gs w i hi

private lemma getD_snoc_eq {α : Type} (w : List α) (v d : α) :
    (w ++ [v]).getD w.length d = v := by simp

end Evaluation

namespace LadderInterval

open Evaluation

lemma not_value_antitone {n : ℕ} (C : Circuit) (i : Fin C.gates.length)
    (hop : (C.gates.get i).op = GateOp.not) (x y : Fin n → Bool)
    (hxy : ∀ r < n + i.val, value C x r ≤ value C y r) :
    value C y (n + i.val) ≤ value C x (n + i.val) := by
  have hw : n + i.val < n + C.size := by simpa only [Circuit.size, Nat.add_lt_add_iff_left] using i.isLt
  have hop' : C.gates[i.val].op = GateOp.not := hop
  have formula (z : Fin n → Bool) : value C z (n + i.val) =
      !((C.gates.get i).inputs.map (fun r => if r < n + i.val then value C z r else false)).headD false := by
    simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem, hop', GateOp.eval] using
      gate_value C z (n + i.val) (Nat.le_add_right _ _) hw
  rw [formula x, formula y]
  cases hlist : (C.gates.get i).inputs with
  | nil => simp
  | cons r rs =>
    by_cases hr : r < n + i.val
    · simp only [List.map_cons, List.headD_cons, ite_eq_left hr]
      have revBool : ∀ a b : Bool, a ≤ b → (!b) ≤ (!a) := by decide
      exact revBool _ _ (hxy r hr)
    · simp [hr]

theorem value_interval {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (x y z : Fin n → Bool) (hxy : ∀ p, x p ≤ y p)
    (hyz : ∀ p, y p ≤ z p)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      value C x (n + i.val) = value C z (n + i.val)) (w : ℕ) :
    value C x w ≤ value C y w ∧ value C y w ≤ value C z w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p ≤ value C y p ∧ value C y p ≤ value C z p
      simpa only [input_value] using And.intro (hxy p) (hyz p)
    by_cases hw : w < n + C.size
    · let i : Fin C.gates.length := ⟨w - n, by unfold Circuit.size at hw; omega⟩
      have hwi : n + i.val = w := by dsimp [i]; omega
      have hg := hG (C.gates.get i) (List.get_mem _ _)
      by_cases h : (C.gates.get i).op = GateOp.not
      · have h₁ := not_value_antitone C i h x y (fun r hr => (ih r (hwi ▸ hr)).1)
        have h₂ := not_value_antitone C i h y z (fun r hr => (ih r (hwi ▸ hr)).2)
        have he := hnot i h
        rw [hwi] at h₁ h₂ he
        exact ⟨he ▸ h₂, he ▸ h₁⟩
      have hGate : ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or) ∧
          (C.gates.get i).inputs.length ≤ 2 := by
        exact ⟨hg.1.elim Or.inl (fun h' => h'.elim Or.inr (fun hn' => (h hn').elim)), hg.2⟩
      obtain ⟨P, _, hP, hstep⟩ := gate_step C w (by omega) hw hGate
      exact ⟨Bool.le_iff_imp.mpr (hstep x y (fun r hr => Bool.le_iff_imp.mp (ih r (hP r hr)).1)),
        Bool.le_iff_imp.mpr (hstep y z (fun r hr => Bool.le_iff_imp.mp (ih r (hP r hr)).2))⟩
    · rw [missing_value C x w (by omega), missing_value C y w (by omega), missing_value C z w (by omega)]
      exact ⟨le_rfl, le_rfl⟩

theorem not_interval_eq {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (x y z : Fin n → Bool) (hxy : ∀ p, x p ≤ y p)
    (hyz : ∀ p, y p ≤ z p)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      value C x (n + i.val) = value C z (n + i.val))
    (i : Fin C.gates.length) (hi : (C.gates.get i).op = GateOp.not) :
    value C x (n + i.val) = value C y (n + i.val) ∧
      value C y (n + i.val) = value C z (n + i.val) := by
  obtain ⟨h₁, h₂⟩ := value_interval C hG x y z hxy hyz hnot (n + i.val)
  have he := hnot i hi
  exact ⟨le_antisymm h₁ (he ▸ h₂), le_antisymm h₂ (he ▸ h₁)⟩

end LadderInterval

namespace Chain

open Evaluation

-- Evaluation at a gate, generalized from the Fano argument.
private theorem splitGate (gates : List Gate) (i : Fin gates.length) :
    gates = gates.take i ++ gates.get i :: gates.drop (i + 1) := by
  calc
    gates = gates.take i ++ gates.drop i := (List.take_append_drop _ _).symm
    _ = _ := congrArg (gates.take i ++ ·) (List.cons_getElem_drop_succ (h := i.isLt)).symm

private theorem evalGate {n : ℕ} (gates : List Gate) (i : Fin gates.length) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, n + i⟩ (List.ofFn x) =
      (gates.get i).op.eval ((gates.get i).inputs.map fun wire =>
        Circuit.eval ⟨gates.take i, wire⟩ (List.ofFn x)) := by
  let previous := wiresFrom (gates.take i) (List.ofFn x)
  let value := (gates.get i).op.eval
    ((gates.get i).inputs.map fun wire => previous.getD wire false)
  have hlength : previous.length = n + i := by
    simp [previous, length_wiresFrom]
  change (wiresFrom gates (List.ofFn x)).getD (n + i) false = value
  have hsplit := congrArg (fun gs => wiresFrom gs (List.ofFn x)) (splitGate gates i)
  rw [hsplit, wiresFrom_append]
  change (wiresFrom (gates.drop (i + 1)) (previous ++ [value])).getD (n + i) false = value
  rw [getD_wiresFrom _ _ _ (by simp [hlength]), ← hlength, getD_snoc_eq]



private theorem not_eval_taken {n : ℕ} (gates : List Gate) (i : Fin gates.length)
    (x : Fin n → Bool) (hi : (gates.get i).op = .not) :
    value ⟨gates, 0⟩ x (n + i) =
      !(((gates.get i).inputs.map (fun w : ℕ =>
        (Circuit.wires ⟨gates.take i.val, 0⟩ (List.ofFn x)).getD w false)).headD false) := by
  change Circuit.eval ⟨gates, n + i⟩ (List.ofFn x) = _
  rw [evalGate, hi]
  rfl

private theorem bool_le_of_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

theorem bound (n s : ℕ) (gates : List Gate)
    (hops : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hnot : ∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = .not → ∃ j : Fin s, ι j = i)
    (r : ℕ) (x : ℕ → Fin n → Bool)
    (hx : ∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true)
    (hchange : ∀ i : ℕ, i < r → ∃ t : Fin gates.length, (gates.get t).op = .not ∧
      ((gates.get t).inputs.map (fun k : ℕ =>
        (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠
      ((gates.get t).inputs.map (fun k : ℕ =>
        (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) :
    r + 1 ≤ 2 ^ s := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let Nots : Finset (Fin gates.length) := Finset.univ.filter (fun i => (gates.get i).op = .not)
  let key (i : ℕ) (t : ↥Nots) : Bool := value C (x i) (n + t.val.val)
  have chain (i j : ℕ) (hij : i ≤ j) (hjr : j ≤ r) (p : Fin n) : x i p ≤ x j p := by
    induction j generalizing i with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      by_cases h : i = j + 1
      · subst i
        exact le_rfl
      · exact (ih i (by omega) (by omega)).trans
          (bool_le_of_imp (hx j (by omega) p))
  have diff (i : ℕ) (hi : i < r) : key i ≠ key (i + 1) := by
    intro he
    obtain ⟨t, ht, hd⟩ := hchange i hi
    have htmem : t ∈ Nots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
    have hv := congrFun he ⟨t, htmem⟩
    change value ⟨gates, 0⟩ (x i) (n + t) =
      value ⟨gates, 0⟩ (x (i + 1)) (n + t) at hv
    rw [not_eval_taken gates t (x i) ht, not_eval_taken gates t (x (i + 1)) ht] at hv
    exact hd (by simpa using congrArg Bool.not hv)
  have sep (i j : ℕ) (hij : i < j) (hjr : j ≤ r) : key i ≠ key j := by
    intro he
    apply diff i (by omega)
    funext t
    have hnotEnds (z : Fin gates.length) (hz : (gates.get z).op = .not) :
        value C (x i) (n + z) = value C (x j) (n + z) := by
      have hmem : z ∈ Nots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      exact congrFun he ⟨z, hmem⟩
    exact (LadderInterval.not_interval_eq C hops _ _ _
      (chain i (i + 1) (by omega) (by omega)) (chain (i + 1) j (by omega) hjr)
      hnotEnds t.val (Finset.mem_filter.mp t.property).2).1
  have inj : Function.Injective (fun i : Fin (r + 1) => key i.val) := by
    intro i j he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact (sep i j h (by have := j.isLt; omega) he).elim
    · exact h
    · exact (sep j i h (by have := i.isLt; omega) he.symm).elim
  have hsize : Nots.card ≤ s := by
    obtain ⟨ι, hι⟩ := hnot
    have hsub : Nots ⊆ Finset.univ.image ι := by
      intro i hi
      obtain ⟨j, hj⟩ := hι i (Finset.mem_filter.mp hi).2
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    calc
      Nots.card ≤ (Finset.univ.image ι).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by simp
  have hkeys := Fintype.card_le_of_injective (fun i : Fin (r + 1) => key i.val) inj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hkeys
  exact hkeys.trans (Nat.pow_le_pow_right (by decide) hsize)

end Chain

end PEqualNP.Outside.L_meta_1323_aux

theorem PEqualNP.Outside.L_meta_1323 :
    ∀ (n s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s →
    Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    ∃ j : Fin s, ι j = i) →
    ∀ (r : ℕ) (x : ℕ →
    Fin n →
    Bool), (∀ i : ℕ, i < r →
    ∀ p : Fin n, x i p = true →
    x (i + 1) p = true) →
    (∀ i : ℕ, i < r →
    ∃ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) →
    r + 1 ≤ 2 ^ s := by
  exact PEqualNP.Outside.L_meta_1323_aux.Chain.bound
