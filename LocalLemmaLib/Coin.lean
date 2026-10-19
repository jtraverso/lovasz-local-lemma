/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Fair coin flips indexed by a finite type

The uniform probability measure on colourings `ι → Bool`, independence of events depending on
disjoint sets of coordinates, and the probability that a set of coordinates is monochromatic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LocalLemma

/-- The uniform (product of fair coins) probability measure on `ι → Bool`. -/
noncomputable def coinMeasure (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ => (PMF.uniformOfFintype Bool).toMeasure

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (coinMeasure ι) := by
  unfold coinMeasure; infer_instance

/-- The event `A` depends only on the coordinates in `D`. -/
def CoordDep {ι : Type*} (A : Set (ι → Bool)) (D : Finset ι) : Prop :=
  ∀ ω ω' : ι → Bool, (∀ i ∈ D, ω i = ω' i) → ω ∈ A → ω' ∈ A

lemma CoordDep.mono {ι : Type*} {A : Set (ι → Bool)} {D D' : Finset ι} (h : CoordDep A D)
    (hD : D ⊆ D') : CoordDep A D' :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (hD hi)

lemma CoordDep.measurableSet {ι : Type*} {A : Set (ι → Bool)} {D : Finset ι}
    (h : CoordDep A D) :
    MeasurableSet[MeasurableSpace.comap (fun ω (i : D) => ω i) MeasurableSpace.pi] A := by
  refine ⟨(fun ω (i : D) => ω i) '' A, (Set.toFinite _).measurableSet, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨ω', hω', he⟩
    refine h ω' ω (fun i hi => ?_) hω'
    exact congrFun he ⟨i, hi⟩
  · intro hω; exact ⟨ω, hω, rfl⟩

lemma coin_indep_comap {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    Indep (MeasurableSpace.comap (fun ω (i : S) => ω i) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω (i : (Sᶜ : Finset ι)) => ω i) MeasurableSpace.pi)
      (coinMeasure ι) := by
  have h : iIndepFun (fun i (ω : ι → Bool) => ω i) (coinMeasure ι) := by
    unfold coinMeasure
    exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have h2 := h.indepFun_finset S Sᶜ disjoint_compl_right fun i => measurable_pi_apply i
  exact (IndepFun_iff_Indep _ _ _).1 h2

/-- Events depending on coordinate sets that are disjoint whenever the indices are non-adjacent
form a dependency graph. -/
lemma coin_dependency {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → Set (ι → Bool)) (D : Fin n → Finset ι) (hA : ∀ i, CoordDep (A i) (D i))
    (Γ : SimpleGraph (Fin n)) (hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j)) :
    ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j})
      (coinMeasure ι) := by
  classical
  intro i
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (coin_indep_comap (D i)) ?_) ?_
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (hA i).measurableSet
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨j, hji, hadj, rfl⟩ := ht
    refine ((hA j).mono ?_).measurableSet
    intro x hx
    rw [Finset.mem_compl]
    exact fun hx' => Finset.disjoint_left.1 (hΓ i j hji hadj) hx' hx

lemma coin_const_eq {ι : Type*} [Fintype ι] (E : Finset ι) (b : Bool) :
    coinMeasure ι {ω | ∀ i ∈ E, ω i = b} = (2⁻¹ : ENNReal) ^ E.card := by
  classical
  have hs : {ω : ι → Bool | ∀ i ∈ E, ω i = b} =
      Set.univ.pi fun i => if i ∈ E then {b} else Set.univ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    refine forall_congr' fun i => ?_
    split_ifs <;> simp_all
  rw [hs, coinMeasure, Measure.pi_pi]
  have : ∀ i, (PMF.uniformOfFintype Bool).toMeasure (if i ∈ E then {b} else Set.univ) =
      if i ∈ E then (2⁻¹ : ENNReal) else 1 := by
    intro i
    split_ifs
    · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp [PMF.uniformOfFintype_apply]
    · exact measure_univ
  simp_rw [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma coin_mono_le {ι : Type*} [Fintype ι] (E : Finset ι) :
    (coinMeasure ι).real {ω | ∃ b, ∀ i ∈ E, ω i = b} ≤ 2 * (1 / 2) ^ E.card := by
  have hs : {ω : ι → Bool | ∃ b, ∀ i ∈ E, ω i = b} =
      {ω | ∀ i ∈ E, ω i = true} ∪ {ω | ∀ i ∈ E, ω i = false} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨b, hb⟩; cases b <;> simp_all
    · rintro (h | h) <;> exact ⟨_, h⟩
  rw [hs]
  refine (measureReal_union_le _ _).trans ?_
  have h : ∀ b, (coinMeasure ι).real {ω | ∀ i ∈ E, ω i = b} = (1 / 2) ^ E.card := by
    intro b
    rw [Measure.real, coin_const_eq, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp
  rw [h, h]; linarith

end LocalLemma
