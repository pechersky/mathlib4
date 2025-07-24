/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Algebra.Order.Archimedean.Submonoid

/-!
# Necessary and sufficient conditions for a locally compact valued field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

open NNReal

section NormedField

open scoped NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

@[simp]
lemma NormedField.v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x := rfl

namespace Valued.integer

-- should we do this all in the Valuation namespace instead?

/-- An element is in the valuation ring if the norm is bounded by 1. This is a variant of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation. -/
lemma mem_iff {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, ← NNReal.coe_le_coe]

lemma norm_le_one (x : 𝒪[K]) : ‖x‖ ≤ 1 := mem_iff.mp x.prop

@[simp]
lemma norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).valuation_unit u

lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  simp

lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).isUnit_iff_valuation_eq_one

lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  Valuation.integer.v_irreducible_lt_one h

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  Valuation.integer.v_irreducible_pos h

lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  simp [Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  simp [h.maximalIdeal_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  simp [h.maximalIdeal_pow_eq_setOf_le_v_coe_pow, Set.ext_iff, ← NNReal.coe_le_coe]

variable (K) in
lemma exists_norm_coe_lt_one : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
lemma exists_norm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_coe_lt_one K

variable (K) in
lemma exists_nnnorm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 :=
  exists_norm_coe_lt_one K

end Valued.integer

end NormedField

namespace Valued.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section FiniteResidueField

open Valued

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_finite_quot_finite_ideal
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

lemma finite_residueField_of_totallyBounded_of_isDiscreteValuationRing
    [IsDiscreteValuationRing 𝒪[K]] (H : TotallyBounded (Set.univ (α := 𝒪[K]))) :
    Finite 𝓀[K] := by
  have hb : (uniformity 𝒪[K]).HasBasis (fun _ ↦ True)
      fun γ : Γ₀ˣ => { p : 𝒪[K] × 𝒪[K] | v (p.2 - p.1 : K) < (γ : Γ₀) } := by
    rw [uniformity_subtype]
    exact (hasBasis_uniformity _ _).comap _
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [totallyBounded_iff_subset] at H
  specialize H {rs : 𝒪[K] × 𝒪[K] | v (rs.2 - rs.1 : K) < Units.mk0 (v (p : K))
    (by simp [hp.ne_zero])} (hb.mem_of_mem trivial)
  simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at H
  obtain ⟨t, ht, ht'⟩ := H
  rw [← Set.finite_univ_iff]
  refine (ht.image (IsLocalRing.residue _)).subset ?_
  rintro ⟨x⟩
  replace ht' := ht'.ge (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at ht'
  obtain ⟨y, hy, hy'⟩ := ht'
  simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Set.mem_univ,
    IsLocalRing.residue, Set.mem_image, true_implies]
  refine ⟨y, hy, ?_⟩
  convert (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := 𝓂[K]) y x).mpr _
  -- TODO: make Valued.maximalIdeal abbreviations instead of def
  rw [Valued.maximalIdeal, hp.maximalIdeal_eq, ← SetLike.mem_coe,
    (Valuation.integer.integers _).coe_span_singleton_eq_setOf_le_v_algebraMap]
  simpa using hy'.le

lemma totallyBounded_iff_finite_residueField [hv : (Valued.v : Valuation K Γ₀).RankOne]
    [IsDiscreteValuationRing 𝒪[K]] :
    TotallyBounded (Set.univ (α := 𝒪[K])) ↔ Finite 𝓀[K] := by
  have hb : (uniformity 𝒪[K]).HasBasis (fun _ ↦ True)
      fun γ : Γ₀ˣ => { p : 𝒪[K] × 𝒪[K] | v (p.2 - p.1 : K) < (γ : Γ₀) } := by
    rw [uniformity_subtype]
    exact (hasBasis_uniformity _ _).comap _
  refine ⟨fun H ↦ finite_residueField_of_totallyBounded_of_isDiscreteValuationRing H, fun H ↦ ?_⟩
  · rw [hb.totallyBounded_iff]
    intro ε _
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := Valuation.integer.v_irreducible_lt_one hp
    by_cases hx : ∀ x : 𝒪[K], x ≠ 0 → ε < v (x : K)
    · -- discrete case, should be disallowed by a different Valued topology
      have : MulArchimedean Γ₀ := .comap hv.hom.toMonoidHom hv.strictMono
      obtain ⟨n, hn⟩ := exists_pow_lt₀ hp' ε
      absurd hn
      simpa using (hx (p ^ n) (by simp [hp.ne_zero])).le
    push_neg at hx
    obtain ⟨x, hx, hx'⟩ := hx
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hp
    have hu : v (u.val : K) = 1 := (Valuation.integer.integers _).valuation_unit u
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, hu, map_pow, one_mul] at hx'
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H (n + 1)
    refine ⟨Quotient.out '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ (n + 1)))), Set.toFinite _, ?_⟩
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ (n + 1)),
      hp.maximalIdeal_pow_eq_setOf_le_v_coe_pow, Set.image_univ, Set.mem_range, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
    intro i y
    simp only [Set.mem_vadd_set, Set.mem_setOf_eq, vadd_eq_add, Subtype.exists, exists_and_left,
      Set.mem_iUnion, forall_exists_index, and_imp]
    rintro z hz hz' rfl
    use i
    simp only [Subring.coe_add, sub_add_cancel_left, Valuation.map_neg]
    refine (hz.trans_lt ?_).trans_le hx'
    exact pow_lt_pow_right_of_lt_one₀ (by simp [zero_lt_iff, hp.ne_zero]) hp' (by simp)

end FiniteResidueField

section CompactDVR

open Valued

lemma locallyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    Nonempty (LocallyFiniteOrder (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ):= by
  constructor
  refine LocallyFiniteOrder.ofFiniteIcc ?_
  -- We only need to show that we can construct a finite set for some set between
  -- a non-zero `z : Γ₀` and 1, because we can scale/invert this set to cover the whole group.
  suffices ∀ z : (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ, (Set.Icc z 1).Finite by
    rintro x y
    rcases lt_trichotomy y x with hxy | rfl | hxy
    · rw [Set.Icc_eq_empty_of_lt]
      · exact Set.finite_empty
      · simp [hxy]
    · simp
    wlog h : x ≤ 1 generalizing x y
    · push_neg at h
      specialize this y⁻¹ x⁻¹ (inv_lt_inv' hxy) (inv_le_one_of_one_le (h.trans hxy).le)
      refine (this.inv).subset ?_
      rw [Set.inv_Icc]
      intro
      simp +contextual
    generalize_proofs _ _ _ _ hxu hyu
    rcases le_total y 1 with hy | hy
    · exact (this x).subset (Set.Icc_subset_Icc_right hy)
    · have H : (Set.Icc y⁻¹ 1).Finite := this _
      refine ((this x).union H.inv).subset (le_of_eq ?_)
      rw [Set.inv_Icc, inv_one, Set.Icc_union_Icc_eq_Icc] <;>
      simp [h, hy]
  -- We can construct a family of spheres at every single element of the valuation ring
  -- outside of a closed ball, which will cover.
  -- Since we are in a compact space, this cover has a finite subcover.
  -- First, we need to pick a threshold element with a nontrivial valuation less than 1,
  -- which will form -- the inner closed ball of the cover, which we need to cover 0.
  intro z
  obtain ⟨a, ha⟩ := z.val.prop
  rcases lt_or_ge 1 z with hz1 | hz1
  · rw [Set.Icc_eq_empty_of_lt]
    · exact Set.finite_empty
    · simp [hz1]
  have z0' : 0 < (z : MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := by simp
  have z0 : 0 < ((z : MonoidHom.mrange (Valued.v : Valuation K Γ₀)) : Γ₀) :=
    Subtype.coe_lt_coe.mpr z0'
  have a0 : 0 < v a := by simp [ha, z0]
  -- Construct our cover, which has an inner closed ball, and spheres for each element
  -- outside of the closed ball. These are all open sets by the nonarchimedean property.
  let U : K → Set K := fun y ↦ if v (y : K) ≤ z
    then {w | v (w : K) ≤ z}
    else {w | v (w : K) = v (y : K)}
  have := hc.elim_finite_subcover U
  specialize this ?_ ?_
  · intro w
    simp only [U]
    split_ifs with hw
    · exact Valued.isOpen_closedball _ z0.ne'
    · refine Valued.isOpen_sphere _ ?_
      push_neg at hw
      refine (hw.trans' ?_).ne'
      simp [z0]
  · intro w
    simp only [integer, SetLike.mem_coe, Valuation.mem_integer_iff, Set.mem_iUnion, U]
    intro hw
    use if v w ≤ z then a else w
    split_ifs <;>
    simp_all
  -- For each element of the valuation ring that is bigger than our threshold element above,
  -- there must be something in the cover that has the precise valuation of the element,
  -- because it must be outside the inner closed ball, and thus is covered by some sphere.
  obtain ⟨t, ht⟩ := this
  classical
  refine (t.finite_toSet.dependent_image ?_).subset ?_
  · refine fun i hi ↦ if hi' : v i ≤ z then z else Units.mk0 ⟨(v i), by simp⟩ ?_
    push_neg at hi'
    exact Subtype.coe_injective.ne_iff.mp (hi'.trans' z0).ne'
  · intro i
    simp only [Set.mem_Icc, Finset.mem_coe, exists_prop, Set.mem_setOf_eq, and_imp]
    -- we get the `c` from the cover that covers our arbitrary `i` with its set
    obtain ⟨c, hc⟩ := i.val.prop
    intro hzi hi1
    have hj := ht (hc.trans_le hi1)
    simp only [Set.mem_iUnion, exists_prop, U] at hj
    obtain ⟨j, hj, hj'⟩ := hj
    use j, hj
    -- and this `c` is either less than or greater than (or equal to) the threshold element
    split_ifs at hj' with hcj
    · simp only [Set.mem_setOf_eq, hc, Subtype.coe_le_coe, Units.val_le_val] at hj'
      simp [hcj, le_antisymm hj' hzi]
    · simp only [Set.mem_setOf_eq] at hj'
      rw [dif_neg hcj]
      simp [← hj', hc]

lemma mulArchimedean_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    MulArchimedean (MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := by
  rw [← Units.mulArchimedean_iff]
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  exact MulArchimedean.of_locallyFiniteOrder

lemma isPrincipalIdealRing_of_compactSpace [hc : CompactSpace 𝒪[K]] :
    IsPrincipalIdealRing 𝒪[K] := by
  -- TODO: generalize to `Valuation.Integer`, which will require showing that `IsCompact`
  -- pulls back across `TopologicalSpace.induced` from a `LocallyCompactSpace`.
  -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the valuation is densely ordered.
  -- We can also construct that it has a locally finite ordered, by compactness
  -- which leads to a contradiction.
  -- the key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have hc : IsCompact (X := K) 𝒪[K] := by
    simpa [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype] using hc
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  have hm := mulArchimedean_mrange_of_isCompact_integer hc
  rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
  intro H
  -- since we are densely ordered, we necessarily are nontrivial
  replace H : DenselyOrdered (MonoidHom.mrange (v : Valuation K Γ₀)) := H
  obtain ⟨x, hx, hx'⟩ := exists_between (α := (MonoidHom.mrange (v : Valuation K Γ₀))) zero_lt_one
  lift x to (MonoidHom.mrange (v : Valuation K Γ₀))ˣ using IsUnit.mk0 _ hx.ne'
  rw [← Units.val_one, Units.val_lt_val] at hx'
  have : Nontrivial (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ := ⟨_, _, hx'.ne'⟩
  rw [← denselyOrdered_units_iff] at H
  exact not_lt_of_denselyOrdered_of_locallyFinite _ _ hx'

lemma isDiscreteValuationRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).IsNontrivial]
    [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] := by
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  obtain ⟨x, hx, hx'⟩ := hn.exists_lt_one
  have key : IsPrincipalIdealRing 𝒪[K] := isPrincipalIdealRing_of_compactSpace
  exact {
    not_a_field' := by
      -- here is the other place where the nontriviality of the valuation comes in,
      -- since if we had `v x = 0 ∨ v x = 1`, then the maximal ideal would be `⊥`.
      simp only [ne_eq, Ideal.ext_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Ideal.mem_bot, not_forall, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      refine ⟨⟨x, hx'.le⟩, ?_⟩
      simpa [Subtype.ext_iff, hx'] using hx
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).IsNontrivial] :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : IsDiscreteValuationRing 𝒪[K] := isDiscreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete] at h
    exact finite_residueField_of_totallyBounded_of_isDiscreteValuationRing h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩

lemma properSpace_iff_compactSpace_integer [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             toNormedField.setOf_mem_integer_eq_closedBall]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField,
      toNormedField.setOf_mem_integer_eq_closedBall,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype]

end Valued.integer
