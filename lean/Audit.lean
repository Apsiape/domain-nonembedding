import DomainNonembedding
import Main
import DomainNonembedding.IncidenceBounds

set_option autoImplicit false
#check DomainNonembedding.nonembedding
#check DomainNonembedding.nonembedding_data
#check DomainNonembedding.permutation_average
#print axioms DomainNonembedding.Permutation.unusedCount_ge
#print axioms DomainNonembedding.Permutation.bad_count_mul_unused_le
#print axioms DomainNonembedding.Permutation.bad_border_corner_unique
#print axioms DomainNonembedding.Permutation.sum_growth_ge
#print axioms DomainNonembedding.Permutation.exists_arrangement_ge
#print axioms DomainNonembedding.Permutation.block_factorization
#print axioms DomainNonembedding.Permutation.average_integer
#print axioms DomainNonembedding.Permutation.average
#print axioms DomainNonembedding.Permutation.exists_common_normalized
#print axioms DomainNonembedding.DivisionRingRank.row_eq_column
#print axioms DomainNonembedding.permutation_average
#print axioms DomainNonembedding.rowRank_eq_columnRank
#print axioms DomainNonembedding.FiniteFieldData.exists_large_power
#print axioms DomainNonembedding.FiniteFieldData.grid_card
#print axioms DomainNonembedding.nonembedding

#check DomainNonembedding.Construction.paperData_exists
#check DomainNonembedding.Interpolation.interpolation_identity
#check DomainNonembedding.MatrixDescent.rank_certificate
#check DomainNonembedding.LocalRank.universal_rank_ceiling

#print axioms DomainNonembedding.Incidence.deletedMarks_card_le
#print axioms DomainNonembedding.Incidence.retained_girth
#print axioms DomainNonembedding.Incidence.mem_chosenLinePoints
#print axioms DomainNonembedding.Incidence.chosenLinePoints_card
#print axioms DomainNonembedding.Incidence.deletedPoints_card_le
#print axioms DomainNonembedding.Incidence.exceptionalPoints_card_le
#print axioms DomainNonembedding.Incidence.incidence_not_deleted
#print axioms DomainNonembedding.Incidence.retainedIncidence_card
#print axioms DomainNonembedding.Incidence.retainedIncidence_card_ge
#print axioms DomainNonembedding.Incidence.retained_card
#print axioms DomainNonembedding.Incidence.expect_deletedMarks_le
#print axioms DomainNonembedding.Incidence.exists_alteration_cost
#print axioms DomainNonembedding.Incidence.numeric_halves
#print axioms DomainNonembedding.Incidence.alteration_arith
#print axioms DomainNonembedding.Incidence.geom_sum_bounds
#print axioms DomainNonembedding.Incidence.cycle_numeric_bound
#print axioms DomainNonembedding.Incidence.gridMarks_card
#print axioms DomainNonembedding.Incidence.floor_grid_lower
#print axioms DomainNonembedding.Incidence.directions_card
#print axioms DomainNonembedding.Incidence.mean_grid_lower
#print axioms DomainNonembedding.Incidence.large_field_outcome
#print axioms DomainNonembedding.MarkedLines.exists_regular
#print axioms DomainNonembedding.Incidence.parameter_incidence_iff
#print axioms DomainNonembedding.Incidence.exists_markedLines
#print axioms DomainNonembedding.MarkedLines.block_subset
#print axioms DomainNonembedding.Construction.numbered_grid_card
#print axioms DomainNonembedding.Construction.exists_withBlocks
#print axioms DomainNonembedding.Construction.paperData_exists
#print axioms DomainNonembedding.Interpolation.scalar_card
#print axioms DomainNonembedding.Interpolation.degree_cutoff
#print axioms DomainNonembedding.Interpolation.lagrange_eq_grid
#print axioms DomainNonembedding.Interpolation.mem_lineIncidence
#print axioms DomainNonembedding.Interpolation.interpolation_identity
#print axioms DomainNonembedding.MatrixDescent.flatten_mul
#print axioms DomainNonembedding.MatrixDescent.flatten_sum
#print axioms DomainNonembedding.MatrixDescent.flatten_neg
#print axioms DomainNonembedding.MatrixDescent.rank_blockDiagonal
#print axioms DomainNonembedding.MatrixDescent.rank_neg
#print axioms DomainNonembedding.MatrixDescent.rank_sum_le
#print axioms DomainNonembedding.MatrixDescent.rank_amplification
#print axioms DomainNonembedding.MatrixDescent.exists_regular_representation
#print axioms DomainNonembedding.MatrixDescent.weighted_eq
#print axioms DomainNonembedding.MatrixDescent.certificate_identity
#print axioms DomainNonembedding.MatrixDescent.rank_certificate_of_rep
#print axioms DomainNonembedding.MatrixDescent.rank_certificate
#print axioms DomainNonembedding.LocalRank.block_sum_factor
#print axioms DomainNonembedding.LocalRank.rank_add_le
#print axioms DomainNonembedding.LocalRank.triangle_relation
#print axioms DomainNonembedding.LocalRank.block_rank_le_one
#print axioms DomainNonembedding.LocalRank.point_rank_bound
#print axioms DomainNonembedding.LocalRank.rank_budget
#print axioms DomainNonembedding.LocalRank.universal_rank_ceiling

-- Session 4: exact frozen target interfaces and every new proved node.
#check DomainNonembedding.LineFree.line_free
#check DomainNonembedding.GraphNormalForms.central_injective
#check DomainNonembedding.GraphNormalForms.copied_injective
#print axioms DomainNonembedding.CollapsedLines.block_incident
#print axioms DomainNonembedding.CollapsedLines.block_unique
#print axioms DomainNonembedding.CollapsedLines.incidences_girth
#print axioms DomainNonembedding.CollapsedLines.v_link_girth
#print axioms DomainNonembedding.CollapsedLines.w_link_girth
#print axioms DomainNonembedding.CollapsedLines.linkDirection_color
#print axioms DomainNonembedding.CollapsedLines.linkDirection_injective
#print axioms DomainNonembedding.CollapsedLines.face_corner_adj
#print axioms DomainNonembedding.CollapsedLines.allLink_closed
#print axioms DomainNonembedding.CollapsedLines.v_reduced_same_label
#print axioms DomainNonembedding.CollapsedLines.w_reduced_same_label
#print axioms DomainNonembedding.CollapsedLines.x_turn_large
#print axioms DomainNonembedding.CollapsedLines.ribbon_outer_iff
#print axioms DomainNonembedding.CollapsedLines.ribbon_color
#print axioms DomainNonembedding.CollapsedLines.ribbon_direction_step
#print axioms DomainNonembedding.CollapsedLines.ribbon_adj
#print axioms DomainNonembedding.CollapsedLines.ribbon_reduced
#print axioms DomainNonembedding.CollapsedLines.ribbon_closed
#print axioms DomainNonembedding.CollapsedLines.x_turn_large'
#print axioms DomainNonembedding.CollapsedLines.xword_not_fillable
#print axioms DomainNonembedding.CollapsedLines.tgt_xEdge
#print axioms DomainNonembedding.CollapsedLines.src_xEdge
#print axioms DomainNonembedding.CollapsedLines.flip_xEdge
#print axioms DomainNonembedding.CollapsedLines.xEdge_injective
#print axioms DomainNonembedding.CollapsedLines.wp_congr
#print axioms DomainNonembedding.CollapsedLines.wordPath_cons_x
#print axioms DomainNonembedding.CollapsedLines.wordPath_even
#print axioms DomainNonembedding.CollapsedLines.wordValue_xEdge
#print axioms DomainNonembedding.CollapsedLines.lineSubgroup_free
#print axioms DomainNonembedding.LineFree.edgeImage_relators
#print axioms DomainNonembedding.LineFree.toAuxiliary_mk_of
#print axioms DomainNonembedding.LineFree.retract_row
#print axioms DomainNonembedding.LineFree.retract_col
#print axioms DomainNonembedding.LineFree.retract_inner
#print axioms DomainNonembedding.LineFree.normalizedBasis_injective
#print axioms DomainNonembedding.LineFree.fullLine_injective
#print axioms DomainNonembedding.LineFree.normalizedImage_injective
#print axioms DomainNonembedding.LineFree.toAuxiliary_lineHom
#print axioms DomainNonembedding.LineFree.line_free
#print axioms DomainNonembedding.GraphNormalForms.exists_conjugators
#print axioms DomainNonembedding.GraphNormalForms.centralLine_injective
#print axioms DomainNonembedding.GraphNormalForms.treeMap_injective
#print axioms DomainNonembedding.GraphNormalForms.central_injective_tree
#print axioms DomainNonembedding.GraphNormalForms.copy_injective_tree
#print axioms DomainNonembedding.GraphNormalForms.tree_relation
#print axioms DomainNonembedding.GraphNormalForms.leftMap_injective
#print axioms DomainNonembedding.GraphNormalForms.rightMap_injective
#print axioms DomainNonembedding.GraphNormalForms.letters_relation
#print axioms DomainNonembedding.GraphNormalForms.edge_relation
#print axioms DomainNonembedding.GraphNormalForms.generatorImage_copyWord
#print axioms DomainNonembedding.GraphNormalForms.generatorImage_relators
#print axioms DomainNonembedding.GraphNormalForms.central_composition
#print axioms DomainNonembedding.GraphNormalForms.copy_composition
#print axioms DomainNonembedding.GraphNormalForms.central_injective
#print axioms DomainNonembedding.GraphNormalForms.copied_injective

-- Session 5: independent proved headline and shear replacements.
#check DomainNonembedding.Headline.nonembedding
#check DomainNonembedding.ShearNonembedding.shear_nonembedding
#print axioms DomainNonembedding.Headline.rank_row_column_le
#print axioms DomainNonembedding.Headline.rank_row_difference_le
#print axioms DomainNonembedding.Headline.normalized_difference_rank_le
#print axioms DomainNonembedding.Headline.conjugated_difference_rank_le
#print axioms DomainNonembedding.Headline.gluing_relation
#print axioms DomainNonembedding.Headline.groupMap_injective
#print axioms DomainNonembedding.Headline.entries_injective
#print axioms DomainNonembedding.Headline.entries_ne_zero
#print axioms DomainNonembedding.Headline.copied_line_rank
#print axioms DomainNonembedding.Headline.nonembedding_prime_data
#print axioms DomainNonembedding.Headline.coefficient_injective
#print axioms DomainNonembedding.Headline.nonembedding_data
#print axioms DomainNonembedding.Headline.paperData_admissible
#print axioms DomainNonembedding.Headline.nonembedding
#print axioms DomainNonembedding.ShearNormalForms.leftMap_injective
#print axioms DomainNonembedding.ShearNormalForms.rightMap_injective
#print axioms DomainNonembedding.ShearNormalForms.letters_relation
#print axioms DomainNonembedding.ShearNormalForms.s_commutes_base
#print axioms DomainNonembedding.ShearNormalForms.letters_commute_s
#print axioms DomainNonembedding.ShearNormalForms.line_relation
#print axioms DomainNonembedding.ShearNormalForms.generatorImage_baseWord
#print axioms DomainNonembedding.ShearNormalForms.generatorImage_relators
#print axioms DomainNonembedding.ShearNormalForms.s_ne_one
#print axioms DomainNonembedding.ShearNonembedding.groupMap_ne_zero
#print axioms DomainNonembedding.ShearNonembedding.diagonal_rank_ge
#print axioms DomainNonembedding.ShearNonembedding.shear_rank_bound
#print axioms DomainNonembedding.ShearNonembedding.normalized_rank_le
#print axioms DomainNonembedding.ShearNonembedding.line_relation
#print axioms DomainNonembedding.ShearNonembedding.normalized_line_rank
#print axioms DomainNonembedding.ShearNonembedding.nonembedding_data
#print axioms DomainNonembedding.ShearNonembedding.shear_nonembedding

#print axioms DomainNonembedding.Main.paperData_exists
#print axioms DomainNonembedding.Main.interpolation_identity
#print axioms DomainNonembedding.Main.rank_certificate
#print axioms DomainNonembedding.Main.line_free
#print axioms DomainNonembedding.Main.universal_rank_ceiling
#print axioms DomainNonembedding.Main.central_injective
#print axioms DomainNonembedding.Main.copied_injective
#print axioms DomainNonembedding.Main.nonembedding_prime_data
#print axioms DomainNonembedding.Main.nonembedding_data
#print axioms DomainNonembedding.Main.nonembedding
#print axioms DomainNonembedding.Main.shear_nonembedding
#check @DomainNonembedding.paperData
#check @DomainNonembedding.paperData_admissible

-- Full development audit: every declaration, including generated instances/private helpers,
-- selected by its defining module, rather than a hand-picked theorem list.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let entries := env.constants.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  let mut count : Nat := 0
  for (name, _) in entries do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx]!
    unless mod.getRoot == `DomainNonembedding || mod == `Statements || mod == `Main ||
        mod.getRoot == `NonSofic || mod.getRoot == `FiniteLean do continue
    let axs ← Lean.collectAxioms name
    unless axs.all (fun a => permitted.contains a) do
      throwError "Unpermitted dependency in {name}: {axs}"
    logInfo m!"AUDIT|{mod}|{name}|{axs}"
    count := count + 1
  logInfo m!"FULL-AUDIT-PASS declarations={count}"
