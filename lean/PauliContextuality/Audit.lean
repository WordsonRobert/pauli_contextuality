/-
Audit.lean — axiom audit of the headline theorems.

`#audit_pure t₁ t₂ …` fails (compile error) unless each theorem depends only on the three standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

`#audit_comp t₁ t₂ …` allows, in addition, the auxiliary axioms that `native_decide` creates for
finite computations (`…._native.native_decide.ax_…`, i.e. trust in the compiler, `Lean.ofReduceBool`).
Anything else — in particular `sorryAx` or a user `axiom` — is an error.

Both commands print one line per theorem with the number of `native_decide` certificates it uses.
-/
import PauliContextuality.Quadrics5
import PauliContextuality.PhaseStates
import PauliContextuality.HardMain
import PauliContextuality.RealizeDeg
import PauliContextuality.Tensor
import PauliContextuality.Packing
import PauliContextuality.Profile
import PauliContextuality.NoDeletion
import PauliContextuality.Tractable
import PauliContextuality.Cone
import PauliContextuality.CycleSign
import PauliContextuality.QminusBridge
import PauliContextuality.QuantumGame
import PauliContextuality.TightExamples
import PauliContextuality.GaugeKernel
import PauliContextuality.Chain
import PauliContextuality.Intrinsic
import PauliContextuality.SectionCor
import PauliContextuality.ConeQuad
import PauliContextuality.QuadType
import PauliContextuality.ConeSub
import PauliContextuality.TangentQuad
import PauliContextuality.TightConverse

open Lean Elab Command

namespace PauliCtx.Audit

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- the axioms created by `native_decide` (trust in the compiler): the auxiliary
`…._native.native_decide.ax_…` constants and `Lean.ofReduceBool` / `Lean.trustCompiler` -/
def isNative (n : Name) : Bool :=
  (n.toString.splitOn "native_decide").length > 1 || n == ``Lean.ofReduceBool ||
    n == ``Lean.trustCompiler

def auditOne (id : Syntax) (allowNative : Bool) : CommandElabM Unit := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !(stdAxioms.contains a) && !(allowNative && isNative a)
  let nat := (axs.filter isNative).size
  if bad.isEmpty then
    logInfo m!"OK   {n}  (native certificates: {nat})"
  else
    logError m!"FAIL {n} depends on non-allowed axioms {bad.toList}"

elab "#audit_pure " ids:ident* : command => do
  for id in ids do auditOne id false

elab "#audit_comp " ids:ident* : command => do
  for id in ids do auditOne id true

end PauliCtx.Audit

open PauliCtx PauliCtx.Config PauliCtx.Spectral PauliCtx.Hardness PauliCtx.Qm7

/-! ### general theorems: standard axioms only -/

#audit_pure
  mulPG_assoc mulPG_inv mulPG_central comm_rule canon_sq signK_even sign_symm
  Config.deg_gauge Config.mem_range_of_cycles Config.deg_eq_of_cycles
  prod_canon_even cycle_parity_eq_inversions deg_invariant deg_invariant_equiv
  Config.nc_bound nc_bound_attained nc_bound_mixture attenuation_iff
  Config.odd_cycle_forces_violation Config.uniform_cover Config.uniform_cover_deg
  Config.uniform_cover_rigid Config.uniform_cover_excess card_nontight_le
  Config.packing_le_deg packing_le_ratio Config.deg_le_half
  pauli_mul trace_pauli trace_pauli_mul pauli_hermitian pauli_comm pauli_completeness
  trace_cube_comm trace_cube_viol rayleigh cubic_trace_bound spectral_lower
  lines_W W_lower rho_le_half rho_tendsto_half infinitely_many_strict_jumps
  Config.cone_degree cone_degree_pauli
  Hardness.chain_lemma split_opt split_share split_middle one_equation_b0 one_equation_ind
  one_equation_sub
  neg_lines rho_le_explicit rho_lt_half rho_strict_jumps rho_not_eventually_const
  Config.transfer Config.transfer_cover Config.transfer_rigid Sp_trans_pairs Sp_trans_lines
  rho_max rho_mono rho_rigid Config.profile_bound Config.packing_orbit
  P_join mh_join tau_mul
  local_lower local_upper deg_phi induced_degree sub_degree toE3_opt reduction_sub reduction_ind
  no_deletion unavoidable Config.deg_two_points
  rademacher_abs cube_trace_lower sum_abs_ev exists_good_phase asy5_bound wallis_w delta_lower
  rate_explicit rho_window liminf_delta
  den1 den1_weak den1_gap deg_configX_map card_lines_configX_map den1_embed den1_embed_weak
  Config.condExp_avg Config.greedy_le Config.greedy_half den2
  Config.bestWins_eq Config.classicalValue_eq Config.classicalValue_ge Config.mixture_le
  Config.value_attained Config.agree_le_of_violated W_value_eq W_value_le W_value_ge W_value_tendsto
  operator_solution epr_expect alice_valid quantum_win quantum_perfect
  pauli_expand flat_Mg flat_trace_cube tight_of_flat
  B_mono spectral_lower_of_valid valid_ge_rayleigh ceiling
  mem_kerW_iff_lines qplus_mem_kerW qplus_not_linear violated_eq_iff fiberEquiv
  isotropic_finrank_le six_mul_lines_le den3_qubits
  lines_Xstd deg_Xstd_cone std_section_degree exists_sympData finrank_of_sympData
  finrank_radical_of_sympData section_deg_of_sympData W_section_degree W_section_degree'
  omega_span den1_intrinsic intrinsic_min
  psd_mul_zero_of_trace cubic_eq_case rank_one_of_idem tight_converse tight_iff
  finrank_hyp finrank_radical_hyp tangent_degree deg_W_pred
  lines_image_fun deg_configX_fun qplus_isQuad qminus_isQuad secQ_eq_image secQ_deg
  Q_section_degree_b mem_radical_hyp_self nontangent_degree
  omegaB_surjective quad_eq_qplus_add tvL_omega quad_tvL secQ_shift deg_secQ_shift deg_secQ_type
  qminus_eq deg_secQ_qminus card_secQ_type card_secQ_qminus
  std_sub_degree lines_XY deg_XY_cone deg_cone_GY secQ_eq_image_XY secQ_deg_of_sympData
  Q_section_degree_a Q_section_degree_a' radical_hyp_eq tangent_quad_degree tangent_quad_card card_XY
  W_ge_of W11_ge W13_ge W15_ge W17_ge W19_ge W21_ge

/-! ### theorems about specific finite geometries (native_decide certificates allowed) -/

#audit_comp
  den3_density W5_tangent W7_tangent Qplus7_nontangent Qminus7_nontangent
  deg_quad5 deg_quad5' deg_quad7_plus tangent_quad7 card_QP5 card_QM5 card_QM4
  tan_count_plus7 tan_count_minus7 tan_count_plus9 tangent_Qplus7 tangent_Qminus7 tangent_Qplus9
  qm7_ge_216 qm7_le_315 qm7_bounds Qminus7_bounds
  W5_eq_63 Qplus7_eq_315
  three_qubit_bound three_qubit_bound_le three_qubit_barrier doily_rigid
  W3_eq_3 W7_ge_1080 W7_ge_1451 W7_le_1575 W9_ge_28786 W9_le_31479
  Qp9_ge_6426 Qp9_ge_4783 Qp9_le_6975 Qm9_ge_4873 Qm9_le_7087 rho_chain
  tau3 tau4 W11_le W13_le W15_le W17_le
  Qp5_eq_21 Qm5_eq_9 Qp5_rigid Qm5_rigid
  Model.local_closure Model.mlab_spec lab_inj lab_ne_zero line_sum line_comm line_sgn Hardness.closure
  realized_degree realized_sub_degree induced_reduction
  Sint_QP Qplus7_flat Qplus7_eq_315_flat X496_lines X496_le_480 X496_ge_480 X496_eq_480
  steps7_ok kerW3_eq_zero finrank_kerW3 card_kerW3 rank_incW3 card_fiber_violated
  W19_le rho_chain_ext rho_strict_chain
