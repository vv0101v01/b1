///|
/// White-box tests for batch 6 (T191–T200, A16–A18).

///|
test "T191 derived algebraic geometry" {
  assert_true(koszul_examples_ok())
  assert_true(koszul_excess_ok())
  assert_true(action_groupoid_ok())
  assert_true(@b6.derived_ok())
}

///|
test "T192 symplectic and derived symplectic" {
  assert_true(symplectic_form_ok())
  assert_true(jacobi_ok())
  assert_true(reduction_dim_ok())
  assert_true(shifted_symplectic_ok())
  assert_true(@b6.symplectic_ok())
}

///|
test "T193 graded Hamiltonian spaces" {
  assert_true(comoment_lie_ok())
  assert_true(jacobi_poly_ok())
  assert_true(weight_grading_ok())
  assert_true(@b6.hamgrad_ok())
}

///|
test "T194 hyperkähler and mirror symmetry" {
  assert_true(quaternion_relations_ok())
  assert_true(kahler_forms_ok())
  assert_true(duality_involution_ok())
  assert_true(hodge_mirror_ok())
  assert_true(monodromy_mirror_ok())
  assert_true(@b6.hyperkahler_ok())
}

///|
test "T195 arithmetic mirror symmetry" {
  assert_true(hypergeo_two_paths_ok())
  assert_true(hodge_flip_ok())
  assert_true(dwork_pencil_ok())
  assert_true(@b6.arithmirror_ok())
}

///|
test "T196 group schemes and fppf cohomology" {
  assert_true(mu_points_ok())
  assert_true(kummer_ok())
  assert_true(cartier_dual_ok())
  assert_true(alpha_p_ok())
  assert_true(@b6.grpscheme_ok())
}

///|
test "T197 Hecke action on shtuka moduli" {
  assert_true(hecke_relation_ok())
  assert_true(shtuka_count_ok())
  assert_true(satake_ok())
  assert_true(@b6.hecke_ok())
}

///|
test "T198 categorical LLC equivalence" {
  assert_true(char_orthogonality_ok())
  assert_true(fusion_ok())
  assert_true(k0_match_ok())
  assert_true(@b6.llccat_ok())
}

///|
test "T199 arithmetic statistics" {
  assert_true(character_sum_identity_ok())
  assert_true(weil_bound_ok())
  assert_true(heegner_ok())
  assert_true(@b6.arithstat_ok())
}

///|
test "T200 global closed loop" {
  assert_true(closed_loop_x011_ok())
  assert_true(global_local_ok())
  assert_true(gl1_reciprocity_ok())
  assert_true(gl1_character_ok())
  assert_true(@b6.closedloop_ok())
}

///|
test "A16 transversality evolution" {
  assert_true(a16_converges_ok())
}

///|
test "A17 Hecke eigenfunction evolution" {
  assert_true(a17_converges_ok())
}

///|
test "A18 closed-loop trace evolution" {
  assert_true(a18_converges_ok())
}

///|
test "report6 all PASS" {
  assert_eq(report6_probe(), 0)
}

///|
fn report6_probe() -> Int32 {
  let mut fails = 0
  if !@b6.derived_ok() {
    fails = fails + 1
  }
  if !@b6.symplectic_ok() {
    fails = fails + 1
  }
  if !@b6.hamgrad_ok() {
    fails = fails + 1
  }
  if !@b6.hyperkahler_ok() {
    fails = fails + 1
  }
  if !@b6.arithmirror_ok() {
    fails = fails + 1
  }
  if !@b6.grpscheme_ok() {
    fails = fails + 1
  }
  if !@b6.hecke_ok() {
    fails = fails + 1
  }
  if !@b6.llccat_ok() {
    fails = fails + 1
  }
  if !@b6.arithstat_ok() {
    fails = fails + 1
  }
  if !@b6.closedloop_ok() {
    fails = fails + 1
  }
  if !a16_converges_ok() {
    fails = fails + 1
  }
  if !a17_converges_ok() {
    fails = fails + 1
  }
  if !a18_converges_ok() {
    fails = fails + 1
  }
  fails
}
