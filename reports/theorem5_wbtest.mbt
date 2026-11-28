///|
/// White-box tests for batch 5 (T181–T190, A13–A15).

///|
test "T181 octonion from string diagrams" {
  let k = markov_precision()
  assert_true(markov_vanishes(k))
  assert_true(markov_gluing_ok(k))
  assert_true(adj_identity_ok(k))
  assert_true(interchange_ok())
  assert_true(octonion_alternative_ok())
  assert_true(octonion_norm_mult_ok())
  assert_true(markov_implies_octonion_ok())
}

///|
test "T182 noncommutative diagrams and tree spectral pages" {
  assert_true(nc_interchange_ok())
  assert_true(tree_spectral_pages_ok(3))
  assert_true(tree_les_exact_ok())
  assert_true(@b5.nc_tree_spectral_ok())
}

///|
test "T183 fixed points and tree-string homology" {
  assert_true(idempotent_count_ok())
  assert_true(burnside_idempotents_ok())
  assert_true(tree_string_homology_ok())
  assert_true(involution_invariants_ok())
  assert_true(@b5.tree_solution_homology_ok())
}

///|
test "T184 deeply ramified supercuspidal" {
  assert_true(deep_conductor_ok())
  assert_true(supercuspidal_orbits_ok())
  assert_true(supercuspidal_irred_ok())
  assert_true(deep_via_unit_ok())
  assert_true(@b5.supercuspidal_ok())
}

///|
test "T185 depth of representations" {
  assert_true(depth_filtration_ok())
  assert_true(depth_subadditive_ok())
  assert_true(depth_breakpoints_ok())
  assert_true(@b5.depth_ok())
}

///|
test "T186 Yu construction" {
  assert_true(schrodinger_homomorphism_ok())
  assert_true(heisenberg_irreducible_ok())
  assert_true(yu_torus_ok())
  assert_true(@b5.yu_ok())
}

///|
test "T187 Kaletha dihedral LLC" {
  assert_true(char_identity_ok())
  assert_true(dihedral_irred_ok())
  assert_true(regular_matching_ok())
  assert_true(@b5.kaletha_ok())
}

///|
test "T188 semisimple vs non-semisimple parameters" {
  assert_true(nilpotent_class_ok())
  assert_true(weil_deligne_ok())
  assert_true(monodromy_detector_ok())
  assert_true(springer_classes_ok())
  assert_true(@b5.params_ok())
}

///|
test "T189 Plancherel and mild functoriality" {
  assert_true(plancherel_ok())
  assert_true(convolution_theorem_ok())
  assert_true(inversion_ok())
  assert_true(mild_functorial_ok())
  assert_true(@b2.plancherel_all_ok())
}

///|
test "T190 wave front set" {
  assert_true(wf_examples_ok())
  assert_true(wf_union_ok())
  assert_true(wf_product_ok())
  assert_true(@b5.wavefront_ok())
}

///|
test "A13 noncommutative diagram evolution" {
  assert_true(a13_converges_ok())
}

///|
test "A14 deep supercuspidal evolution" {
  assert_true(a14_converges_ok())
}

///|
test "A15 wave front evolution" {
  assert_true(a15_converges_ok())
}

///|
test "report5 all PASS" {
  assert_eq(report5_probe(), 0)
}

///|
fn report5_probe() -> Int32 {
  // re-evaluate every report5 condition
  let mut fails = 0
  let k = markov_precision()
  if !markov_vanishes(k) {
    fails = fails + 1
  }
  if !markov_gluing_ok(k) {
    fails = fails + 1
  }
  if !adj_identity_ok(k) {
    fails = fails + 1
  }
  if !interchange_ok() {
    fails = fails + 1
  }
  if !octonion_alternative_ok() {
    fails = fails + 1
  }
  if !octonion_norm_mult_ok() {
    fails = fails + 1
  }
  if !nc_interchange_ok() {
    fails = fails + 1
  }
  if !tree_spectral_pages_ok(3) {
    fails = fails + 1
  }
  if !tree_les_exact_ok() {
    fails = fails + 1
  }
  if !idempotent_count_ok() {
    fails = fails + 1
  }
  if !burnside_idempotents_ok() {
    fails = fails + 1
  }
  if !tree_string_homology_ok() {
    fails = fails + 1
  }
  if !involution_invariants_ok() {
    fails = fails + 1
  }
  if !@b5.supercuspidal_ok() {
    fails = fails + 1
  }
  if !@b5.depth_ok() {
    fails = fails + 1
  }
  if !@b5.yu_ok() {
    fails = fails + 1
  }
  if !@b5.kaletha_ok() {
    fails = fails + 1
  }
  if !@b5.params_ok() {
    fails = fails + 1
  }
  if !@b2.plancherel_all_ok() {
    fails = fails + 1
  }
  if !@b5.wavefront_ok() {
    fails = fails + 1
  }
  if !a13_converges_ok() {
    fails = fails + 1
  }
  if !a14_converges_ok() {
    fails = fails + 1
  }
  if !a15_converges_ok() {
    fails = fails + 1
  }
  fails
}
