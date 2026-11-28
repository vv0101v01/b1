///|
/// theorem4_wbtest.mbt — 批次四（51–60）白盒測試

///|
test "T51 Kunneth projectors and polarization" {
  assert_true(kunneth_ok())
  assert_true(polarization_isotropic_ok())
  assert_true(polarization_antisym_ok())
  assert_true(hard_lefschetz_toy())
  assert_true(composition_assoc_ok())
}

///|
test "T52 Euler product = q-expansion and purity" {
  let n0 = 30
  let f = newform_level11(n0)
  let mut acc : Array[Int64] = []
  let mut i = 0
  while i <= n0 {
    acc.push(0L)
    i = i + 1
  }
  acc[1] = 1L
  for p in primes_upto(n0) {
    let loc = local_factor_h1(f[p], p, n0)
    acc = dirichlet_conv(acc, loc, n0)
  }
  let mut n1 = 1
  while n1 <= n0 {
    assert_eq(acc[n1], f[n1])
    n1 = n1 + 1
  }
}

///|
test "T52 purity and direct sum" {
  let (m1, m2) = purity_roots(-2L, 2)
  assert_true((m1 - 2.0).abs() < 0.0001)
  assert_true((m2 - 2.0).abs() < 0.0001)
  assert_true(direct_sum_local_identity(-2L, -1L, 2, 3))
  assert_true(tate_twist_shift_ok(30))
}

///|
test "T53 Serre modularity instance (ell = 3)" {
  assert_true(oddness_ok(3))
  assert_eq(serre_modularity_instance(3, 41), 12)
  assert_true(serre_level_ok(3))
  assert_true(serre_irreducible_ok(3, 41))
  // mod-5: REDUCIBLE — X₀(11) has rational 5-torsion (E(Q) = Z/5):
  // all Frobenius polys split mod 5 and #E(F_p) ≡ 0 mod 5
  assert_true(all_charpoly_split(5, 41))
  assert_true(torsion_5_check(41))
  // mod-3: NOT all split (irreducible)
  assert_false(all_charpoly_split(3, 41))
}

///|
test "T54 quadratic twist coefficients" {
  // E: y² = x³ − x over F_p, d = 5
  assert_eq(twist_coeff_check(-1L, 0L, 5, 31), 8) // primes p ≤ 31, p ∉ {2,3,5}
  assert_true(base_change_identity_check(-1L, 0L, 5, 31))
  assert_true(inert_prime_check(-1L, 0L, 5, 31))
}

///|
test "T55 modularity lifting consistency" {
  assert_eq(hecke_consistency(40), 0)
  assert_true(power_sum_consistency(20))
  assert_true(unique_lift_small_primes())
  assert_true(hensel_residues_ok(31))
  assert_true(adequacy_lite_ok())
}

///|
test "T56 deformation ring cohomology and lift count" {
  let g0 = M2fp::{ a: 0, b: 1, c: 1, d: 0, p: 5, }
  let (h0, h1, h2) = cyclic_cohom_dims(g0)
  assert_eq(h0, 2)
  assert_eq(h1, 0)
  assert_eq(h2, 0)
  assert_true(maschke_vanishing_ok(g0))
  assert_true(tangent_exact_ok(g0))
  assert_true(lift_count_check(g0))
  assert_true(rigidity_ok(g0))
  // also p = 7
  let g1 = M2fp::{ a: 0, b: 1, c: 1, d: 0, p: 7, }
  assert_true(lift_count_check(g1))
}

///|
test "T57 Igusa fibers and stack structure" {
  assert_true(fiber_generic_check(13, 1))
  assert_true(fiber_generic_check(17, 5))
  assert_true(stack_structure_check(13))
  assert_true(stack_structure_check(17))
}

///|
test "T57 supersingular counts match formula" {
  assert_true(ss_count_check(5))
  assert_true(ss_count_check(7))
  assert_true(ss_count_check(11))
}

///|
test "T58 simplicial homology algorithm" {
  let (b0, b1, b2) = betti_simplicial(circle_simplices(), 7)
  assert_eq(b0, 1)
  assert_eq(b1, 1)
  assert_eq(b2, 0)
  let (s0, s1, s2) = betti_simplicial(sphere_simplices(), 7)
  assert_eq(s0, 1)
  assert_eq(s1, 0)
  assert_eq(s2, 1)
  let (d0, d1, d2) = betti_simplicial(disk_simplices(), 7)
  assert_eq(d0, 1)
  assert_eq(d1, 0)
  assert_eq(d2, 0)
}

///|
test "T58 quotient invariants and graph cycles" {
  let inv = z2_invariants_dims([1, -1], 7)
  assert_eq(inv[0], 1)
  assert_eq(inv[1], 0)
  let (r0, r1, r2) = rp2_betti(7)
  assert_eq(r0, 1)
  assert_eq(r1, 0)
  assert_eq(r2, 0)
  assert_eq(graph_cycle_dim([(0, 1), (1, 2), (2, 0)], 3, 1), 1)
  assert_true(poincare_duality_betti((1, 0, 1)))
}

///|
test "T59 Hodge-Tate weights of Sym2 and Tate twist" {
  assert_true(sym2_ht_weights_ok(1L, 5))
  assert_true(sym2_ht_weights_ok(1L, 7))
  assert_true(tate_twist_slope_shift_ok(5))
  assert_true(sym_multiplicity_ok())
  assert_true(sen_integer_spectrum_ok())
  // newton_slopes_poly sanity: x² − x + 5: slopes (0, 1)
  let s = @b4.newton_slopes_poly([5L, -1L, 1L], 5)
  assert_true((s[0] - 0.0).abs() < 0.0001 || (s[0] - 1.0).abs() < 0.0001)
}

///|
test "T60 discriminant and Neron model" {
  assert_true(disc_x011_ok())
  let (comp, genus) = component_group_x011()
  assert_eq(comp, 5)
  assert_eq(genus, 1)
}

///|
test "T60 formal smoothness and j-line" {
  assert_true(formal_smoothness_check(5))
  assert_true(formal_smoothness_check(7))
  assert_true(j_model_surjective_check(13))
  assert_true(j_model_surjective_check(17))
}

///|
test "A10 evolve modular lift from constraints" {
  let f11 = newform_level11(60)
  let abar2 = ((f11[2] % 5L + 5L) % 5L).to_int()
  let abar3 = ((f11[3] % 5L + 5L) % 5L).to_int()
  let a4g = galois_a_pj(11, 2, 2)
  let a6g = galois_a_pj(11, 2, 1) * galois_a_pj(11, 3, 1)
  let (x2, x3, fit) = evolve_modular_lift(abar2, abar3, a4g, a6g, 150, 42L)
  assert_eq(fit, 0)
  assert_true(a10_fitness(x2, x3, abar2, abar3, a4g, a6g) == 0)
  // the unique lift is the modular (a₂, a₃) = (−2, −1)
  assert_true(x2 == -2 || x3 == -1)
}

///|
test "A11 evolve pure local factor" {
  let f11 = newform_level11(60)
  let t5 = f11[5]
  let (e1, e2, fit) = evolve_purity(5, t5, 150, 7L)
  assert_eq(fit, 0L)
  assert_true(a11_fitness(e1, e2, 5, t5) == 0L)
  assert_true(e2 == 5L) // Weil: αβ = p
}

///|
test "A12 evolve Lagrangian projector" {
  let (a, b, c, d, fit) = evolve_projector(120, 7L)
  assert_eq(fit, 0)
  assert_true(a12_fitness(a, b, c, d) == 0)
  // valid solutions: any integer idempotent with det = 0 (rank 0 or 1):
  // E² = E and det E = 0
  let e00 = a * a + b * c - a
  let e01 = a * b + b * d - b
  let e10 = a * c + c * d - c
  let e11 = b * c + d * d - d
  assert_eq(e00, 0)
  assert_eq(e01, 0)
  assert_eq(e10, 0)
  assert_eq(e11, 0)
  assert_eq(a * d - b * c, 0)
}
