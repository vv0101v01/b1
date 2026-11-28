///|
/// batch7_wbtest.mbt — 批次七白盒測試（T201–T239）
test "B4 bilattice axioms" {
  assert_true(b7_commutative_ok())
  assert_true(b7_idempotent_ok())
  assert_true(b7_absorption_ok())
  assert_true(b7_associative_ok())
  assert_true(b7_distributive_ok())
  assert_true(b7_order_consistent_ok())
  assert_true(b7_interlacing_ok())
  assert_true(b7_demorgan_ok())
  assert_true(b7_conflation_ok())
  assert_true(b7_negation_antitone_ok())
}

///|
test "B4 lattice classification and symmetries" {
  let (lat, dia, ch) = b7_enumerate_four_element_lattices()
  assert_eq(lat, 2)
  assert_eq(dia, 1)
  assert_eq(ch, 1)
  assert_eq(b7_count_bilattice_automorphisms(), 1)
  assert_eq(b7_count_bilattice_symmetries(), 4)
  let (c, s) = b7_b2_hom_surjective_count()
  assert_eq(c, 3)
  assert_eq(s, 1)
  let (mono, alldes) = b7_unary_monotone_stats()
  assert_eq(mono, 36)
  assert_eq(alldes, 6)
}

///|
test "B4 paraconsistency" {
  assert_true(b7_explosion_fails())
  assert_false(b7_excluded_middle_tautology())
  assert_false(b7_modus_ponens_valid())
  let (p, q) = b7_mp_counterexample()
  assert_eq(b7_code(p), 3)
  assert_eq(b7_code(q), 0)
  let (a, b, c) = b7_product_counts(3)
  assert_eq(a, 64L)
  assert_eq(b, 27L)
  assert_eq(c, 8L)
}

///|
test "fast-leaf t-product equals circular convolution" {
  let a = b7_ten3_rand(3, 3, 4, 11L)
  let b = b7_ten3_rand(3, 3, 4, 22L)
  let cs = b7_tprod_spectral(a, b)
  let cd = b7_tprod_direct(a, b)
  assert_true(b7_ten3_dist(cs, cd) < 1.0e-10)
  let id = b7_ten3_identity(3, 4)
  assert_true(b7_ten3_dist(b7_tprod_spectral(a, id), a) < 1.0e-10)
  assert_true(b7_dft_matches_fft(8))
  assert_true(b7_dft_matches_fft(16))
  assert_true(b7_parseval_error(a) < 1.0e-10)
}

///|
test "projective invariance and t-SVD" {
  let (ok, err) = b7_projective_invariance_check(5L)
  assert_true(ok)
  assert_true(err < 1.0e-9)
  let a = b7_ten3_rand(3, 3, 4, 11L)
  let (f1, m1) = b7_rank_r_error(a, 1)
  let (f2, m2) = b7_rank_r_error(a, 2)
  assert_true((f1 - m1).abs() < 1.0e-9)
  assert_true((f2 - m2).abs() < 1.0e-9)
  assert_true(m2 < m1)
  let (nv, ft, ratio) = b7_leaf_cost_ratio(64)
  assert_eq(nv, 4096)
  assert_eq(ft, 192)
  assert_true(ratio > 20.0)
  assert_true(b7_tnn(a) >= b7_ten3_frob(a) / 2.0 - 1.0e-9)
}

///|
test "Haken-Zwanzig reduction" {
  let a = b7_mat_of(4, 4, [
    -1.0, 0.1, 0.3, 0.0, 0.1, -1.2, 0.0, 0.25, 0.3, 0.0, -20.0, 0.4, 0.0, 0.25, 0.4,
    -25.0,
  ])
  assert_true(b7_schur_spectrum_error(a, 2) < 1.0e-2)
  let (x, res, _) = b7_invariant_manifold(a, 2, 60)
  assert_true(res < 1.0e-10)
  assert_true(b7_mat_frob(b7_mat_sub(x, b7_adiabatic_map(a, 2))) < 1.0)
  assert_true(b7_markov_limit_error(a, 2, 40.0, 4000) < 1.0e-2)
  assert_true(b7_gle_check(a, 2, 6.0, 2000) < 1.0e-2)
}

///|
test "adiabatic error scales like epsilon squared" {
  let epss = [0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001]
  let errs : Array[Double] = []
  for e in epss {
    let (_, er) = b7_two_mode_error(e, 0.1)
    errs.push(er)
  }
  let p = b7_fit_exponent(epss, errs)
  assert_true((p - 2.0).abs() < 0.15)
  let c1 = b7_cm_residual(0.3, 0.02, 0.5, 0.2, 1)
  let c2 = b7_cm_residual(0.3, 0.02, 0.5, 0.2, 2)
  let c3 = b7_cm_residual(0.3, 0.02, 0.5, 0.2, 3)
  assert_true(c1 > c2 && c2 > c3)
}

///|
test "4^64 bigint and CP/TT parameter counts" {
  assert_eq(b7_big_4_64(), "340282366920938463463374607431768211456")
  assert_eq(b7_big_4_64_bits(), 129)
  assert_eq(b7_tt_crossover_rank(), 1)
  for (r, cp, tt) in b7_cp_vs_tt_table() {
    if r >= 2 {
      assert_true(tt > cp)
    }
  }
}

///|
test "GHZ CP rank equals 4 and ALS convergence" {
  let (_, _, lb, ub) = b7_ghz_rank_squeeze(4, 3)
  assert_eq(lb, 4)
  assert_eq(ub, 4)
  assert_true(b7_ghz_als_residuals(4, 300) < 1.0e-9)
  assert_true((b7_ghz_als_residuals(3, 300) - 0.5).abs() < 1.0e-9)
  let sweep = b7_cp_rank_sweep(120)
  let mut last = 2.0
  for (_, rr) in sweep {
    assert_true(rr <= last + 1.0e-12)
    last = rr
  }
  assert_true(last < 1.0e-2)
}

///|
test "Tate algorithm: conductors and FF tower" {
  let c11 = b7_wcurve(0L, -1L, 1L, -10L, -20L)
  let c37 = b7_wcurve(0L, 0L, 1L, -1L, 0L)
  assert_eq(b7_w_disc(c11), -161051L)
  assert_eq(b7_conductor(c11).0, 11L)
  assert_eq(b7_conductor(c37).0, 37L)
  assert_true(b7_ff_period_six_ok(5L))
  assert_true(b7_ff_period_six_ok(7L))
  assert_true(b7_component_count_identity_ok(5L, 12))
  assert_true(b7_kodaira_chain_consistency(5L))
  assert_true(b7_hasse_ok(c11, 97L))
  assert_true(b7_semistable_criterion_ok(c11, 11L))
}

///|
test "p-adic arithmetic, Newton polygon, intersection form" {
  assert_true(b7_zp_ring_ok(5L, 3))
  assert_true(b7_zp_euler_ok(5L, 2))
  assert_eq(@b7.b7_zp_unit_count(5L, 3), 100L)
  let (root, ok) = b7_hensel([-2L, 0L, 1L], 7L, 4, 3L)
  assert_true(ok)
  assert_eq(b7_poly_eval([-2L, 0L, 1L], root, b7_ipow(7L, 4)), 0L)
  let poly : Array[(Int32, Int32)] = [(0, 4), (6, 0)]
  assert_eq(@b7.b7_lattice_length((6, 4)), 2)
  assert_eq(b7_blowup_count(b7_newton_polygon(poly)), 1)
  assert_eq(b7_chain_length(b7_newton_polygon(poly)), 2)
  let (a, b, okp) = b7_pick_check(poly)
  assert_true(okp)
  assert_eq(a, b)
  assert_true(b7_negative_definite(5))
  let (fw, semi, artin) = b7_fundamental_cycle(5)
  assert_true(semi && artin && fw < 1.0e-12)
}

///|
test "p-adic Hodge, Witt vectors, perfectoid tilt" {
  let mut adm = true
  for (name, _, _, ok) in b7_admissibility_table() {
    if name.has_prefix("反例") {
      assert_false(ok)
    } else if !ok {
      adm = false
    }
  }
  assert_true(adm)
  assert_true(b7_frobenius_monodromy_ok(5L))
  assert_true(b7_monodromy_nilpotent_ok())
  assert_true(b7_witt_bijection_ok(5L, 3))
  assert_true(b7_witt_bijection_ok(2L, 4))
  assert_true(b7_witt_add_compatible_ok(5L, 2))
  assert_true(b7_witt_add_compatible_ok(3L, 3))
  assert_true(
    b7_frobenius_image_finite_field(5L).0 ==
    b7_frobenius_image_finite_field(5L).1,
  )
  assert_true(
    b7_frobenius_image_dual_numbers(5L).0 !=
    b7_frobenius_image_dual_numbers(5L).1,
  )
  assert_true(b7_tilt_involution_ok(3L, 3))
  assert_true(b7_perfectoid_tower_ok(3L, 5))
}

///|
test "p-adic Langlands categorification counts" {
  assert_eq(b7_count_characters(3L), 2L)
  assert_eq(b7_count_characters(5L), 4L)
  assert_eq(b7_count_characters(7L), 6L)
  assert_true(b7_plancherel(7L).2)
  assert_true(b7_rank_bookkeeping_ok().0)
  let (h0, h1, _, _) = b7_cohomology_unipotent(3L)
  assert_eq(h0, 2)
  assert_eq(h1, 1)
  let (t0, t1) = b7_cohomology_trivial(5L)
  assert_eq(t0, 1)
  assert_eq(t1, 1)
  let (_, d1, _, dm) = b7_local_deformation_dim(0)
  assert_eq(d1, 3)
  assert_eq(dm, 3)
  assert_true(b7_deformation_twist_invariance_ok())
  assert_true(b7_good_reduction_ht_ok())
  assert_true(b7_semistable_slope_range_ok())
}
