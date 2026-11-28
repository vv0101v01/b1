///|
/// theorem3_wbtest.mbt — 批次三（101–110）白盒測試

///|
test "T101 dual involution and pi1-center swap" {
  let sl2 = root_datum_A1_sc()
  let d = sl2.dual()
  let dd = d.dual()
  assert_eq(dd.pi1, 1)
  assert_eq(dd.center, 2)
  assert_eq(d.pi1, 2)
  assert_eq(d.center, 1)
}

///|
test "T101 B2 dual is C2 (long-short swap)" {
  let b2 = root_datum_B2()
  let c2 = root_datum_C2()
  let d = b2.dual()
  assert_eq(d.cartan[0][0], 2)
  assert_eq(d.cartan[0][1], -2)
  assert_eq(d.symm[0], 1)
  assert_eq(d.symm[1], 2)
  assert_true(c2.symmetrizable())
  assert_true(b2.symmetrizable())
}

///|
test "T101 Weyl group orders A2 = 6, B2 = 8, A1 = 2" {
  assert_eq(weyl_group_order(root_datum_A2_sc()), 6)
  assert_eq(weyl_group_order(root_datum_B2()), 8)
  assert_eq(weyl_group_order(root_datum_A1_sc()), 2)
}

///|
test "T102 dims: S12 = 1, S28 = 2, M16 monomials = 2" {
  assert_eq(cusp_basis_sl2(12).length(), 1)
  assert_eq(cusp_basis_sl2(28).length(), 2)
  assert_eq(monomials_e4_e6(16).length(), 2)
}

///|
test "T102 Hecke commutativity on S28 and integrality" {
  let basis = cusp_basis_sl2(28)
  let t2 = hecke_matrix_sl2(basis, 2, 28)
  let t3 = hecke_matrix_sl2(basis, 3, 28)
  assert_true(mat2_eq(mat2_mul(t2, t3), mat2_mul(t3, t2), 0.01))
  assert_true(mat2_integral(t2, 0.01))
  assert_true(mat2_integral(t3, 0.01))
}

///|
test "T102 tau(2) = -24 and Ramanujan bound" {
  assert_eq(delta_series(8).0[2], -24L)
  assert_eq(eisenstein_eigenvalue(2, 12), 2049L)
  let b = ramanujan_bound(2, 12)
  assert_true(2049.0 > b)
  assert_true(24.0 <= b)
}

///|
test "T103 x^3-2 has full S3 pattern set" {
  let pats = observed_patterns([-2L, 0L, 0L, 1L], 200, [2, 3])
  let mut h111 = false
  let mut h12 = false
  let mut h3 = false
  for pt in pats {
    if pattern_eq(pt, pattern_identity(3)) {
      h111 = true
    }
    if pattern_eq(pt, pattern_transposition(3)) {
      h12 = true
    }
    if pattern_eq(pt, pattern_cycle(3)) {
      h3 = true
    }
  }
  assert_true(h111)
  assert_true(h12) // transposition present: not A3
  assert_true(h3)
}

///|
test "T103 zeta cyclo coefficients = character sums" {
  let chars = dir_chars_mod7()
  let lhs = sum_chars_at(chars, 3)
  assert_eq(zeta_cyclo_coeff_prime(3), 0)
  assert_true(lhs.0.abs() < 0.001)
  let lhs2 = sum_chars_at(chars, 29) // 29 = 1 mod 7
  assert_eq(zeta_cyclo_coeff_prime(29), 6)
  assert_true((lhs2.0 - 6.0).abs() < 0.001)
}

///|
test "T104 Newton slopes: ordinary (0,1), supersingular (0.5,0.5)" {
  let (a1, b1) = newton_slopes_quadratic(-1L, 5L, 5)
  assert_true((a1 == 0.0 && b1 == 1.0) || (a1 == 1.0 && b1 == 0.0))
  let (a2, b2) = newton_slopes_quadratic(0L, 5L, 5)
  assert_true((a2 - 0.5).abs() < 0.0001)
  assert_true((b2 - 0.5).abs() < 0.0001)
}

///|
test "T104 weak admissibility" {
  let h = HodgeData::{ weights: [0, 1], }
  assert_true(weak_admissible_2d(h, 0.0, 1.0))
  assert_true(weak_admissible_2d(h, 0.5, 0.5))
  assert_false(weak_admissible_2d(h, 1.0, 1.0)) // total 2 ≠ 1
  assert_false(weak_admissible_2d(h, -1.0, 2.0)) // partial violation
}

///|
test "T105 de Rham dimensions and cup pairing" {
  assert_eq(hyperelliptic_genus(5), 2)
  assert_eq(hyperelliptic_genus(3), 1)
  let (f0, f1, f2) = h1_filtration_dims(2)
  assert_eq(f0, 4)
  assert_eq(f1, 2)
  assert_eq(f2, 0)
  assert_eq(det2i(cup_matrix_genus1()), 1)
}

///|
test "T106 Frobenius-monodromy N phi = p phi N" {
  assert_true(frobenius_monodromy_ok(5))
  assert_true(conjugation_form_ok(5))
  assert_true(monodromy_nilpotent(5))
  assert_false(crystalline_iff_n_zero(tate_curve_monodromy(5).0))
  assert_eq(tate_kernel_dim(5), 1)
}

///|
test "T107 degeneracy relations and tower growth" {
  let sys = make_degen_system(3)
  assert_true(degen_relations_ok(sys, 3))
  assert_true(degen_relations_ok(make_degen_system(2), 2))
  assert_true(hecke_commute_ok())
  assert_true(tower_growth_ok())
}

///|
test "T108 Ramanujan sieve separation" {
  assert_true(sieve_weight12_ok())
  assert_true(middle_vanish_ok())
  assert_eq(@b3.ramanujan_classify(-24L, 2, 12), "cuspidal")
  assert_eq(@b3.ramanujan_classify(2049L, 2, 12), "non-cuspidal")
}

///|
test "T109 local-global match p ≤ 47, j ≤ 3" {
  assert_eq(local_global_check(11, 47, 3), 42)
  assert_true(steinberg_check(11, 3))
  assert_true(det_compatibility(11))
}

///|
test "T110 Carlitz module law on F9 and F5" {
  assert_true(carlitz_module_law_ok(3, 2, 1, [1, 2, 1], [2, 1]))
  assert_true(carlitz_module_law_ok(5, 1, 2, [1, 1, 1], [3, 2]))
  assert_true(carlitz_t_square_check(3, 2, 1))
}

///|
test "T110 zeta P1 and GL2 decomposition" {
  assert_true(zeta_p1_check(3, 8))
  assert_true(zeta_p1_check(5, 8))
  // E/F_5: power sums identity
  let e = x011_curve()
  let counts : Array[Int64] = []
  let mut n = 0
  while n <= 3 {
    counts.push(e.count_points(5, n + 1).to_int64())
    n = n + 1
  }
  assert_true(zeta_gl2_check(counts, 5, 3))
  let a1 = 6 - counts[0].to_int()
  assert_true(satake_frobenius_check(a1, 5, counts, 3))
}

///|
test "A7 evolve Hodge-Newton to weakly admissible slopes" {
  let (x, y, f, _) = evolve_hodge_newton(150, 42L)
  assert_eq(f, 0)
  assert_true(a7_fitness(x, y) == 0)
  // admissible niches: (0,1),(1,0),(5,5),(−0,... ) check sums
  assert_true(x + y == 10 && x >= 0 && y >= 0)
}

///|
test "A8 evolve local factor from dual sources" {
  let (ok, auto_a, gal_a) = modularity_check_prime(5)
  assert_true(ok)
  let (e1, e2, f) = evolve_localglobal(5L, auto_a, gal_a, 150, 7L)
  assert_eq(f, 0L)
  assert_true(a8_fitness(e1, e2, auto_a, gal_a, 5L) == 0L)
}

///|
test "A9 evolve function-field power sums" {
  let e = x011_curve()
  let counts : Array[Int64] = []
  let mut n = 0
  while n <= 2 {
    counts.push(e.count_points(7, n + 1).to_int64())
    n = n + 1
  }
  let (s1, s2) = evolve_ff_satake(7L, counts, 99L)
  let t1 = 7L + 1L - counts[0]
  let t2 = 49L + 1L - counts[1]
  assert_eq(s1, t1)
  assert_eq(s2, t2)
  assert_eq(t1 * t1 - t2, 14L) // = 2αβ = 2q
}
