///|
/// theorem2_wbtest.mbt — 批次二（31–40 + A4–A6）白箱測試

///|
test "T31 tate module char poly" {
  let e = WCurve(0, 0, 0, 1, 1) // y² = x³ + x + 1
  let mut checked = false
  let mut kk = 1
  while kk <= 3 && !checked {
    let mut ell = 2
    while ell <= 3 && !checked {
      let tors = torsion_points(e, 7, kk, ell)
      if tors.length() >= ell * ell - 1 {
        let (tro, deto, _) = verify_tate_module(e, 7, kk, ell)
        assert_true(tro)
        assert_true(deto)
        checked = true
      }
      ell = ell + 1
    }
    kk = kk + 1
  }
  assert_true(checked)
}

///|
test "T31b representation axiom" {
  let err = rep_power_consistency(WCurve(0, 0, 0, 1, 1), 7, 3, 2, 3)
  assert_eq(err, 0)
}

///|
test "T32a frobenius fixed fields" {
  let mut k = 1
  while k <= 4 {
    assert_true(fixed_field_theorem_ok(2, 4, k))
    k = k + 1
  }
  assert_eq(@b2.frobenius_order(3, 4), 4)
}

///|
test "T32b cyclotomic splitting" {
  assert_eq(frobenius_in_cyclotomic(2, 7), 3)
  assert_true(prime_split_cyclotomic(2, 7) == (3, 2))
  assert_true(prime_split_cyclotomic(5, 7) == (6, 1))
  assert_eq(frobenius_in_cyclotomic(7, 8), 2) // ord_8(7) = 2
  assert_eq(frobenius_in_cyclotomic(2, 8), -1) // gcd(2, 8) > 1: ramified
}

///|
test "T33a artin = dirichlet" {
  let chi = dir_char_mod5()
  let s1 = dirichlet_series_char(chi, 300, 6.0)
  let s2 = euler_product_char(chi, 100, 6.0)
  assert_true(s1.sub(s2).abs() < 0.0000001)
}

///|
test "T33b artin direct sum" {
  let err = artin_direct_sum_error(
    dir_char_mod5(),
    dir_char_chi4(),
    300,
    80,
    6.0,
  )
  assert_true(err < 0.000001)
}

///|
test "T33c zeta_qi = zeta * L(chi4)" {
  let lhs = zeta_qi_series(200, 6.0)
  let rhs = zeta_series(200, 6.0) * l_chi4_series(200, 6.0)
  let diff = lhs - rhs
  let abs = if diff < 0.0 { -diff } else { diff }
  assert_true(abs < 0.000001)
  assert_eq(r2_direct(25), r2_formula(25))
  assert_eq(r2_formula(65), 16) // 65 = 1²+8² = 4²+7²: r₂ = 16
}

///|
test "T34a rankin-selberg" {
  let a = delta_series(50)
  let b = rankin_selberg_coefficients(a.0, 12, 50)
  let ds = dirichlet_series_double(b, 50, 14.0)
  let ep = rankin_selberg_euler(a.0, 12, 40, 14.0)
  let diff = ds - ep
  let abs = if diff < 0.0 { -diff } else { diff }
  assert_true(abs < 0.01)
}

///|
test "T34b sym2 satake identities" {
  let a = delta_series(20)
  assert_true(sym2_local_identity_error(a.0, 12, 15) < 0.5)
  assert_eq(functorial_power_sum_error(a.coeff(2), 2, 12, 5), 0)
}

///|
test "T35 sym2 and adj functoriality" {
  let a = delta_series(20)
  let (e1, e2, e3) = sym2_satake(a.coeff(2), 2, 12)
  assert_eq(e1, a.coeff(2) * a.coeff(2) - 2048)
  assert_eq(e2, 2048L * e1)
  assert_eq(e3, 2048L * 2048L * 2048L)
  let (ae1, _, _) = adj_satake(a.coeff(2), 2, 12)
  assert_eq(ae1, a.coeff(2) * a.coeff(2) - 2 * 2048)
}

///|
test "T36 base change quadratic" {
  let a = delta_series(12)
  let b3 = base_change_coefficient(a.0[3], 3, 12, legendre(5L, 3L))
  assert_eq(b3, a.0[3] * a.0[3] - 2 * 177147)
  let b11 = base_change_coefficient(a.0[11], 11, 12, legendre(5L, 11L))
  assert_eq(b11, 2 * a.0[11]) // (5/11) = 1: 11 splits in Q(√5)
}

///|
test "T37a automorphic induction" {
  assert_true(ai_coefficient_error(30) < 0.000001)
}

///|
test "T37b inert primes vanish" {
  let gl2 = ai_gl2_coefficients(30)
  assert_true(gl2[3] == 0.0)
  assert_true(gl2[7] == 0.0)
  assert_true(gl2[11] == 0.0)
  assert_true(gl2[9] != 0.0) // 3² even power: χ((3)) = ψ(4) = −1
  assert_true(gl2[5] == 0.0) // 5 在導子上：χ = 0
}

///|
test "T38a deuring mass" {
  for p in [5, 7, 11] {
    let (_, mass, _) = ss_j_invariants_gf2(p)
    let want = (p - 1).to_double() / 24.0
    let diff = mass - want
    let abs = if diff < 0.0 { -diff } else { diff }
    assert_true(abs < 0.000001)
  }
}

///|
test "T38b deuring count" {
  assert_eq(deuring_j_count(5), 1) // ⌊5/12⌋+1
  assert_eq(deuring_j_count(7), 1)
  assert_eq(deuring_j_count(11), 2) // ⌊11/12⌋+2
  assert_eq(deuring_j_count(13), 1) // ⌊13/12⌋+0
  for p in [5, 7, 11] {
    let (count, _, _) = ss_j_invariants_gf2(p)
    assert_eq(count, deuring_j_count(p))
  }
}

///|
test "T39a jacobi triple product" {
  assert_true(jacobi_triple_product_error(0.2, 0.7, 12) < 0.000001)
  assert_true(jacobi_triple_product_error(0.05, 1.8, 12) < 0.000001)
}

///|
test "T39b theta counting and L" {
  assert_eq(theta_r2_error(50), 0)
  assert_true(theta_l_function_error(150, 6.0) < 0.001)
}

///|
test "T40a modularity primes" {
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23] {
    let (match_, _, _) = modularity_check_prime(p)
    assert_true(match_)
  }
}

///|
test "T40b hasse and hecke" {
  assert_true(hasse_violation(47) <= 0.000001)
  assert_eq(modularity_hecke_violations(20), 0)
  let (ok, _) = level11_known_prime_check()
  assert_true(ok)
}

///|
test "A4 evolution finds newform" {
  let (fit, best, _) = evolve_modularity(12, 400)
  assert_eq(fit, 0)
  let truth = newform_level11(12)
  let mut n = 1
  while n <= 12 {
    assert_eq(best[n], truth[n])
    n = n + 1
  }
}

///|
test "A5 evolution finds frobenius matrix" {
  let e = x011_curve()
  let a11 = e.trace(11)
  let (fit, m, _) = evolve_frobenius_matrix(a11, 11, 5, 120)
  assert_eq(fit, 0)
  assert_eq(m.trace_mod(5), (a11 % 5 + 5) % 5)
  assert_eq(m.det_mod(5), 1) // p = 11 ≡ 1 mod 5
}

///|
test "A6 evolution recovers sym2 satake" {
  let a = delta_series(20)
  let s = satake_power_sums(a.coeff(2), 2, 12, 8)
  let targets : Array[Int64] = []
  let pk = 2048L
  let mut pm = 1L
  let mut m = 1
  while m <= 3 {
    pm = pm * pk
    targets.push(s[2 * m] + pm)
    m = m + 1
  }
  let (fit, e1, e2, e3, _) = evolve_sym2_data(targets, 400)
  assert_eq(fit, 0)
  assert_eq(e1, a.coeff(2) * a.coeff(2) - 2048)
  assert_eq(e2, 2048L * e1)
  assert_eq(e3, 2048L * 2048L * 2048L)
}

///|
test "T37c ai L = product of dirichlet L" {
  assert_true(ai_three_way_error(60, 8.0) < 0.000001)
}
