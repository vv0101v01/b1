///|
/// theorem_wbtest.mbt — 關鍵定理恆等式的白箱測試（moon test 執行）

///|
test "T1 乘積公式 Q" {
  for r in [Rat(6L, 35L), Rat(-12L, 77L), Rat(1L, 2L), Rat(2310L, 1L)] {
    let prod = product_formula_rat(r)
    assert_true(prod.0 == 1L && prod.1 == 1L, msg="product formula must be 1")
  }
}

///|
test "T1b 乘積公式 二次域" {
  let x = QuadElem(-5L, Rat(2L, 1L), Rat(1L, 1L))
  let prod = product_formula_quad(x)
  assert_true(prod.0 == 1L && prod.1 == 1L, msg="quadratic product formula")
}

///|
test "T1c 函數域乘積公式" {
  let f = ff2_mul(ff2_mul(2, 3), 7)
  let g = ff2_mul(11, 3)
  assert_true(ff2_product_formula(f, g) == 0, msg="ff2 product formula")
  assert_true(ff2_product_formula(19, 13) == 0, msg="ff2 product formula 2")
}

///|
test "T3 Hensel 平方根" {
  for (p, a) in [(5L, 4L), (7L, 2L), (11L, 5L)] {
    let adic = PAdic::from_int(a, p, 12)
    let root = hensel_sqrt(adic)
    let sq = root.mul(root)
    let diff = sq.sub(adic)
    assert_true(diff.is_zero(), msg="hensel sqrt")
  }
}

///|
test "T8 類數" {
  assert_true(class_number_forms(-4) == 1, msg="h(-4)")
  assert_true(class_number_forms(-20) == 2, msg="h(-20)")
  assert_true(class_number_forms(-23) == 3, msg="h(-23)")
  assert_true(class_number_forms(-163) == 1, msg="h(-163)")
}

///|
test "T9 Hilbert 類多項式類域" {
  let disc = 1264000L * 1264000L + 4L * 681472000L
  assert_true(disc % 5L == 0L, msg="disc divisible by 5")
  assert_true(is_square64(disc / 5L), msg="class field Q(sqrt 5)")
}

///|
test "T10 j-不變量參數化" {
  for p in [5, 7, 11] {
    assert_true(count_j_invariants(p) == p, msg="j count = p")
  }
}

///|
test "T11 旗簇軌道穩定子" {
  for (n, q) in [(2, 2), (2, 3), (3, 2)] {
    let gl = count_gl_bruteforce(n, q)
    let b = count_b_bruteforce(n, q)
    assert_true(gl == b * flag_variety_order(n, q), msg="|GL|=|B||Fl|")
  }
}

///|
test "T12 Gaussian 二項式" {
  assert_true(gaussian_binom(4, 2, 2) == 35, msg="[4 2]_2 = 35")
  assert_true(count_subspaces(4, 2, 2) == 35, msg="enumeration")
  assert_true(gaussian_binom(4, 2, 3) == 130, msg="[4 2]_3 = 130")
  assert_true(count_subspaces(4, 2, 3) == 130, msg="enumeration q=3")
}

///|
test "T13 仿射格拉斯曼 σ₁" {
  for (p, m) in [(2, 3), (3, 3)] {
    assert_true(sublattice_count(p, m) == sigma1_pm(p, m), msg="sigma1")
    assert_true(schubert_poincare_sl2(m, p) == sigma1_pm(p, m), msg="poincare")
  }
  assert_true(two_rho_pairing([4, 0], 2) == 4, msg="dim Gr^(m) = m")
}

///|
test "T16 自同構計數" {
  let e = SplitBundle(3, 1)
  assert_true(aut_order(e, 3) == aut_order_bruteforce(e, 3), msg="aut count")
  let f = SplitBundle(2, 2)
  assert_true(aut_order(f, 3) == gl_order(2, 3), msg="semistable aut = GL2")
}

///|
test "T17 質量公式" {
  let m1 = bun_mass_truncated(4, 10, 3)
  let m2 = bun_mass_closed(4, 10, 3)
  let diff = if m1 > m2 { m1 - m2 } else { m2 - m1 }
  assert_true(diff < 0.0000001, msg="mass closed form")
}

///|
test "T18 E4³ − E6² = 1728Δ" {
  let n0 = 22
  let e4 = e4_series(n0)
  let e6 = e6_series(n0)
  let d = delta_series(n0)
  let lhs = e4.mul(e4.mul(e4)).sub(e6.mul(e6))
  let rhs = d.scale(1728L)
  assert_true(lhs.equals_upto(rhs, n0), msg="modular discriminant identity")
}

///|
test "T19 Hecke 特徵形式" {
  let n0 = 33
  let d = delta_series(n0)
  let t2 = hecke_operator(d.0, 2, 12)
  let tau2 = d.coeff(2)
  assert_true(tau2 == -24L, msg="tau(2) = -24")
  let mut n = 1
  while n <= n0 / 2 {
    assert_true(t2[n] == tau2 * d.coeff(n), msg="T2 eigen")
    n = n + 1
  }
}

///|
test "T21 乘性 τ(6) = τ(2)τ(3)" {
  let d = delta_series(40)
  assert_true(d.coeff(6) == d.coeff(2) * d.coeff(3), msg="tau multiplicative")
  assert_true(d.coeff(12) == d.coeff(4) * d.coeff(3), msg="tau(12)")
}

///|
test "T22 Satake |α| = p^5.5" {
  let d = delta_series(50)
  for p in [2, 3, 5, 7] {
    let ap = d.coeff(p).to_double()
    assert_true(ramanujan_ok(ap, p, 12), msg="ramanujan bound")
    let (al, be) = satake_params(ap, p, 12)
    let target = @math.pow(p.to_double(), 5.5)
    let diff = al.abs() - target
    assert_true(diff.abs() < 0.001, msg="satake abs")
    let prod = al.mul(be)
    assert_true(
      (prod.0 - target * target).abs() < 0.01,
      msg="alpha beta = p^11",
    )
  }
}

///|
test "T23 Euler 乘積" {
  let d = delta_series(50)
  let dir = dirichlet_partial(d.0, 45, 12.0)
  let eul = euler_partial(d.0, 43, 12.0, 12)
  let rel = (dir - eul).abs() / dir
  assert_true(rel < 0.0001, msg="euler product")
}

///|
test "T24 Hecke 代數 T_p² = T_{p²} + p^{k−1}" {
  let d = delta_series(30)
  assert_true(hecke_structure_error(d.0, 2, 12, 12) == 0L, msg="hecke algebra")
  assert_true(hecke_commutativity_error(d.0, 2, 3, 12, 12) == 0L, msg="commute")
}

///|
test "T25 Hitchin 維度" {
  for n in [2, 3, 4] {
    for g in [2, 3] {
      assert_true(
        hitchin_base_dim(n, g) == hitchin_base_dim_closed(n, g),
        msg="base dim",
      )
      assert_true(
        spectral_genus(n, g) == hitchin_base_dim_closed(n, g),
        msg="genus",
      )
    }
  }
}

///|
test "T27/T28 譜曲線 Weil" {
  let curve = HypCurve([3, 1, 0, 0, 0, 1])
  let g = curve.genus()
  assert_true(g == 2, msg="genus 2")
  let e = hyp_l_polynomial(curve, 7, g)
  assert_true(hyp_functional_equation_ok(e, 7, g), msg="functional equation")
  assert_true((e[4] - 49.0).abs() < 0.0001, msg="e4 = q^g")
  let cnt = curve.point_count(7, 1)
  assert_true(hyp_hasse_ok(cnt, 7, g), msg="hasse-weil")
  let curve2 = HypCurve([1, 1, 0, 1])
  let e2 = hyp_l_polynomial(curve2, 7, 1)
  assert_true(
    hyp_jacobian_order(e2) == curve2.point_count(7, 1).to_int64(),
    msg="P(1)=#C",
  )
}

///|
test "A1 Hecke 特徵形式演化" {
  let (lam, res, _) = hecke_eigenform_evolution(42L, 200)
  assert_true(res < 0.000001, msg="power method residual")
  assert_true(lam.abs() > 1.0, msg="eigenvalue")
}

///|
test "A2 Hitchin 譜曲線演化" {
  let hist = hitchin_spectral_curve_ga(7, 20, 15, 2024L)
  let mut i = 1
  while i < hist.length() {
    assert_true(hist[i] >= hist[i - 1], msg="elitism monotone")
    i = i + 1
  }
}

///|
test "A3 二次型約化演化" {
  let (s1, f1) = form_reduction_evolution(3, 2, 2, 100)
  assert_true(s1 < 100, msg="converges")
  assert_true(f1 <= 10, msg="fitness small")
}
