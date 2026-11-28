///|
/// batch8_wbtest.mbt — 批次八白盒測試（T240–T293）
test "point functor checks over seven categories" {
  let cats = [
    b8_cat_arrow(),
    b8_cat_par(),
    b8_cat_iso(),
    b8_cat_z2(),
    b8_cat_span(),
    b8_cat_square(),
    b8_cat_disc(3),
  ]
  for c in cats {
    assert_true(b8_cat_ok(c))
    let (y, p, co, l, r) = b8_point_functor_checks(c, 7L)
    assert_true(y)
    assert_true(p)
    assert_true(co)
    assert_true(l)
    assert_true(r)
    assert_true(b8_yoneda_full_faithful(c))
  }
}

///|
test "pullback functors along composition" {
  let arr = b8_cat_arrow()
  let sq = b8_cat_square()
  let z2 = b8_cat_z2()
  let f = b8_fun(arr, sq, [0, 1], [0, 4, 1])
  let g = b8_fun(sq, z2, [0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 1, 0])
  assert_true(@b8.b8_fun_ok(f))
  assert_true(@b8.b8_fun_ok(g))
  let x = b8_ps_rand(sq, 5L)
  assert_true(b8_pull_comp_check(f, g, x))
  let xa = b8_ps_rand(arr, 3L)
  assert_true(b8_ps_eq(b8_lan(b8_fun_id(sq), x), x))
  assert_true(b8_lan_adj_ok(f, xa, b8_ps_yoneda(sq, 1)))
  assert_true(b8_lan_adj_ok(f, xa, b8_ps_const(sq, 2)))
  let (l, r) = b8_lan_comp_sz(f, g, xa)
  assert_true(b_sh_arr_eq(l, r))
}

///|
test "colimits and sheafification" {
  assert_eq(b8q_coeq_size(3, [0, 1, 2], [0, 1, 2]), 3)
  assert_eq(b8q_coeq_size(3, [0, 1, 2], [1, 2, 0]), 1)
  let (n1, s1) = b8q_chain_colim([3, 3, 3], [[0, 1, 2], [0, 1, 2]])
  assert_eq(n1, 3)
  assert_eq(s1, 0)
  let pcat = b8_cat_build(
    4,
    9,
    [0, 1, 2, 3, 0, 0, 0, 1, 2],
    [0, 1, 2, 3, 1, 2, 3, 3, 3],
    [0, 1, 2, 3],
    [(7, 4, 6), (8, 5, 6)],
  )
  let site = b8_site(pcat, [[0], [4, 1], [5, 2], [6, 7, 8]])
  assert_true(b8_site_ok(site))
  let f = b8_ps_zero(pcat, [1, 2, 2, 0])
  let (stages, stab) = b8_plus_stages(site, f)
  assert_eq(stages[0], 5)
  assert_eq(stages[1], 9)
  assert_eq(stab, 1)
  let a = b8_sheafify(site, f)
  assert_eq(a.sz[3], 4)
  assert_true(b8_is_sheaf(site, a))
  let f2 = b8_ps_zero(pcat, [2, 3, 3, 0])
  let f3 = b8_ps_zero(pcat, [1, 1, 1, 0])
  let afg = b8_sheafify(site, b8_ps_coprod(f2, f3))
  assert_eq(
    afg.sz[3],
    b8_sheafify(site, f2).sz[3] + b8_sheafify(site, f3).sz[3],
  )
}

///|
test "universes and cardinals" {
  let lv = b8u_level_sizes(6)
  assert_eq(lv[4], 16)
  assert_eq(lv[5], 65536)
  assert_true(b8u_beth(4).to_string() == "65536")
  assert_eq(b8u_level_size_big(6).to_string().length(), 19729)
  let reg = b8reg_new()
  let uni = b8u_universe_levels(reg, 5)
  assert_true(uni[0])
  assert_false(uni[1])
  assert_eq(b8u_reachable_count(1000), 1000)
  assert_eq(b8u_regular_count(1000), 1000)
  assert_eq(b8u_pow_failures(reg, 2), 1)
}

///|
test "categorified invariants" {
  let (a1, a2) = b8w_core_card(b8_cat_arrow())
  assert_eq(a1, 2L)
  assert_eq(a2, 1L)
  let (i1, i2) = b8w_core_card(b8_cat_iso())
  assert_eq(i1, 1L)
  assert_eq(i2, 1L)
  let (z1, z2) = b8w_core_card(b8_cat_z2())
  assert_eq(z1, 1L)
  assert_eq(z2, 2L)
  assert_true(b_sh_arr_eq(b8w_betti(b8w_sphere(2)), [1, 0, 1]))
  assert_true(b_sh_arr_eq(b8w_betti(b8w_sphere(3)), [1, 0, 0, 1]))
  assert_eq(b8w_euler_complex(b8w_sphere(3)), b8w_euler_betti(b8w_sphere(3)))
  assert_true(b8w_nerve_count(b8_cat_square(), 3).to_string() == "25")
}

///|
test "well-founded and anti-founded structures" {
  let reg = b8reg_new()
  let edges : Array[Array[Int32]] = [[1, 2], [3], [3], []]
  let ids = b8reg_mostowski(reg, edges)
  assert_false(b8reg_collapse_injective(ids))
  assert_false(b8reg_extensional(edges))
  let cyc : Array[Array[Int32]] = [[1], [0]]
  assert_eq(b8reg_mostowski(reg, cyc).length(), 0)
  let self : Array[Array[Int32]] = [[0]]
  let v3 = b8reg_level(reg, 3)
  assert_eq(b8wf_solution_count(reg, self, v3), 0)
  assert_eq(b8afa_decor_classes(self), 1)
  let acyc : Array[Array[Int32]] = [[1], []]
  assert_eq(b8wf_solution_count(reg, acyc, v3), 1)
}

///|
test "morita equivalence of matrix algebras" {
  assert_eq(b8mm_units_bruteforce(2, 2), 6)
  assert_eq(b8mm_units_formula(2, 3), 48)
  assert_eq(b8mm_idempotents(2, 2), 8)
  assert_eq(b8mm_idempotents_rank(2, 2, 1), 6)
  assert_eq(b8mm_count_ideals(2, 2), 2)
  assert_true(b8mm_transpose_anti(2, 2))
  assert_true(b8mm_unit_rule(2))
  let (d1, d2) = b8mm_tensor_dim(2, 2)
  assert_eq(d1, d2)
  assert_eq(b8mm_corner_size(b8mm_unit(2, 0, 0), 2, 2), 2)
}

///|
test "synthetic higher category theory" {
  for
    c in [
      b8_cat_arrow(),
      b8_cat_square(),
      b8_cat_z2(),
      b8_cat_span(),
      b8_cat_par(),
    ] {
    let ss = b8ss_nerve(c)
    assert_true(b8ss_identities(ss))
    assert_true(b8ss_is_quasicat(ss))
  }
  let (ok, hn, hf) = b8ss_inner_horn(b8ss_nerve(b8_cat_arrow()), 2, 1)
  assert_true(ok)
  assert_eq(hn, hf)
  let (tot, quasi) = b8ss_count_quasi_subsets()
  assert_eq(tot, 19)
  assert_eq(quasi, 1)
  assert_true(b8ss_is_kan2(b8ss_nerve(b8_cat_z2())))
}

///|
test "information functionals" {
  let p : Array[Array[Double]] = [[0.4, 0.1], [0.1, 0.4]]
  assert_true((b8i_h([0.5, 0.5]) - 1.0).abs() < 1.0e-12)
  assert_true((b8i_tc2(p) - b8i_mi(p)).abs() < 1.0e-12)
  let xor : Array[Array[Array[Double]]] = [
    [[0.25, 0.0], [0.0, 0.25]],
    [[0.0, 0.25], [0.25, 0.0]],
  ]
  let ten = b8i_tensor3(xor)
  assert_true((ten[7] + 1.0).abs() < 1.0e-12)
  let (tot, zero, prod, mism) = b8i_independence_scan()
  assert_eq(tot, 969)
  assert_eq(zero, prod)
  assert_eq(mism, 0)
  let (ixt, ity, res, _) = b8i_ib(p, 2, 100.0, 800)
  assert_true((ixt - 1.0).abs() < 1.0e-6)
  assert_true((ity - 0.2780719051126379).abs() < 1.0e-6)
  assert_true(res < 1.0e-12)
}
