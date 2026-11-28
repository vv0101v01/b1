///|
/// batch10_wbtest.mbt — 批次十白盒測試（勒雷譜序列 / ∞-遺址 / 基本群 / 基變 / 局部化）。
///
/// 全部數值皆由模組函式重新計算，與 report10 的報告數字交叉核對。

///|
/// 模組一：高階直像的維數表與歐拉–龐加萊。
test "batch10_m1_direct_image" {
  let expect : Array[(String, Array[Int32], Int32)] = [
    ("Sierpiński", [1, 0, 0], 5),
    ("離散2點", [2, 0, 0], 25),
    ("圓S¹(4點)", [1, 1, 0], 5),
    ("3點特殊化", [2, 0, 0], 25),
  ]
  let tops = b10r_spaces()
  for i in 0..<tops.length() {
    let st = b9_site(tops[i].1)
    let cv = b10r_maxcover(st)
    let rq = b10_higher_direct_dims(cv, 2, 5)
    assert_eq(rq, expect[i].1)
    assert_eq(b10_direct_image_pt(cv, 5).sz[0], expect[i].2)
    assert_eq(b10_sections_dim(st, cv.v, 5), expect[i].2)
    let (l, r) = b10_euler_poincare(cv, 2, 5)
    assert_eq(l, r)
  }
}

///|
/// 模組一：Künneth／勒雷 E₂ 退化。
test "batch10_m1_kunneth" {
  let tops = b10r_spaces()
  let sc = b9_site(tops[2].1)
  let sd = b9_site(tops[1].1)
  let ss = b9_site(tops[0].1)
  let cvc = b10r_maxcover(sc)
  let cvd = b10r_maxcover(sd)
  let cvs = b10r_maxcover(ss)
  assert_eq(b10_kunneth(cvc, cvd, 2, 2, 5).1, [2, 2, 0, 0, 0])
  assert_eq(b10_kunneth(cvc, cvc, 2, 2, 5).1, [1, 2, 1, 0, 0])
  assert_eq(b10_kunneth(cvc, cvs, 2, 2, 5).1, [1, 1, 0, 0, 0])
  assert_true(b10_kunneth_ok(cvc, cvd, 2, 2, 5))
  assert_true(b10_kunneth_ok(cvc, cvc, 2, 2, 5))
  assert_true(b10_kunneth_ok(cvc, cvs, 2, 2, 5))
}

///|
/// 模組二：∞-遺址與高階吉羅公理。
test "batch10_m2_inf_site" {
  let mut strict_true = 0
  for (_, t) in b10r_spaces() {
    let st = b9_site(t)
    let cv = b10r_maxcover(st)
    assert_true(b10_simplicial_ok(cv))
    assert_true(b10_hypercover_degenerate_ok(cv))
    assert_true(b10_nerve_cohomology_ok(cv, 2, 5))
    assert_true(@b10.b10_inf_site_ok(st, cv, 2, 5))
    assert_true(b10_giraud_g3(cv))
    let (a, b, c) = b10_giraud_low(st)
    assert_true(a && b && c)
    if b10_hypercover_ok(st, cv) {
      strict_true = strict_true + 1
    }
  }
  // 嚴格版本僅在「不交覆蓋」時成立 ⇒ 至少 3 個負見證
  assert_true(strict_true <= 1)
}

///|
/// 模組三：局部常數層、基本群、局部群oid、等變層。
test "batch10_m3_fundamental_group" {
  let tops = b10r_spaces()
  let sd = b9_site(tops[1].1)
  let ss = b9_site(tops[0].1)
  assert_true(b10_is_locally_constant(sd, b8_ps_const(sd.cat, 2)))
  assert_true(b10_is_locally_constant(sd, b8_ps_yoneda(sd.cat, sd.cat.nob - 1)))
  assert_false(b10_is_locally_constant(ss, b10r_collapse(ss, 2)))
  let z2 = b9_group_zn(2)
  let z3 = b9_group_zn(3)
  let v4 = b9_group_v4()
  let s3 = b9_group_s3()
  assert_eq(b10_fiber_aut(z2), 2)
  assert_eq(b10_fiber_aut(z3), 3)
  assert_eq(b10_fiber_aut(v4), 4)
  assert_eq(b10_fiber_aut(s3), 6)
  assert_eq(b10_subgroup_index_count(z2, 2), 1)
  assert_eq(b10_subgroup_index_count(z3, 3), 1)
  assert_eq(b10_subgroup_index_count(z3, 2), 0)
  assert_eq(b10_subgroup_index_count(v4, 2), 3)
  assert_eq(b10_subgroup_index_count(s3, 3), 3)
  assert_eq(b10_conj_class_count(s3, 2), 1)
  assert_eq(b10_conj_class_count(s3, 3), 1)
  assert_eq(b10_subgroup_index_count(s3, 3), 3)
  assert_eq(b10_subgroup_total(z2), 2)
  assert_eq(b10_subgroup_total(v4), 5)
  assert_eq(b10_subgroup_total(s3), 6)
  let reg = b9_gset_reg(z2)
  assert_eq(b10_groupoid_sizes(reg), (2, 4))
  assert_true(b10_groupoid_invertible(reg))
  assert_true(b10_regular_power_ok(z2, 0))
  assert_true(b10_regular_power_ok(z2, 2))
  assert_eq(b10_equivariant_classes(z2, 2), 3)
}

///|
/// 模組四：弗羅貝尼烏斯／基變／滿射／有界。
test "batch10_m4_geometric" {
  let s2 = b9_site(b10r_spaces()[1].1)
  let s3 = b9_site(
    b9_top(3, [
      [false, false, false],
      [true, false, false],
      [false, true, false],
      [false, false, true],
      [true, true, false],
      [true, false, true],
      [false, true, true],
      [true, true, true],
    ]),
  )
  let u = b9_open_fun([0, 1, 1], s2, s3)
  assert_true(b10_frobenius(u, b8_ps_const(s3.cat, 2), b8_ps_const(s2.cat, 3)))
  assert_true(
    b10_frobenius(
      u,
      b8_ps_const(s3.cat, 2),
      b8_ps_yoneda(s2.cat, s2.cat.nob - 1),
    ),
  )
  let uf = b9_open_fun([0, 1], s2, s2)
  let ufp = b9_open_fun([0, 1, 2], s3, s3)
  assert_true(b10_beck_chevalley(uf, u, u, ufp, b8_ps_const(s2.cat, 2)))
  assert_true(
    b10_beck_chevalley(uf, u, u, ufp, b8_ps_yoneda(s2.cat, s2.cat.nob - 1)),
  )
  assert_true(b10_surjective_pts([0, 1, 1], 2))
  assert_false(b10_surjective_pts([0, 0, 0], 2))
  assert_true(
    b10_fully_faithful_star(u, [b8_ps_const(s2.cat, 2)], [
      b8_ps_yoneda(s2.cat, 1),
    ]),
  )
  assert_true(
    b10_direct_preserves_coprod(
      u,
      b8_ps_const(s3.cat, 2),
      b8_ps_yoneda(s3.cat, s3.cat.nob - 1),
    ),
  )
  let (b, ok) = b10_bounded_ok(s3)
  assert_true(ok)
  assert_true(b > 0)
}

///|
/// 模組五：局部化／原子／格里森／空間／索引。
test "batch10_m5_localization" {
  let tops = b10r_spaces()
  let mut atomic_cnt = 0
  for (_, t) in tops {
    let st = b9_site(t)
    let top = st.cat.nob - 1
    let y = b8_ps_yoneda(st.cat, top)
    let (a, c) = b10_open_localization(st, top)
    assert_eq(a, c)
    assert_eq(b10_sub_terminal_sh(st), t.opens.length())
    assert_eq(b10_slice_sub_terminal(y), a)
    assert_true(b10_spatial(st))
    if b10_atomic(st) {
      atomic_cnt = atomic_cnt + 1
    }
  }
  // 僅離散空間原子
  assert_eq(atomic_cnt, 1)
  let sier = tops[0].1
  let circ = tops[2].1
  assert_eq(b10_regular_open_count(sier), 2)
  assert_eq(b10_regular_open_count(circ), 4)
  assert_eq(b10_gleason_atoms(sier), 1)
  assert_eq(b10_gleason_atoms(circ), 2)
  assert_true(b10_gleason_boolean(sier))
  assert_false(b10_gleason_boolean(circ))
  let z2 = b9_group_zn(2)
  assert_true(
    b10_spatial_gset(z2, [
      b9_gset_reg(z2),
      b9_gset_regular2(z2),
      b9_gset_triv(z2, 3),
    ]),
  )
  assert_eq(
    b10_indexed_total([
      b9_site(tops[0].1),
      b9_site(tops[1].1),
      b9_site(tops[2].1),
    ]),
    11,
  )
}
