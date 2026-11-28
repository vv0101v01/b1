///|
/// batch11_wbtest.mbt — 批次十一白盒測試（拓撲斯幾何 / 句法遺址 / 導出範疇 / 非交換）。
///
/// 全部數值由模組函式重新計算，與 report11 的報告數字交叉核對。

///|
/// 模組一：豪斯多夫與緊拓撲斯。
test "batch11_m1_hausdorff" {
  let sp = b10r_spaces()
  // 僅離散 2 點豪斯多夫；兩條路線（點分離／對角閉）必須一致
  let (sep0, diag0) = b11_hausdorff(sp[0].1)
  let (sep1, diag1) = b11_hausdorff(sp[1].1)
  assert_false(sep0)
  assert_false(diag0)
  assert_true(sep1)
  assert_true(diag1)
  for (_, t) in sp {
    let (a, b) = b11_hausdorff(t)
    assert_eq(a, b)
    assert_true(b11_compact(t).0)
  }
  assert_eq(b11_closed_pts(sp[0].1), 1)
  assert_eq(b11_closed_pts(sp[1].1), 2)
  let (covers, worst, _) = b11_cover_stats(sp[2].1)
  assert_eq(covers, 80)
  assert_eq(worst, 2)
}

///|
/// 模組二：幾何態射族、依賴乘積、六運算。
test "batch11_m2_geometric" {
  let c2 = b8_cat_disc(2)
  let c3 = b8_cat_disc(3)
  let u_id = b8_fun(c2, c2, [0, 1], [0, 1])
  let u_surj = b8_fun(c3, c2, [0, 1, 1], [0, 1, 1])
  let u_inj = b8_fun(c2, c3, [0, 1], [0, 1])
  let f2 = b11_ps_family(c2, [1, 2])
  let g2 = b11_ps_family(c2, [2, 2])
  let f3 = b11_ps_family(c3, [1, 2, 1])
  let g3 = b11_ps_family(c3, [2, 2, 2])
  // 依賴乘積
  assert_true(b11_dep_prod_ok(u_id, f2, g2))
  assert_true(b11_dep_prod_ok(u_surj, f3, g2))
  assert_true(b11_dep_prod_ok(u_inj, f2, g3))
  assert_true(b11_pull_ran_ok(u_surj, f3, g2))
  // 六運算
  let (a1, a2) = b11_six_ok(u_surj, f3, g2)
  assert_true(a1 && a2)
  // 帶緊支撐直像 vs 直像
  assert_eq(b11_sum_prod(u_surj, 3), (9, 12))
  assert_true(b11_proper(u_id))
  assert_true(b11_proper(u_inj))
  assert_false(b11_proper(u_surj))
  // 連通 / 平展 / 局部
  assert_true(b11_connected(u_id, [f2], [g2]))
  assert_false(b11_connected(u_surj, [f2], [g2]))
  assert_true(b11_etale(u_surj, f3, g2))
  assert_true(b11_local_ok(u_id, f2, g2))
  assert_false(b11_local_ok(u_surj, f3, g2))
  assert_false(b11_local_ok(u_inj, f2, g3))
}

///|
/// 模組三：導出範疇、單純形層、反常層、ℓ-進層。
test "batch11_m3_derived" {
  let sp = b10r_spaces()
  let expect : Array[Array[Int32]] = [
    [1, 0, 0],
    [2, 0, 0],
    [1, 1, 0],
    [2, 0, 0],
  ]
  for i in 0..<sp.length() {
    let st = b9_site(sp[i].1)
    let cv = b10r_maxcover(st)
    assert_eq(b11_ext_dims(cv, 2, 5), expect[i])
    // 有序（含退化）Čech 與交替複形一致
    assert_eq(b11_ordered_cech_h(cv, 0, 5), expect[i][0])
    assert_eq(b11_ordered_cech_h(cv, 1, 5), expect[i][1])
    assert_true(b11_degeneracy_ok(cv))
    // Ext^0 = 連通分量數
    let (e0, comps) = b11_ext0_check(cv, 5)
    assert_eq(e0, comps)
    // ℓ 無關性
    assert_true(b11_ell_betti(cv, 2, 5, 7).2)
    // cdh Mayer–Vietoris（閉點集 + 全集 的閉覆蓋）
    let z : Array[Bool] = []
    let zall : Array[Bool] = []
    for p in 0..<sp[i].1.npt {
      let comp : Array[Bool] = []
      for q in 0..<sp[i].1.npt {
        comp.push(q != p)
      }
      z.push(b9_top_find(sp[i].1, comp) >= 0)
      zall.push(true)
    }
    assert_true(b11_cdh_mv(sp[i].1, z, zall, 2, 5).2)
    let (hx, per) = b11_perverse_dims(st, cv, z, 2, 5)
    assert_eq(hx, expect[i])
    assert_eq(per.length(), 3)
    assert_eq(
      b11_inf_adjunction(
        b8_fun(b8_cat_disc(3), b8_cat_disc(2), [0, 1, 1], [0, 1, 1]),
        [b8_ps_const(b8_cat_disc(3), 2)],
        [b8_ps_const(b8_cat_disc(2), 2)],
      ),
      true,
    )
  }
  assert_eq(b11_connected_components(sp[1].1), 2)
  assert_eq(b11_connected_components(sp[2].1), 1)
}

///|
/// 模組四：句法遺址、泛模型、橋樑、相干函子。
test "batch11_m4_syntactic" {
  let z2 = b9_group_zn(2)
  let v4 = b9_group_v4()
  let s3 = b9_group_s3()
  assert_eq(b11_transitive_degrees(z2), [1, 1])
  assert_eq(b11_transitive_degrees(v4), [1, 3, 0, 1])
  assert_eq(b11_transitive_degrees(s3), [1, 1, 1, 0, 0, 1])
  assert_eq(b11_fp_gsets(z2, 3), 6)
  assert_eq(b11_fp_gsets(v4, 3), 10)
  for g in [z2, b9_group_zn(3), v4, s3] {
    assert_true(b11_generic_model(g, [b9_gset_reg(g), b9_gset_triv(g, 3)]))
    assert_eq(b11_sub_terminal(g), 2)
    assert_eq(b11_aut_regular(g), g.k)
    let (grp, syn, eq) = b11_bridge(g, 5)
    assert_true(eq)
    assert_eq(grp, syn)
  }
  let c2 = b8_cat_disc(2)
  let c3 = b8_cat_disc(3)
  let u = b8_fun(c3, c2, [0, 1, 1], [0, 1, 1])
  let (c1, c2b, c3b) = b11_coherent(u, b8_ps_const(c2, 2), b8_ps_const(c2, 3))
  assert_true(c1 && c2b && c3b)
}

///|
/// 模組五：主 G-叢、微分凝聚、非交換拓撲斯。
test "batch11_m5_bundles" {
  let sp = b10r_spaces()
  let mut trivial_cnt = 0
  for (_, t) in sp {
    let st = b9_site(t)
    let cv = b10r_maxcover(st)
    let h1 = b9_cech_h(cv, 1, 5)
    assert_eq(b11_bundle_classes(cv, 5), b8_pow_int(5, h1))
    if b11_bundle_trivial(cv, 5) {
      trivial_cnt = trivial_cnt + 1
    }
    // 凝聚：Γ = 終對象截面；Disc ⊣ Γ 成立
    let (_, ga, _, adj2) = b11_cohesion(st, b8_ps_const(st.cat, 2))
    assert_eq(ga, 2)
    assert_true(adj2)
  }
  assert_eq(trivial_cnt, 3)
  // 無窮小形狀
  assert_eq(b11_inf_shape(sp[1].1), (2, 2))
  assert_eq(b11_inf_shape(sp[0].1).0, 1)
  assert_eq(b11_inf_shape(sp[2].1).0, 1)
  // 非交換拓撲斯：點 1 而 π₁ = |G|
  for g in [b9_group_zn(2), b9_group_zn(3), b9_group_v4(), b9_group_s3()] {
    let (pts, pi1, _) = b11_nc_invariants(g, 5)
    assert_eq(pts, 1)
    assert_eq(pi1, g.k)
  }
}
