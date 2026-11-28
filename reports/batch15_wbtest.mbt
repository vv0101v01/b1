///|
/// batch15_wbtest.mbt — 批次十五白盒測試（補洞：歸納法 × 反證法）。
///
/// 數值全部來自 `report15` 的實跑輸出；報告零 [FAIL] 的前提是本檔零 test 失敗。
test "b15-terminal-generator" {
  // n 重餘積的普遍性 + {1} 分離
  let (univ, sep, n) = @b15.b15_terminal_generator_check(5, 4)
  inspect(univ, content="true")
  inspect(sep, content="true")
  inspect(n, content="1818")
}

///|
test "b15-chain-groupoid" {
  let (o1, c1) = @b15.b15_chain_groupoid_check(1)
  let (o2, c2) = @b15.b15_chain_groupoid_check(2)
  let (o3, c3) = @b15.b15_chain_groupoid_check(3)
  let (o4, c4) = @b15.b15_chain_groupoid_check(4)
  inspect(o1, content="true")
  inspect(o2, content="true")
  inspect(o3, content="true")
  inspect(o4, content="true")
  inspect(c1, content="2")
  inspect(c2, content="14")
  inspect(c3, content="96")
  inspect(c4, content="656")
}

///|
test "b15-nerve-degrees" {
  let (a, b, c, n) = @b15.b15_nerve_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="10")
  // 三重交集真的出現在 3 成員覆蓋上
  let ch = @b14.b14_cech(@b14.b14_m_circle(), [12, 13, 14], 1)
  inspect(ch.n, content="3")
}

///|
test "b15-perverse-true" {
  let (a, b, c, n) = @b15.b15_perverse_true_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="162")
  let (shadow, real) = @b15.b15_shadow_gap()
  inspect(shadow, content="4")
  inspect(real, content="2")
}

///|
test "b15-intermediate-formula" {
  let (ok, counts) = @b15.b15_intermediate_induction(5)
  inspect(ok, content="true")
  inspect(@common.b_sh_arr_i32(counts), content="[3, 9, 27, 81, 243]")
  inspect(@b15.b15_intermediate_formula(5), content="true")
}

///|
test "b15-milnor-all-n" {
  let (a, b, c, n) = @b15.b15_milnor_all_n_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="16")
  // K^M_1(F₅) = ℤ/4，K^M_2(F₅) = 0
  inspect(@b15.b15_km_n(5, 1).0, content="4")
  inspect(@b15.b15_km_n(5, 2).0, content="1")
  inspect(@b15.b15_primitive_root(7), content="3")
}

///|
test "b15-k0" {
  let (free, b, c, inv) = @b15.b15_k0_check()
  inspect(free, content="1")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(@common.b_sh_arr_i32(inv), content="[1, 1, 1, 1, 1]")
}

///|
test "b15-pi2" {
  let (q1, q2, q3, q4, q5) = @b15.b15_pointed2_check()
  inspect(q1, content="true")
  inspect(q2, content="true")
  inspect(q3, content="true")
  inspect(q4, content="true")
  inspect(q5, content="true")
  // RP² 的 H₂ = 0 但非 1-連通
  let d2 : Array[Array[Int32]] = [[2]]
  let (simply, _, h2) = @b15.b15_pi2(1, 1, 1, d2)
  inspect(simply, content="false")
  inspect(h2, content="0")
}

///|
test "b15-fiber-and-logic" {
  let (a, b, c, n) = @b15.b15_fiber_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="29")
  // Sierpiński 上排中律與雙重否定皆失敗、De Morgan 成立
  let (lem, dne, dm, _) = @b15.b15_internal_logic()
  inspect(lem, content="true")
  inspect(dne, content="true")
  inspect(dm, content="true")
}

///|
test "b15-descent-high" {
  let (a, b, c, n) = @b15.b15_descent_high_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="12")
  // 群值 Čech：圓環三成員覆蓋 H⁰/H¹/H² = (1,1,0)
  let h = @b15.b15_group_cech_dims(@b14.b14_m_circle(), [12, 13, 14], 3)
  inspect(@common.b_sh_arr_i32(h), content="[1, 1, 0]")
}

///|
test "b15-cone-les" {
  let (a, b, c, n) = @b15.b15_cone_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="2")
}

///|
test "b15-twistor" {
  let (a, b, c) = @b15.b15_twistor_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(
    @common.b_sh_arr_i32(@b15.b15_cpn_betti(3)),
    content="[1, 0, 1, 0, 1, 0, 1]",
  )
}

///|
test "b15-quasi-separated" {
  let (qs, n) = @b15.b15_qs_finite_check(3)
  inspect(qs, content="true")
  inspect(n, content="371")
  let (all, wits, _) = @b15.b15_qs_bounded_counterexample(4)
  inspect(all, content="true")
  inspect(@common.b_sh_arr_i32(wits), content="[1, 2, 3, 4]")
  let (found, s, nn, _) = @b15.b15_separated_counterexample()
  inspect(found, content="true")
  inspect(s, content="1")
  inspect(nn, content="2")
}
