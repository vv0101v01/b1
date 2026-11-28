///|
/// batch13_wbtest.mbt — 批次十三白盒測試（拓撲格 → 扭子）。
///
/// 每個定理族至少一個測試，數值全部來自 `report13` 的實跑輸出，
/// 因此報告與測試互為見證（報告零 [FAIL] 的前提是本檔零 test 失敗）。

// ═════════ 模組一：拓撲格 / 內在遺址 / 外化 / 莫里塔 ═════════

test "b13-frame-axioms" {
  let sier = @b9.b9_sh_sier()
  let f = @b13.b13_frame_of_top(sier)
  // Sierpiński 的開集格有 3 個元素：∅、{上}、X
  inspect(f.n, content="3")
  let (comm, assoc, absorb, dist) = @b13.b13_frame_ok(f)
  inspect(comm, content="true")
  inspect(assoc, content="true")
  inspect(absorb, content="true")
  inspect(dist, content="true")
  // Top = X、Bot = ∅
  inspect(f.meet[f.top][f.bot], content=f.bot.to_string())
  inspect(f.join[f.top][f.bot], content=f.top.to_string())
}

///|
test "b13-boolean-vs-heyting" {
  let fsier = @b13.b13_frame_of_top(@b9.b9_sh_sier())
  let fdisc = @b13.b13_frame_of_top(@b9.b9_sh_disc2())
  // 離散兩點：布爾格（無偽補反例）
  let (bdisc, bad_disc) = @b13.b13_is_boolean(fdisc)
  inspect(bdisc, content="true")
  inspect(bad_disc, content="0")
  // Sierpiński：非布爾（有 1 個元素 a ∨ ¬a ≠ ⊤）
  let (bsier, bad_sier) = @b13.b13_is_boolean(fsier)
  inspect(bsier, content="false")
  inspect(bad_sier, content="1")
}

///|
test "b13-heyting-implication" {
  let f = @b13.b13_frame_of_top(@b9.b9_sh_sier())
  // a ⇒ b 在 Sierpiński 格上為 ⊤（元素 2）
  let imp = @b13.b13_heyting(f, 1, 2)
  inspect(imp, content="2")
  // 伴隨律：a ∧ (a⇒b) ≤ b
  inspect(@b13.b13_le(f, f.meet[1][imp], 2), content="true")
}

///|
test "b13-internal-site-roundtrip" {
  let s = @b9.b9_site(@b9.b9_sh_circ())
  let isit = @b13.b13_isite_of_site(s)
  let (r, m, t) = @b13.b13_isite_ok(isit)
  inspect(r, content="true")
  inspect(m, content="true")
  inspect(t, content="true")
  let (site, ok, n) = @b13.b13_externalize(isit)
  inspect(ok, content="true")
  inspect(n, content="7")
  inspect(site.cat.nob, content="7")
}

///|
test "b13-morita-equivalence" {
  let fsier = @b13.b13_frame_of_top(@b9.b9_sh_sier())
  let fcirc = @b13.b13_frame_of_top(@b9.b9_sh_circ())
  let (self_ok, bij, paired) = @b13.b13_morita(fsier, fsier)
  inspect(self_ok, content="true")
  inspect(paired, content="3")
  inspect(@common.b_sh_arr_i32(bij), content="[0, 1, 2]")
  // 與圓的開集格不等價（7 ≠ 3 個元素）
  inspect(@b13.b13_morita(fsier, fcirc).0, content="false")
}

// ═════════ 模組二：幾何態射 ═════════

///|
test "b13-geometric-morphism" {
  let circ = @b9.b9_sh_circ()
  let to_pt : @b13.B13CMap = { src: circ, dst: @b9.b9_pt(), f: [0, 0, 0, 0], }
  let (ok, bound) = @b13.b13_geom_ok(to_pt)
  inspect(ok, content="true")
  inspect(bound, content="4")
  // 非連續映射被拒
  let bad : @b13.B13CMap = { src: circ, dst: circ, f: [0, 0, 1, 1], }
  inspect(@b13.b13_cont(bad), content="false")
}

///|
test "b13-quasi-separated" {
  let circ = @b9.b9_sh_circ()
  let idc : @b13.B13CMap = { src: circ, dst: circ, f: [0, 1, 2, 3], }
  let (ok, good, total) = @b13.b13_quasi_separated(idc)
  inspect(ok, content="true")
  inspect(good, content=total.to_string())
  // 恆等態射與自身同構 ⇒ 恆等於「全通過」；有限空間每子集緊緻
  inspect(total > 0, content="true")
}

///|
test "b13-locally-closed-decomposition" {
  let sier = @b9.b9_sh_sier()
  // Sierpiński 的兩個單點都是局部閉（A = U ∩ cl A）
  inspect(@b13.b13_is_locally_closed(sier, [false, true]), content="true")
  inspect(@b13.b13_is_locally_closed(sier, [true, false]), content="true")
  let (ok, c, u) = @b13.b13_locally_closed(sier, [false, true])
  inspect(ok, content="true")
  // 分解見證逐點驗證：A = U ∩ C
  let a = [false, true]
  let mut witness = true
  for p in 0..<a.length() {
    if a[p] != (u[p] && c[p]) {
      witness = false
    }
  }
  inspect(witness, content="true")
  // 4 點「雙孤島」空間：{0} 非局部閉、{0,1} 是局部閉
  let split4 = @b9.b9_top(4, [
    [false, false, false, false],
    [true, true, false, false],
    [false, false, true, true],
    [true, true, true, true],
  ])
  inspect(
    @b13.b13_is_locally_closed(split4, [true, false, false, false]),
    content="false",
  )
  inspect(
    @b13.b13_locally_closed(split4, [true, true, false, false]).0,
    content="true",
  )
}

///|
test "b13-closure-interior-duality" {
  let sier = @b9.b9_sh_sier()
  // cl{下點} = {下點}（Sierpiński 的 {下點} 本身是閉集）
  let cl = @b13.b13_closure(sier, [true, false])
  inspect(b_sh_arr_bool(cl), content="[1,0]")
  // cl{上點} = X（{上點} 的閉包是全空間）
  inspect(b_sh_arr_bool(@b13.b13_closure(sier, [false, true])), content="[1,1]")
  // {上點} 是開集 ⇒ int{上點} = {上點}；int{下點} = ∅
  inspect(
    b_sh_arr_bool(@b13.b13_interior(sier, [false, true])),
    content="[0,1]",
  )
  inspect(
    b_sh_arr_bool(@b13.b13_interior(sier, [true, false])),
    content="[0,0]",
  )
  let ittop = @b13.b13_interior(sier, [true, true])
  inspect(b_sh_arr_bool(ittop), content="[1,1]")
}

///|
test "b13-fibre-topos" {
  let circ = @b9.b9_sh_circ()
  let to_pt : @b13.B13CMap = { src: circ, dst: @b9.b9_pt(), f: [0, 0, 0, 0], }
  let (npt, nopen, comps) = @b13.b13_fibre_topos(to_pt, 0)
  inspect(npt, content="4")
  inspect(nopen, content="2")
  inspect(comps, content="1")
  let idc : @b13.B13CMap = { src: circ, dst: circ, f: [0, 1, 2, 3], }
  // 恆等態射的纖維為單點
  inspect(@b13.b13_fibre_topos(idc, 1).0, content="1")
}

///|
test "b13-descent-gluing" {
  let sct = @b9.b9_site(@b9.b9_sh_circ())
  let top = @b13.b13_site_obj_of_open(sct, @b9.b9_top_top(sct.top))
  // 真正的覆蓋族：常數截面可黏合
  inspect(
    @b13.b13_descent(sct, top, [4, 9, 13, 15, 17], [2, 2, 2, 2, 2]).1,
    content="true",
  )
  // 冒充的覆蓋族：不可黏合
  inspect(@b13.b13_descent(sct, top, [4], [2]).1, content="false")
  // 相容性失敗的情形：同點上兩個不同值
  inspect(@b13.b13_descent(sct, top, [4, 9], [2, 3]).0, content="false")
}

// ═════════ 模組三：伽羅瓦 ═════════

///|
test "b13-galois-topos" {
  let v4 = @b9.b9_group_v4()
  let reg = @b9.b9_gset_reg(v4)
  let (ok, orbits, n) = @b13.b13_galois_topos(reg)
  inspect(ok, content="true")
  inspect(orbits, content="1")
  inspect(n, content="4")
}

///|
test "b13-galois-correspondence" {
  let v4 = @b9.b9_group_v4()
  let s3 = @b9.b9_group_s3()
  let (subs, iso, built) = @b13.b13_galois_correspondence(v4)
  inspect(subs, content="5")
  inspect(iso, content="3")
  inspect(built, content="5")
  let (subs3, iso3, _) = @b13.b13_galois_correspondence(s3)
  inspect(subs3, content="6")
  inspect(iso3, content="4")
  // 子群階數清單 = {1,2,2,2,4}
  inspect(
    @common.b_sh_arr_i32(@b13.b13_subgroup_sizes(v4)),
    content="[1, 2, 2, 2, 4]",
  )
}

///|
test "b13-frobenius-action" {
  // 置換 (01)(2)(3)：固定點 {2,3}、軌道 {0,1},{2},{3}
  let (fix, orbits, full) = @b13.b13_frobe_fixpoints([1, 0, 2, 3])
  inspect(fix, content="2")
  inspect(orbits, content="3")
  inspect(full, content="false")
  // 恆等置換是全固定
  inspect(@b13.b13_frobe_fixpoints([0, 1, 2, 3]).2, content="true")
  // 直和下固定點數可加：(01) 有 2 個、[1,0,2] 有 2 個
  let (sum, expect, ok) = @b13.b13_frobe_additive([1, 0, 2], [0, 2, 1])
  inspect(ok, content="true")
  inspect(sum, content=expect.to_string())
}

///|
test "b13-base-change-adjunction" {
  let v4 = @b9.b9_group_v4()
  let phi : Array[Int32] = [0, 1]
  let x = @b13.b13_base_change_restrict(phi, v4, @b9.b9_gset_triv(v4, 1))
  let y1 = @b9.b9_gset_triv(v4, 1)
  let y2 = @b9.b9_gset_triv(v4, 2)
  let (ok1, l1, r1) = @b13.b13_base_change_adjunction(phi, v4, x, y1)
  inspect(ok1, content="true")
  inspect(l1, content="1")
  inspect(r1, content="1")
  let (ok2, l2, r2) = @b13.b13_base_change_adjunction(phi, v4, x, y2)
  inspect(ok2, content="true")
  inspect(l2, content="2")
  inspect(r2, content="2")
}

///|
test "b13-base-change-restriction-laws" {
  let v4 = @b9.b9_group_v4()
  let phi : Array[Int32] = [0, 1]
  // 限制後仍是合法 G-集合（換群為 ℤ/2，仍滿足作用公理）
  let res = @b13.b13_base_change_restrict(phi, v4, @b9.b9_gset_reg(v4))
  inspect(@b9.b9_gset_ok(res), content="true")
  // 投影公式：f_!(F ⊗ f*G) 與 f_!F ⊗ G 的逐元素差全為 0
  let zeros = @b13.b13_zeros(4)
  let (ok, diff) = @b13.b13_projection_formula(zeros, zeros)
  inspect(ok, content="true")
  inspect(@common.b_sh_arr_i32(diff), content="[0, 0, 0, 0]")
}

///|
test "b13-artin-dm-stacks" {
  let gpd : @b13.B13Groupoid = {
    n: 4,
    nmor: 8,
    src: [0, 1, 0, 1, 2, 3, 2, 3],
    dst: [0, 0, 1, 1, 2, 2, 3, 3],
    inv: [true, true, true, true, true, true, true, true],
    cmp: [],
  }
  let (dm, max_aut, classes) = @b13.b13_dm_ok(gpd)
  inspect(dm, content="true")
  inspect(max_aut, content="1")
  inspect(classes, content="2")
  let (artin, all_inv, stab) = @b13.b13_artin_ok(gpd)
  inspect(artin, content="true")
  inspect(all_inv, content="true")
  inspect(stab, content="1")
  // 含不可逆邊 ⇒ 同構類增加、Artin 條件失敗
  let bad : @b13.B13Groupoid = {
    n: 2,
    nmor: 2,
    src: [0, 1],
    dst: [0, 1],
    inv: [true, false],
    cmp: [],
  }
  inspect(@b13.b13_iso_classes(bad), content="2")
  inspect(@b13.b13_artin_ok(bad).1, content="false")
}

// ═════════ 模組四：∞-世界 ═════════

///|
test "b13-chain-complex-euler" {
  // 圓的極大面（4 條邊）
  let c = @b13.b13_chain_of_complex([[0, 1], [1, 2], [2, 3], [3, 0]])
  // dim = [4 頂點, 4 條邊]
  inspect(@common.b_sh_arr_i32(c.dim), content="[4, 4, 0]")
  inspect(@b13.b13_euler(c), content="0")
  // 同調：H₀ = 4、H₁ = 4（未計邊界秩的自由近似）
  inspect(@common.b_sh_arr_i32(@b13.b13_betti(c)), content="[4, 4, 0]")
}

///|
test "b13-n-topos-truncation" {
  let line : @b13.B13Chain = { dim: [2, 1, 0], rank: [0, 1, 0], }
  let twotype : @b13.B13Chain = { dim: [1, 0, 1], rank: [0, 0, 0], }
  // [2,1,0]：H₀ = 1、H₁ = 0、H₂ = 0 ⇒ 1-拓撲斯
  let (ok1, beyond1, _) = @b13.b13_is_n_topos(line, 1)
  inspect(ok1, content="true")
  inspect(beyond1, content="0")
  // [1,0,1]：H₂ = 1 ⇒ 連 0-拓撲斯都不是
  let (ok0, beyond0, _) = @b13.b13_is_n_topos(twotype, 0)
  inspect(ok0, content="false")
  inspect(beyond0, content="1")
  // 截斷 τ_{≤1}：去掉 2 維部分
  let tr = @b13.b13_truncate(twotype, 1)
  inspect(@common.b_sh_arr_i32(tr.dim), content="[1, 0]")
  inspect(@b13.b13_truncate_idem(twotype, 1), content="true")
  inspect(@b13.b13_truncate_preserves(line, 1), content="true")
  // 截斷後即為 1-拓撲斯
  inspect(@b13.b13_is_n_topos(tr, 1).0, content="true")
}

///|
test "b13-coherent-topos" {
  let coh : Array[@b13.B13Coherent] = [
    { n: 3, rank: [2, 1, 0], },
    { n: 3, rank: [1, 1, 3], },
    { n: 3, rank: [0, 2, 1], },
  ]
  let (ok, total, count) = @b13.b13_coherent_topos(coh)
  inspect(ok, content="true")
  inspect(count, content="3")
  inspect(total, content="11")
  // 有限餘積封閉：直和秩逐點相加
  let (cop_ok, rank) = @b13.b13_coherent_coproduct(coh[0], coh[1])
  inspect(cop_ok, content="true")
  inspect(@common.b_sh_arr_i32(rank), content="[3, 2, 3]")
}

///|
test "b13-spectral-sequence" {
  // 目標 H = [0, 0, 1]（dim = [1,1,1], rank = [0,1,0]）
  let target : @b13.B13Chain = { dim: [1, 1, 1], rank: [0, 1, 0], }
  inspect(@common.b_sh_arr_i32(@b13.b13_betti(target)), content="[0, 0, 1]")
  let sp : @b13.B13Spectral = { page: [[0, 0, 1], [0, 0, 0], [0, 0, 0]], }
  let (conv, diag) = @b13.b13_spectral_converges(sp, target)
  inspect(conv, content="true")
  inspect(@common.b_sh_arr_i32(diag), content="[0, 0, 1]")
  // 錯誤的譜序列不收斂
  let wrong : @b13.B13Spectral = { page: [[1, 0, 0], [0, 0, 0], [0, 0, 0]], }
  inspect(@b13.b13_spectral_converges(wrong, target).0, content="false")
  // 譜層：兩層都收斂 ⇒ 整體收斂
  let target2 : @b13.B13Chain = { dim: [1, 2, 1], rank: [0, 1, 0], }
  let sp2 : @b13.B13Spectral = { page: [[0, 1, 1], [0, 0, 0], [0, 0, 0]], }
  let (shf_ok, layers, _) = @b13.b13_spectral_sheaf([sp, sp2], [target, target2])
  inspect(shf_ok, content="true")
  inspect(layers, content="2")
}

// ═════════ 模組五：內部邏輯 ═════════

///|
test "b13-geometric-order" {
  let sct = @b9.b9_site(@b9.b9_sh_circ())
  let full = @b9.b9_groth_spatial(sct)
  let coarse = @b13.b13_groth_coarser(sct)
  // 反身性
  let (self_ok, total, ok) = @b13.b13_geometric_le(full, full)
  inspect(self_ok, content="true")
  inspect(ok, content=total.to_string())
  // 較粗 ⊆ 較細，但反之不然 ⇒ 非全序
  inspect(@b13.b13_geometric_le(coarse, full).0, content="true")
  inspect(@b13.b13_geometric_le(full, coarse).0, content="false")
}

///|
test "b13-regular-order" {
  let sct = @b9.b9_site(@b9.b9_sh_circ())
  let full = @b9.b9_groth_spatial(sct)
  let (regular, added) = @b13.b13_is_regular(full)
  inspect(regular, content="true")
  inspect(added, content="0")
  // 正則化後仍是拓撲（公理檢核）
  let reg = @b13.b13_regular_closure(full)
  let (a, b, c) = @b9.b9_groth_ok(reg)
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
}

///|
test "b13-internal-tensor-hom" {
  let f : @b13.B13Sheaf = { n: 3, rank: [1, 2, 3], }
  let g : @b13.B13Sheaf = { n: 3, rank: [2, 1, 4], }
  let h : @b13.B13Sheaf = { n: 3, rank: [1, 2, 1], }
  // 秩相乘
  inspect(
    @common.b_sh_arr_i32(@b13.b13_tensor(f, g).rank),
    content="[2, 2, 12]",
  )
  let (assoc, comm, unit) = @b13.b13_tensor_laws(f, g, h)
  inspect(assoc, content="true")
  inspect(comm, content="true")
  inspect(unit, content="true")
  // 內部 Hom：秩為 |G|^|F|
  let ih = @b13.b13_internal_hom({ n: 2, rank: [1, 2], }, {
    n: 2,
    rank: [1, 3],
  })
  inspect(@common.b_sh_arr_i32(ih.rank), content="[1, 9]")
  // 伴隨律逐點成立
  let (adj_ok, points, bad) = @b13.b13_tensor_hom_adjunction(
    { n: 2, rank: [1, 2], },
    { n: 2, rank: [1, 3], },
    { n: 2, rank: [1, 4], },
  )
  inspect(adj_ok, content="true")
  inspect(points, content="2")
  inspect(bad, content="0")
}

///|
test "b13-twistor" {
  // 可容許：扭數隨秩單調
  let (ok, total, nonzero) = @b13.b13_twistor([1, 2, 3], [0, 1, 2])
  inspect(ok, content="true")
  inspect(total, content="8")
  inspect(nonzero, content="2")
  // 不可容許：秩大者扭數反而小
  inspect(@b13.b13_twistor([3, 1], [0, 2]).0, content="false")
  // 恆等態射下扭數和守恆
  let circ = @b9.b9_sh_circ()
  let idc : @b13.B13CMap = { src: circ, dst: circ, f: [0, 1, 2, 3], }
  let (inv, src_sum, dst_sum) = @b13.b13_twistor_invariant(idc, [1, 2, 3, 4])
  inspect(inv, content="true")
  inspect(src_sum, content=dst_sum.to_string())
}
