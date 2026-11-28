///|
/// batch9_wbtest.mbt — 批次九白盒測試（T294–T348、A39–A48）
///
/// 每個測試對應一個模組，斷言全部為整數／布林值精確等式。

///|
test "w9 site heyting and sieves" {
  for (_, t) in b10r_spaces() {
    assert_true(b9_top_ok(t))
    let s = b9_site(t)
    for v in 0..<s.cat.nob {
      assert_true(b9_sieve_distrib(s.cat, v))
      assert_true(b9_gen_cover_agree(s, v))
      // 篩格模律
      let all = b9_all_sieves(s.cat, v)
      for i in 0..<all.length() {
        for j in 0..<all.length() {
          assert_eq(
            b9_sieve_inter(all[i], all[j]).length() +
            b9_sieve_union(all[i], all[j]).length(),
            all[i].length() + all[j].length(),
          )
        }
      }
    }
    let (a, b, c) = b9_topology_ok(s)
    assert_true(a)
    assert_true(b)
    assert_true(c)
  }
}

///|
test "w9 sieve counts" {
  let s = b9_site(b9_sh_sier())
  assert_eq(b9_all_sieves(s.cat, 0).length(), 2)
  assert_eq(b9_all_sieves(s.cat, 1).length(), 3)
  let s2 = b9_site(b9_sh_circ())
  let cnts : Array[Int32] = []
  for v in 0..<s2.cat.nob {
    cnts.push(b9_all_sieves(s2.cat, v).length())
  }
  assert_eq(cnts.length(), 6)
  assert_eq(cnts[0], 2)
  assert_eq(cnts[1], 2)
  assert_eq(cnts[2], 5)
  assert_eq(cnts[5], 9)
}

///|
test "w9 pretopology equals spatial topology" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    let p = b9_pre_canonical(s)
    let (a, b, c) = b9_pre_ok(p)
    assert_true(a)
    assert_true(b)
    assert_true(c)
    assert_true(b9_pre_transitive(p))
    assert_true(b9_pre_matches_spatial(s, p))
    let arr = b9_topology_of_pre(p)
    for v in 0..<s.cat.nob {
      assert_eq(arr[v].length(), b9_covering_sieves(s, v).length())
    }
  }
}

///|
test "w9 sheaves and sheafification" {
  let s = b9_site(b9_sh_circ())
  let g = b9_groth_spatial(s)
  let (a, b, c) = b9_groth_ok(g)
  assert_true(a)
  assert_true(b)
  assert_true(c)
  for v in 0..<s.cat.nob {
    assert_true(b9_is_sheaf(g, b8_ps_yoneda(s.cat, v)))
  }
  assert_true(b9_is_sheaf(g, b8_ps_const(s.cat, 0)))
  assert_true(b9_is_sheaf(g, b8_ps_const(s.cat, 1)))
  // 常數預層 2：圓上有不連通開集 ⟹ 非層
  assert_false(b9_is_sheaf(g, b8_ps_const(s.cat, 2)))
  let c2 = b8_ps_const(s.cat, 2)
  assert_true(b9_is_sheaf(g, b9_sheafify(g, c2)))
  assert_true(b9_sheafify_idem(g, c2))
}

///|
test "w9 constant presheaf is sheaf iff all opens connected" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    let g = b9_groth_spatial(s)
    let mut all_conn = true
    for v in 0..<s.cat.nob {
      if b9_comp_count(s, v) != 1 {
        all_conn = false
      }
    }
    assert_eq(b9_is_sheaf(g, b8_ps_const(s.cat, 2)), all_conn)
  }
  // Sierpiński 的每個開集連通 ⟹ 常數 2 是層
  let s = b9_site(b9_sh_sier())
  assert_true(b9_is_sheaf(b9_groth_spatial(s), b8_ps_const(s.cat, 2)))
}

///|
test "w9 stalks of representables are characteristic functions" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    for v in 0..<s.cat.nob {
      let y = b8_ps_yoneda(s.cat, v)
      let ov = t.opens[s.opens[v]]
      for p in 0..<t.npt {
        let mut ex = false
        for w in 0..<s.cat.nob {
          let ow = t.opens[s.opens[w]]
          let mut le = true
          for q in 0..<t.npt {
            if ow[q] && !ov[q] {
              le = false
            }
          }
          if le && ow[p] {
            ex = true
          }
        }
        assert_eq(b9_stalk_count(y, s, p), if ex { 1 } else { 0 })
      }
    }
  }
}

///|
test "w9 points are sufficient" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    assert_true(b9_points_distinguished(s))
    let g = b9_groth_spatial(s)
    let f = b9_sheafify(g, b8_ps_const(s.cat, 2))
    assert_true(b9_points_separate_sections(s, f))
    let (l, r) = b9_point_adjunction(s, b8_ps_const(s.cat, 2), 0, 2)
    assert_eq(l, r)
  }
}

///|
test "w9 geometric morphisms" {
  let s = b9_site(b9_sh_sier())
  let g = b9_groth_spatial(s)
  let u = b9_open_fun([0, 1], s, s)
  assert_true(b9_cont_ok([0, 1], s, s))
  let c2 = b8_ps_const(s.cat, 2)
  let (l, r) = b9_geom_adjoint(u, g, c2, c2)
  assert_eq(l, r)
  assert_true(b9_preserves_terminal(u, g))
  assert_true(b9_preserves_prod(u, g, c2, c2))
  assert_true(b9_direct_preserves_sheaf(u, g, c2))
}

///|
test "w9 inverse image is local constant on preimage" {
  let spt = b9_site(b9_pt())
  let gpt = b9_groth_spatial(spt)
  for (_, t) in b10r_spaces() {
    let y = b9_site(t)
    let fmap : Array[Int32] = []
    for _ in 0..<t.npt {
      fmap.push(0)
    }
    assert_true(b9_cont_ok(fmap, spt, y))
    let u = b9_open_fun(fmap, spt, y)
    let f2 = b9_inverse(u, b9_groth_spatial(y), b8_ps_const(spt.cat, 2))
    for v in 0..<y.cat.nob {
      assert_eq(f2.sz[v], b8_pow_int(2, b9_comp_count(y, v)))
    }
  }
  let _ = gpt
}

///|
test "w9 subobject classifier" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    let om = b9_omega(s)
    for v in 0..<s.cat.nob {
      assert_eq(om.sz[v], b9_all_sieves(s.cat, v).length())
    }
    assert_eq(
      b9_classifier_check(s, b8_ps_const(s.cat, 1)).0,
      b9_classifier_check(s, b8_ps_const(s.cat, 1)).1,
    )
    let (a, b) = b9_classifier_check(s, b8_ps_const(s.cat, 2))
    assert_eq(a, b)
    for v in 0..<s.cat.nob {
      let (c, d) = b9_classifier_check(s, b8_ps_yoneda(s.cat, v))
      assert_eq(c, d)
    }
  }
  // Sierpiński：|Ω| = [2, 3]，|Sub(1)| = 3
  let s = b9_site(b9_sh_sier())
  let om = b9_omega(s)
  assert_eq(om.sz[0], 2)
  assert_eq(om.sz[1], 3)
  assert_eq(b9_sub_count(b8_ps_const(s.cat, 1)), 3)
}

///|
test "w9 local operators on Sierpinski" {
  let s = b9_site(b9_sh_sier())
  let lts = b9_lt_enumerate(s)
  assert_eq(lts.length(), 4)
  for l in lts {
    let (a, b, c, d) = b9_lt_ok(l)
    assert_true(a)
    assert_true(b)
    assert_true(c)
    assert_true(d)
    let g = b9_topology_of_lt(l)
    let (x, y, z) = b9_groth_ok(g)
    assert_true(x)
    assert_true(y)
    assert_true(z)
    assert_eq(b9_lt_of_groth(g).lt.length(), l.lt.length())
  }
}

///|
test "w9 open and closed subtoposes" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    let gsp = b9_groth_spatial(s)
    for u in 0..<s.cat.nob {
      let jo = b9_open_topology(s, u)
      let jc = b9_closed_topology(s, u)
      let (a, b, c) = b9_groth_ok(jo)
      assert_true(a)
      assert_true(b)
      assert_true(c)
      let (d, e, f) = b9_groth_ok(jc)
      assert_true(d)
      assert_true(e)
      assert_true(f)
      // 子拓撲斯：J ⊆ J_U、J ⊆ J^U
      assert_true(b9_groth_le(gsp, jo))
      assert_true(b9_groth_le(gsp, jc))
      // J_U ⊆ J ⟺ U = X
      assert_eq(b9_groth_le(jo, gsp), u == s.cat.nob - 1)
      // 閉子拓撲斯不退化為原拓撲
      assert_false(b9_groth_le(jc, gsp))
    }
    let jd = b9_dense_topology(s)
    let (g1, g2, g3) = b9_groth_ok(jd)
    assert_true(g1)
    assert_true(g2)
    assert_true(g3)
    assert_true(b9_groth_le(gsp, jd))
  }
}

///|
test "w9 group and G-set axioms" {
  for g in [b9_group_zn(2), b9_group_zn(3), b9_group_v4(), b9_group_s3()] {
    assert_true(b9_group_ok(g))
    assert_true(b9_gset_ok(b9_gset_reg(g)))
    assert_true(b9_gset_ok(b9_gset_triv(g, 2)))
  }
  assert_eq(b9_group_zn(2).k, 2)
  assert_eq(b9_group_zn(3).k, 3)
  assert_eq(b9_group_v4().k, 4)
  assert_eq(b9_group_s3().k, 6)
}

///|
test "w9 orbit stabilizer and Burnside" {
  for g in [b9_group_zn(2), b9_group_zn(3), b9_group_v4(), b9_group_s3()] {
    let reg = b9_gset_reg(g)
    let mut sum_stab = 0
    for x in 0..<reg.n {
      sum_stab = sum_stab + b9_stab_size(reg, x)
    }
    assert_eq(sum_stab, g.k * b9_orbit_count(reg))
    let mut sum_fix = 0
    for gi in 0..<g.k {
      sum_fix = sum_fix + b9_fix_count(reg, gi)
    }
    assert_eq(sum_fix, g.k * b9_orbit_count(reg))
    // 正則作用：單一軌道、無不變量
    assert_eq(b9_orbit_count(reg), 1)
    assert_eq(@b9.b9_invariants(reg), 0)
    let triv2 = b9_gset_triv(g, 2)
    assert_eq(@b9.b9_invariants(triv2), 2)
    assert_eq(b9_orbit_count(triv2), 2)
  }
}

///|
test "w9 torsor counts" {
  assert_eq(@b9.b9_torsor_bruteforce(b9_group_zn(2)), 1)
  assert_eq(@b9.b9_torsor_bruteforce(b9_group_zn(3)), 2)
  for g in [b9_group_zn(2), b9_group_zn(3), b9_group_v4(), b9_group_s3()] {
    assert_eq(@b9.b9_torsor_count(g), @b9.b9_fact(g.k) / g.k)
    assert_eq(@b9.b9_torsor_aut(g), g.k)
  }
  assert_eq(@b9.b9_torsor_count(b9_group_v4()), 6)
  assert_eq(@b9.b9_torsor_count(b9_group_s3()), 120)
}

///|
test "w9 Cech cohomology of the circle" {
  let t = b9_sh_circ()
  let s = b9_site(t)
  let mx = s.cat.nob - 1
  let mut u1 = -1
  let mut u2 = -1
  for v in 0..<s.cat.nob {
    if b9_comp_count(s, v) == 1 && b9_top_card(t, s.opens[v]) == 3 {
      u1 = v
    }
  }
  for v in 0..<s.cat.nob {
    if v != u1 &&
      b9_top_card(t, s.opens[v]) == 3 &&
      b9_site_inter(s, u1, v) >= 0 {
      u2 = v
    }
  }
  assert_eq(u1, 4)
  assert_eq(u2, 3)
  let cv : B9Cover = {
    site: s,
    v: mx,
    fam: [b9_site_incl(s, u1, mx), b9_site_incl(s, u2, mx)],
  }
  assert_eq(b9_cech_dim(cv, 0), 2)
  assert_eq(b9_cech_dim(cv, 1), 2)
  assert_eq(b9_cech_dim(cv, 2), 0)
  assert_eq(b9_cech_h(cv, 0, 5), 1)
  assert_eq(b9_cech_h(cv, 1, 5), 1)
  assert_eq(b9_cech_h(cv, 2, 5), 0)
  assert_eq(b9_cech_euler(cv, 2, 5), 0)
}

///|
test "w9 Cech cohomology on discrete and Sierpinski" {
  let s = b9_site(b9_sh_disc2())
  let mx = s.cat.nob - 1
  let fam : Array[Int32] = []
  for v in 0..<s.cat.nob {
    if v != mx && b9_site_inter(s, v, mx) == v {
      let mut maximal = true
      for w in 0..<s.cat.nob {
        if w != v &&
          w != mx &&
          b9_site_inter(s, v, w) == v &&
          b9_site_inter(s, w, mx) == w {
          maximal = false
        }
      }
      if maximal {
        fam.push(b9_site_incl(s, v, mx))
      }
    }
  }
  let cv : B9Cover = { site: s, v: mx, fam, }
  assert_eq(b9_cech_h(cv, 0, 5), 2)
  assert_eq(b9_cech_h(cv, 1, 5), 0)
  assert_eq(b9_cech_euler(cv, 2, 5), 2)
}

///|
test "w9 group cohomology table" {
  let z2 = b9_group_zn(2)
  assert_eq(b9_group_h(z2, 0, 2), 1)
  assert_eq(b9_group_h(z2, 1, 2), 1)
  assert_eq(b9_group_h(z2, 2, 2), 1)
  assert_eq(b9_group_h(z2, 0, 3), 1)
  assert_eq(b9_group_h(z2, 1, 3), 0)
  let z3 = b9_group_zn(3)
  assert_eq(b9_group_h(z3, 1, 3), 1)
  assert_eq(b9_group_h(z3, 1, 2), 0)
  let v4 = b9_group_v4()
  assert_eq(b9_group_h(v4, 0, 2), 1)
  assert_eq(b9_group_h(v4, 1, 2), 2)
  assert_eq(b9_group_h(v4, 2, 2), 3)
  let s3 = b9_group_s3()
  assert_eq(b9_group_h(s3, 1, 2), 1)
  assert_eq(b9_group_h(s3, 1, 3), 0)
  // H¹ 與 Hom(G, F_p) 一致
  assert_eq(b9_hom_to_fp(z2, 2), 2)
  assert_eq(b9_hom_to_fp(z3, 3), 3)
  assert_eq(b9_hom_to_fp(v4, 2), 4)
  assert_eq(b9_hom_to_fp(s3, 2), 2)
}

///|
test "w9 modular rank" {
  // Z/3 的 d¹（9 × 3）在 F_3 上秩為 3
  let g = b9_group_zn(3)
  let d1 = @b9.b9_bar_diff(g, 1, 3)
  assert_eq(d1.1, 9)
  assert_eq(d1.2, 3)
  assert_eq(b9_rank_mod(d1.0, d1.2, 3), 2)
  // F_2 上同一複形的秩
  let d1b = @b9.b9_bar_diff(b9_group_zn(2), 0, 2)
  assert_eq(b9_rank_mod(d1b.0, d1b.2, 2), 0)
}

///|
test "w9 Giraud axioms and coherence" {
  for (_, t) in b10r_spaces() {
    let s = b9_site(t)
    let (ok, k) = b9_site_coherent(s)
    assert_true(ok)
    assert_true(k > 0)
    // 可表預層對濾過餘極限緊緻
    let chain : Array[B8PS] = [
      b8_ps_const(s.cat, 1),
      b8_ps_const(s.cat, 2),
      b8_ps_const(s.cat, 3),
    ]
    for v in 0..<s.cat.nob {
      let (l, r, step) = b9_compact_check(b8_ps_yoneda(s.cat, v), chain)
      assert_eq(l, r)
      assert_true(step <= 2)
    }
    // 餘積不交且泛
    let f = b8_ps_const(s.cat, 2)
    let g = b8_ps_yoneda(s.cat, 0)
    assert_true(b9_coprod_disjoint(f, g))
    assert_true(b9_coprod_universal(f, g, f))
    // 有限極限／餘極限
    let (a, b, c, d) = b9_lex_ok(b8_cat_arrow())
    assert_true(a)
    assert_true(b)
    assert_true(c)
    assert_true(d)
  }
}

///|
test "w9 density and small generating set" {
  let s = b9_site(b9_sh_sier())
  for v in 0..<s.cat.nob {
    let (l, r) = b9_density_check(b8_ps_yoneda(s.cat, v))
    assert_eq(l, r)
    let (l2, r2) = @b9.b9_generator_density(b8_ps_yoneda(s.cat, v))
    assert_eq(l2, r2)
  }
  let (l, r) = b9_density_check(b8_ps_const(s.cat, 3))
  assert_eq(l, r)
  assert_true(b9_reps_generate(b8_ps_const(s.cat, 2), b8_ps_yoneda(s.cat, 0)))
}

///|
test "w9 kernel pairs and regular epis" {
  let s = b9_site(b9_sh_sier())
  let y1 = b8_ps_yoneda(s.cat, 1)
  let one = b8_ps_const(s.cat, 1)
  let f : Array[Int32] = []
  for v in 0..<s.cat.nob {
    for _ in 0..<y1.sz[v] {
      f.push(0)
    }
  }
  let kp = b9_kernel_pair(y1, one, f)
  assert_true(b8_ps_ok(kp))
  for v in 0..<s.cat.nob {
    assert_eq(kp.sz[v], y1.sz[v])
  }
  assert_true(b9_effective_epi(y1, one, f))
  // const 2 → 1：核對大小 = 4 × 物件數
  let c2 = b8_ps_const(s.cat, 2)
  let f2 : Array[Int32] = []
  for v in 0..<s.cat.nob {
    for _ in 0..<c2.sz[v] {
      f2.push(0)
    }
  }
  let kp2 = b9_kernel_pair(c2, one, f2)
  assert_eq(kp2.sz[0], 4)
  assert_true(b9_effective_epi(c2, one, f2))
  // 非滿射 ⟹ 非正則滿
  let fz : Array[Int32] = []
  for v in 0..<s.cat.nob {
    for _ in 0..<c2.sz[v] {
      fz.push(0)
    }
  }
  assert_false(b9_effective_epi(c2, c2, fz))
}

///|
test "w9 equivalence relations are effective" {
  let s = b9_site(b9_sh_sier())
  // 離散關係：商大小 = 元素總數
  let c3 = b8_ps_const(s.cat, 3)
  let rep : Array[Array[Int32]] = []
  for _ in 0..<s.cat.nob {
    let row : Array[Int32] = []
    for x in 0..<c3.sz[0] {
      row.push(x)
    }
    rep.push(row)
  }
  let r : B9Rel = { a: c3, rep, }
  assert_true(b9_rel_stable(r))
  assert_true(b9_rel_effective(r))
  assert_eq(b9_rel_quot_size(r), 6)
  // 泛關係：商大小 = 物件數
  let rep2 : Array[Array[Int32]] = []
  for _ in 0..<s.cat.nob {
    let row : Array[Int32] = []
    for x in 0..<c3.sz[0] {
      let _ = x
      row.push(0)
    }
    rep2.push(row)
  }
  let r2 : B9Rel = { a: c3, rep: rep2, }
  assert_true(b9_rel_stable(r2))
  assert_eq(b9_rel_quot_size(r2), 2)
  // 非自然的分類函數 ⟹ 不穩定
  // 在頂物件上合併、其餘物件上不合并的分類函數（非自然）
  let cls : Array[Int32] = []
  for v in 0..<s.cat.nob {
    for x in 0..<c3.sz[v] {
      cls.push(if v == s.cat.nob - 1 { 0 } else { x })
    }
  }
  let r3 = @b9.b9_rel_of_class(c3, cls)
  assert_false(b9_rel_stable(r3))
}

///|
test "w9 Bell numbers partition enumeration" {
  let s = b9_site(b9_sh_sier())
  for n in [2, 3, 4] {
    let cn = b8_ps_const(s.cat, n)
    let rs = b9r_rgs(n)
    let mut eff = 0
    for rg in rs {
      let rep : Array[Array[Int32]] = []
      for _ in 0..<s.cat.nob {
        let row : Array[Int32] = []
        for x in 0..<n {
          row.push(rg[x])
        }
        rep.push(row)
      }
      let r : B9Rel = { a: cn, rep, }
      if b9_rel_effective(r) {
        eff = eff + 1
      }
    }
    assert_eq(eff, rs.length())
  }
  assert_eq(b9r_rgs(2).length(), 2)
  assert_eq(b9r_rgs(3).length(), 5)
  assert_eq(b9r_rgs(4).length(), 15)
}

///|
test "w9 classifying topos of G-torsors" {
  for g in [b9_group_zn(2), b9_group_zn(3), b9_group_v4(), b9_group_s3()] {
    let u = b9_univ_torsor(g)
    let (free, trans) = b9_torsor_frame(u)
    assert_true(free)
    assert_true(trans)
    assert_eq(u.n, g.k)
    // 表示性：|Hom(U, X)| = |X|
    let (a, b) = b9_represent(b9_gset_regular2(g))
    assert_eq(a, b)
    let (c, d) = b9_classify_check(g, b9_gset_reg(g))
    assert_eq(c, d)
    // Aut(U) = |G|，點單一
    assert_eq(b9_aut_univ(g), g.k)
    assert_eq(b9_point_iso_count(g), 1)
    assert_eq(@b9.b9_torsor_iso_count(g), g.k)
    // Ω = 2
    let (om, nat) = b9_omega_gset(g)
    assert_eq(om, 2)
    assert_eq(nat, 2)
  }
}

///|
test "w9 subobject counts in Set[G]" {
  let g = b9_group_zn(3)
  for n in [1, 2, 3] {
    let (a, b) = b9_classifier(b9_gset_triv(g, n))
    assert_eq(a, b)
    assert_eq(a, b8_pow_int(2, n))
  }
  let (a, b) = b9_classifier(b9_gset_reg(g))
  assert_eq(a, b)
  assert_eq(a, 2)
  let (c, d) = b9_classifier(b9_gset_regular2(g))
  assert_eq(c, d)
  assert_eq(c, 4)
}

///|
/// 輔助 API 的覆蓋測試：這些函式先前只在臨時探針中使用，現固化為白盒斷言。
test "w9 auxiliary API coverage" {
  let t = b9_sh_sier()
  let s = b9_site(t)
  // 站物件 ↔ 開集編號
  for v in 0..<s.cat.nob {
    assert_eq(@b9.b9_site_open(s, v), s.opens[v])
  }
  // 柄的整體快照 == 逐點計數
  let c2 = b8_ps_const(s.cat, 2)
  let all = @b9.b9_stalk_all(c2, s)
  assert_eq(all.length(), t.npt)
  for p in 0..<t.npt {
    assert_eq(all[p], b9_stalk_count(c2, s, p))
  }
  // 層 ⟹ 分離
  let g = b9_groth_spatial(s)
  assert_true(@b9.b9_is_separated(g, b8_ps_const(s.cat, 1)))
  assert_true(@b9.b9_sheafify_pointwise(s, g, c2))
  // 子拓撲斯的分類器：|Sub_{Sh_J}(F)| = |Nat(F, Ω_J)|
  let omj = @b9.b9_omega_j(g)
  for n in [1, 2] {
    let f = b9_sheafify(g, b8_ps_const(s.cat, n))
    assert_eq(@b9.b9_sub_count_sh(g, f), b8_nat_count(f, omj))
  }
  // 不可分空間：只有兩個開集，站只有一個物件
  let ind = @b9.b9_indiscrete(2)
  assert_true(b9_top_ok(ind))
  assert_eq(b9_site(ind).cat.nob, 1)
  // 由置換表直接建構作用：正則作用可重建且為單一軌道
  let g2 = b9_group_zn(3)
  let reg = b9_gset_reg(g2)
  let rebuilt = @b9.b9_gset_of_perms(g2, reg.n, reg.act)
  assert_true(b9_gset_ok(rebuilt))
  assert_eq(b9_orbit_count(rebuilt), 1)
  assert_eq(b9_stab_size(rebuilt, 0), 1)
}
