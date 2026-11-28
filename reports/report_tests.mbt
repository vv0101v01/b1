///|
/// report_tests.mbt — 報告層的契約測試（集中一處，隨報告套件一起跑）。
///
/// 為什麼要搬出各批白盒測試：拆分資料夾後，模組套件不應依賴報告套件，
/// 否則會形成「拓撲斯 → 報告 → 拓撲斯」這種套件循環。報告的整體檢查
/// 因此集中在報告套件內的同名測試（批次三／四／九／十／十一）。

///|
/// 批次三報告：零 FAIL。
test "theorem3_report_all_pass" {
  let out = report3()
  assert_eq(b_sh_count_sub(out, "[FAIL]"), 0)
}

///|
/// 批次四報告：零 FAIL。
test "theorem4_report_all_pass" {
  let out = report4()
  assert_eq(b_sh_count_sub(out, "[FAIL]"), 0)
}

///|
/// 批次九報告：零 FAIL 且 PASS ≥ 60。
test "w9_report_all_green" {
  let r = report9()
  assert_eq(b_sh_count_sub(r, "[FAIL]"), 0)
  assert_true(b_sh_count_sub(r, "[PASS]") >= 60)
}

///|
/// 批次十報告：零 FAIL、PASS ≥ 45、標題與統計格式正確。
test "batch10_report" {
  let r = report10()
  assert_eq(b_sh_count_sub(r, "[FAIL]"), 0)
  assert_true(b_sh_count_sub(r, "[PASS]") >= 45)
  assert_true(
    @common.b_sh_contains(
      r, "批次十實驗報告（T349–T380、A49–A56）",
    ),
  )
  assert_true(@common.b_sh_contains(r, "PASS = "))
  assert_true(@common.b_sh_contains(r, "框架假設"))
  assert_true(@common.b_sh_contains(r, "負見證"))
  assert_true(@common.b_sh_contains(r, "A56"))
}

///|
/// 批次十一報告：零 FAIL、PASS ≥ 40、標題與統計格式正確。
test "batch11_report" {
  let r = report11()
  assert_eq(b_sh_count_sub(r, "[FAIL]"), 0)
  assert_true(b_sh_count_sub(r, "[PASS]") >= 40)
  assert_true(
    @common.b_sh_contains(
      r, "批次十一實驗報告（T381–T410、A57–A64）",
    ),
  )
  assert_true(@common.b_sh_contains(r, "PASS = "))
  assert_true(@common.b_sh_contains(r, "框架假設／限制"))
  assert_true(@common.b_sh_contains(r, "負見證"))
  assert_true(@common.b_sh_contains(r, "A64"))
}
