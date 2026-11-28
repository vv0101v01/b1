///|
/// common/shared.mbt — 跨批次共用的小工具（去重後的單一實作）。
///
/// 批次七至十一的報告生成器原本各自複製了 `count_sub`、整數／布林陣列比較
/// 與報告行產生器，此處集中一份，避免同一段程式碼出現三到四個副本。
/// 測試空間幾何（sierpiński／離散兩點／S¹／特殊化序）已移至 `packages/topos/site9.mbt`，
/// 以免本套件反向依賴拓撲斯層。

///|
/// 計數子字串出現次數（不重疊匹配）。
pub fn b_sh_count_sub(hay : String, needle : String) -> Int32 {
  let hl = hay.length()
  let nl = needle.length()
  if nl == 0 {
    return 0
  }
  let mut count = 0
  let mut i = 0
  while i + nl <= hl {
    let mut j = 0
    let mut ok = true
    while j < nl {
      if hay.code_unit_at(i + j) != needle.code_unit_at(j) {
        ok = false
        break
      }
      j = j + 1
    }
    if ok {
      count = count + 1
      i = i + nl
    } else {
      i = i + 1
    }
  }
  count
}

///|
/// 報告行的統一產生器（批次九／十／十一共用，消除三份複製）。
pub fn b_sh_line(tag : String, cond : Bool, detail : String) -> String {
  let head = if cond { "[PASS] " } else { "[FAIL] " }
  head + tag + "  " + detail + "\n"
}

///|
/// 整數陣列轉字串（無需 `Show`）。
pub fn b_sh_arr_i32(a : Array[Int32]) -> String {
  let mut s = "["
  for i in 0..<a.length() {
    if i > 0 {
      s = s + ", "
    }
    s = s + a[i].to_string()
  }
  s + "]"
}

///|
/// 子字串存在性判定（測試輔助，單一實作）。
pub fn b_sh_contains(hay : String, needle : String) -> Bool {
  b_sh_count_sub(hay, needle) > 0
}

///|
/// 陣列逐元素相等（`Eq` 泛型，取代 Int32／Bool／矩陣三份複製）。
pub fn[T : Eq] b_sh_arr_eq(a : Array[T], b : Array[T]) -> Bool {
  @core.go_arr_eq(a, b)
}

///|
/// 矩陣逐元素相等（嵌套陣列走 `b_sh_arr_eq`）。
pub fn[T : Eq] b_sh_mat_eq(a : Array[Array[T]], b : Array[Array[T]]) -> Bool {
  b_sh_arr_eq(a, b)
}

///|
/// 布林陣列轉字串（批次十二的 Σ_n 真值表／閉集列印用）。
pub fn b_sh_bools(a : Array[Bool]) -> String {
  let mut s = "{"
  for i in 0..<a.length() {
    if i > 0 {
      s = s + ", "
    }
    s = s + (if a[i] { "1" } else { "0" })
  }
  s + "}"
}
