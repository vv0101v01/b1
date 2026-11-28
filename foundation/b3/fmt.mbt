///|
/// fmt.mbt — 報告列印的共用格式（批次三至十一共用的單一定義）。
///
/// 原本 `fmt_b` 定義在 report3.mbt，卻被 report4–report8 直接呼叫；
/// 拆成獨立套件後該依賴會變成「報告 → 報告」的交叉引用，故獨立成模組。

///|
/// 一行 [PASS] / [FAIL] 報告列。
pub fn fmt_b(name : String, ok : Bool) -> String {
  "  [" + (if ok { "PASS" } else { "FAIL" }) + "] " + name + "\n"
}
