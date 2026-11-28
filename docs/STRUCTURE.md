# 專案結構（目錄歸類說明）

本專案原先在倉庫根目錄平鋪約 127 個 `.mbt` 檔與 20 餘份文件。現在依「角色」分成
套件（MoonBit package），每層都有 `moon.pkg` 宣告依賴，根目錄只留入口與文件。

```
core/            純數學核心（無內部依賴）
  arith.mbt        整數／模算術、質數、sigma、Rat 等
  galois.mbt       有限體、置換群等

common/          跨批次共用小工具（單一實作，避免複製貼上）
  shared.mbt       b_sh_* 字串／陣列輔助

foundation/      算術與表示論地基（批次一至八）
  b1/  整體域→局部域→阿代爾環→伊代爾群→志村簇→旗簇→主叢模疊→希欽→自守形式→自守表示
  b2/  ℓ-進表示、Frobenius、阿廷 L、自守 L、函子性、基變換、模性
  b3/  朗蘭茲 C-群、代數自守表示、動機伽羅瓦群、霍奇–泰特、卡-朔消滅
  b4/  純動機、動機 L-函數、塞爾模性、模性提升
  b5/  弦圖高斯馬可夫、非交換弦圖／完美樹譜序列、解空間不動點
  b6/  導出代數幾何、辛疊、分次哈密頓、超凱勒／鏡像
  b7/  B₄ 四值雙格、快葉射影循環卷積、哈肯–茲萬齊格快慢分離
  b8/  點函子、拉回、餘極限與層化、格羅滕迪克宇宙、莫里塔等價
  b12/ 批次十二：CZFM 不可達層級、哥德爾編碼與可證性、KPM／馬洛／塌縮、列維綱領、朗蘭茲約束

topos/           拓撲斯與高階範疇（批次九至十一）
  b9/  平展拓撲斯、預拓撲、篩／遺址、層化、柄、吉羅定理、分類拓撲斯
  b10/ 勒雷譜序列、高階直像、∞-遺址、拓撲斯基本群
  b11/ 豪斯多夫／緊拓撲斯、六運算、導出範疇、反常層、ℓ-進層、cdh
  b14/ 批次十四：剛性拓撲／可容許覆蓋、譜空間、斯科特拓撲、左正合全子範疇、
       2-單子性、可近／正則範疇、反常 t-結構／IC／Serre 對偶、𝔸¹-同倫／Milnor K₂／下降、
       吉羅／∞-層化／有效群oid／穩定化／點空間（linalg、space、rigid、cat、derived、motivic、infty、models）
  b13/ 批次十三：拓撲格、內在遺址與外化、莫里塔等價、幾何態射、伽羅瓦拓撲斯與基變、
       內部張量積／Hom、扭子（5 檔：grid／geom13／gal13／infty13／inner）
  b15/ 批次十五（補洞）：對批次十三／十四的 13 個缺口以歸納法＋反證法補完——
       小生成集／預層有效／Čech 度 2／真反常截斷／IC 的 3^b／K^M_n／K₀ 表現／π₂／
       纖維拓撲斯＋內部邏輯／群值高階下降／映射錐與 LES／CP³ 與 twistor／擬分離
       （4 檔：g14a／g14b／g13／g13b，只依賴 topos/b14）

axioms/          全域公理與自洽性審計（批次十二的 GA-1／GA-2／GA-3）
  axioms.mbt     LCT／Mahlo／LC 公理清單、有限模型檢核、三完備與哥德爾殘餘標記

reports/         十五批可執行報告（`render_report*`）與白盒測試（`*_wbtest.mbt`）
cmd/main/        可執行入口：依序印出批次一至十五的完整報告
tools/           維護腳本（見下）
docs/
  theorems/      各批定理全集 THEOREMS*.md（批次十三見 THEOREMS13.md、批次十四見 THEOREMS14.md、批次十五見 THEOREMS15.md）
  reports/       各批報告的歷史輸出快照 REPORT*_output.txt
```

## 套件依賴方向（無環）

```
core → common → foundation/b1 … b8 → topos/b9 → b10 → b11 → b13 → b14 → b15 → axioms → reports → cmd/main
        └ foundation/b12 ─────────────────────────────────┘
```

`reports` 依賴所有前置套件，`cmd/main` 只依賴 `reports`；反向依賴一律禁止
（早期版本的「報告測試放在模組套件裡」就會造成 b9→reports→b9 的循環，已移除）。

## `zz_deps.mbt` 是什麼

MoonBit 的跨套件名稱只能透過檔案頂端的 `using @alias { … }` 匯入，而**同一套件
的多個檔案各自寫 `using` 會觸發 `[4051] declared twice`**。因此每個套件都有一個
集中放別名的檔案 `zz_deps.mbt`，內容由 `cmd/tools`（MoonBit 程式，見下）以靜態分析維護。

## 維護腳本

**全倉零 Python**：原本的兩支腳本（`tools/regen_deps.py`、`tools/qualify_test_uses.py`）
已改寫成 MoonBit 可執行程式 `cmd/tools`。關鍵差別是它們不再呼叫 `moon check` 並解析
其人類可讀的診斷文字，而是**自己做詞法分析**（`scan.mbt`，處理註解／字串／插值／
test 區塊）——因此不需要 subprocess，也不需要外部程式。

```bash
moon run cmd/tools --target native -- deps      # 維護 zz_deps.mbt 與 moon.pkg
moon run cmd/tools --target native -- deps --check
moon run cmd/tools --target native -- qualify   # 只在 test 中使用的名稱 → @alias.name
moon run cmd/tools --target native -- qualify --check
moon run cmd/tools --target native -- audit     # 死碼清單（減債用）
moon run cmd/tools --target native -- dups      # 逐字重複的函式體（去重用）
moon run cmd/tools --target native -- stats     # 行數／宣告數
moon run cmd/tools --target native -- why topos/b14   # 為何要 import 某套件
```

`deps` 的兩條設計約束：
1. **層級即契約**：`pkg_rank()` 明列 core → common → b1 … b8 → b9 … b15 → b12 → axioms
   → reports → cmd/main；只允許由高 rank 指向低 rank，因此 import 圖**不可能有環**。
2. **語義比較**：`--check` 比較的是「alias＋名稱」的集合與「路徑＋別名」的集合，
   不是文字，所以 `moon fmt` 要怎麼斷行都不會造成假漂移。

注意：MoonBit 的 unused-import 分析不計 `test` 區塊內的引用，所以「只在測試裡用到」
的跨套件名稱若留在 `using` 會永遠被回報 `unused_value`；正確做法是測試內寫
`@alias.name`，這也是 `cmd/tools qualify` 做的事。
