# 结果与集成

## 扫描报告

Scanner 从同一次扫描写出三份文件。打开 `report.md` 可以阅读发现和依据，`report.json` 保存完整的机器证据，`input-requirements.json` 列出仍需补充的输入。取得可核对的值后，按[静态数据格式](static-data.md)另写清单。

JSON 的 `schemaVersion` 为 `4`。`execution` 表示分析完成或截断，`outcome` 表示本次是否有发现。截断时，CLI 和终端界面会显示首条原因，完整列表见报告的 `limitations`。阅读候选时，同时查看缺失类、分析限制和需要补充的条件。

`findings` 保留发现与所选依据，`relations` 记录调用和数据关系，`demandFrontier` 与 `breakpoints` 指向仍待核对的位置。同一关系可以有多组依据（`supports`），每一组都需要 `dependencies` 列出的关系。`proof` 记录发现使用的关系和支持编号。

位置、值和条件等共用 `references` 表，下标只在所属报告有效。指令编号按含标签和调试节点的 ASM 视图计数，可附源码行。非有限浮点值用带类型的 JSON 对象表示，例如 `{"type":"Double","value":"NaN"}`。

`statistics.elapsedMillis` 记录分析耗时。进程总耗时还包含 JVM 启动、输入装配和报告写入。

## 工具查询

Bridge 可以查询声明、实际指令、调用图、方法分派和数据来源，也能发起完整扫描。核对已有关系时，连接检查会指出所选依据是否齐全、还缺什么，或哪些条件相互冲突。输入是否可得、部署前提是否成立，按各自的证据判断。

`scanner_lookup_knowledge` 可以按知识 ID 查看参考关系；部分关系附有样本、依赖版本和公开来源。扫描选择 `knowledge: none` 时不使用参考知识，仍按当前字节码排序。这些引导不代替当前输入的调用和条件。

结果默认返回摘要、小页和 `resultRef`。用 `scanner_read_result` 沿引用读取详情，`path` 由 JSON 键和数组下标组成。数组和字符串页把返回的 `next` 用作下一页的 `offset`，`-1` 表示到尾。字符串偏移按 UTF-16 单元计。关系、发现和输入要求也可以按 ID 取页，缺失项和暂未读取的项分别返回。

`scanRef` 接受 `scanner_scan_target` 返回的结果引用，供局部查询复用该次扫描的程序事实。引用、关系编号与支持编号只在所属输入和结果内有效。结果可主动释放，宿主关闭后临时引用失效。需要跨会话保留的依据可记录到[审计黑板](audit.md#黑板与恢复)。

## 嵌入

直接调用 `createScannerTools({ input, jdk })` 时，调用方在结束后使用返回对象的 `close()`。在 Pi 中加载 `scannerExtension(options)` 时，扩展随会话关闭宿主。两种入口均可用 `scannerJar` 和 `bridgeJar` 指定同次构建的配套 JAR。

Bridge 通过 UTF-8 JSON Lines 串行处理请求，提供进度与取消。参数错误随请求返回，协议错误会关闭宿主。参数范围和扫描默认值可从工具定义查询。[架构](../architecture.md)
