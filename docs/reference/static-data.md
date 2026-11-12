# 静态数据

已有可核对的对象、字段或参数值时，可以用 `--facts file.json` 交给 Scanner。Scanner 按本次字节码核对类型，保留输入的来源。未提供的值按未知处理。

```json
{
  "source": "输入来源与核验说明",
  "basis": "BINDING",
  "entry": {
    "owner": "example.Service",
    "name": "inspect",
    "descriptor": "(Ljava/lang/Object;)V",
    "receiver": {"ref": "service"},
    "arguments": [{"ref": "value"}]
  },
  "objects": [
    {"id": "service", "type": "example.Service"},
    {"id": "value", "type": "example.Value"}
  ]
}
```

`entry` 须符合当前模式和入口筛选。实例方法填写 `receiver`，静态方法省略。类名可用点分包名或 JVM 内部名，方法与字段的 `descriptor` 用 JVM 格式。

| `basis` | 用法 |
| --- | --- |
| `BINDING` | 将经字节码核对的输入作为已知事实 |
| `ASSUMPTION` | 按给定关系分析，并把假设留在结果中 |
| `REFERENCE` | 记录资料来源，供阅读结果时参考 |

## 对象和值

每个对象有唯一的 `id` 和具体的运行时 `type`。引用写成 `{"ref":"id"}`，Class 字面值写成 `{"class":"Ljava/lang/String;"}`。其他值使用 JSON 字符串、数字、布尔值或 null。Scanner 按字段、数组元素或参数的 JVM 类型校验数值范围。

| 属性 | 写法 |
| --- | --- |
| `fields` | 实例字段列表，每项包含 `owner`、`name`、`descriptor` 和 `value`，可填写继承字段 |
| `elements` | 数组或集合的值列表，顺序按对象类型和已知条件处理 |
| `entries` | 映射条目列表，每项填写 `key` 和 `value` |
| `classfile` | 用文件内容填写 `[B` 对象。可用绝对路径或相对于清单所在目录的路径。与 `fields`、`elements`、`entries` 和 `decoded` 互斥 |
| `decoded` | 记录已知的外部解码结果，源数据与当前对象状态分别处理 |
| `absentFields` | 记录已知缺失的源字段，每项包含 `owner`、`name` 和 `descriptor` |
| `classData` | 记录源对象某个类的数据槽，每项包含 `owner` 和布尔值 `present` |

`absentFields` 和 `classData` 用于 `decoded` 可达的源对象。已填写的字段及其声明类按存在处理。对象自身的类数据槽也要保留。集合或映射的迭代顺序取决于类型与已知状态。

JSON 和附件合计最多 1 MiB，最多 256 个对象、2048 次赋值。`elements` 和 `arguments` 每个序列最多 256 项。无效引用和类型会报告具体位置。[输入要求模板](evidence.md#扫描报告)
